/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.HaagerupZsido.Basic
public import TauCeti.Analysis.SpecialFunctions.Integrals.AbsSinExp

/-!
# The exact `L¹` mass of the Haagerup–Zsidó kernel

The Haagerup–Zsidó kernel `k(t) = -i r(t)`, `r(t) = (sin t / 2) L(t)`, is a superposition over
`y > 0` of the damped oscillations `(sin t / 2) w(y) e^{-|t| y}`, where `w(y) = tanh (π y / 2)` and
`L` is the Laplace transform of `w`. This file shows that the superposition is absolutely
integrable on `(0, ∞) × ℝ`, so that integrals against the kernel may be computed by Fubini, and
computes the mass of the kernel exactly:

`∫_ℝ ‖k(t)‖ dt = ∫_ℝ |r(t)| dt = π / 2`.

By Tonelli, the mass is `∫_{y > 0} (w(y) / 2) ∫_ℝ |sin t| e^{-y |t|} dt dy`. The Laplace transform
of `|sin|` is `2 (1 + e^{-π y}) / ((1 - e^{-π y}) (1 + y²))`, and the weight
`w(y) = (1 - e^{-π y}) / (1 + e^{-π y})` is exactly the factor that cancels the periodic part,
leaving `∫_{y > 0} (1 + y²)⁻¹ dy = π / 2`. This value is the sharp constant `π / 2` in the norm
bound for the Sylvester equation `AX - XB = C` with pairwise separated spectra.

## Main results

* `TauCeti.HaagerupZsido.integrable_kernelIntegrand`: the integrand
  `(y, t) ↦ (sin t / 2) w(y) e^{-|t| y}` is integrable on `(0, ∞) × ℝ`;
* `TauCeti.HaagerupZsido.integral_abs_realKernel`: `∫_ℝ |r(t)| dt = π / 2`;
* `TauCeti.HaagerupZsido.integral_norm_reciprocalKernel`: `∫_ℝ ‖k(t)‖ dt = π / 2`.

## References

* U. Haagerup, L. Zsidó, the extremal kernel attaining the constant `π / 2`; see the account in
  S. Albeverio, K. A. Makarov, A. K. Motovilov, *Graph subspaces and the spectral shift function*,
  Canad. J. Math. **55** (2003), 449–503.
-/

public section

open MeasureTheory Set
open scoped Real

namespace TauCeti.HaagerupZsido

/-- The integrand `(y, t) ↦ (sin t / 2) w(y) e^{-|t| y}` whose integral over `y > 0` is the real
kernel `r(t)`. -/
noncomputable def kernelIntegrand (p : ℝ × ℝ) : ℝ :=
  Real.sin p.2 / 2 * (weight p.1 * Real.exp (-(|p.2| * p.1)))

theorem kernelIntegrand_def (p : ℝ × ℝ) :
    kernelIntegrand p = Real.sin p.2 / 2 * (weight p.1 * Real.exp (-(|p.2| * p.1))) := (rfl)

@[fun_prop]
theorem continuous_kernelIntegrand : Continuous kernelIntegrand := by
  unfold kernelIntegrand
  fun_prop

/-- The real kernel is the integral of `kernelIntegrand` over `y > 0`. -/
theorem integral_kernelIntegrand (t : ℝ) :
    ∫ y in Ioi (0 : ℝ), kernelIntegrand (y, t) = realKernel t := by
  simp only [kernelIntegrand_def, realKernel_def, weightLaplaceTransform_def, integral_const_mul]

/-- The weight satisfies `w(y) (1 + e^{-π y}) = 1 - e^{-π y}`, that is,
`w(y) = (1 - e^{-π y}) / (1 + e^{-π y})`. -/
private theorem weight_mul_one_add_exp (y : ℝ) :
    weight y * (1 + Real.exp (-(π * y))) = 1 - Real.exp (-(π * y)) := by
  have hpos : 0 < Real.exp (π * y / 2) + Real.exp (-(π * y / 2)) := by positivity
  have hsq : Real.exp (-(π * y)) = Real.exp (-(π * y / 2)) * Real.exp (-(π * y / 2)) := by
    rw [← Real.exp_add]
    ring_nf
  have hone : Real.exp (π * y / 2) * Real.exp (-(π * y / 2)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [weight_def, Real.tanh_eq, hsq, div_mul_eq_mul_div, div_eq_iff hpos.ne']
  linear_combination 2 * Real.exp (-(π * y / 2)) * hone

/-- For `y ≥ 0`, `|kernelIntegrand (y, t)| = (w(y) / 2) |sin t| e^{-y |t|}`. -/
private theorem abs_kernelIntegrand {y : ℝ} (hy : 0 ≤ y) (t : ℝ) :
    |kernelIntegrand (y, t)| = weight y / 2 * (|Real.sin t| * Real.exp (-(y * |t|))) := by
  rw [kernelIntegrand_def, abs_mul, abs_div, abs_two, abs_mul, abs_of_nonneg (weight_nonneg hy),
    Real.abs_exp, mul_comm |t| y]
  ring

/-- For `y > 0`, the `t`-integral of `|kernelIntegrand (y, t)|` is `(1 + y²)⁻¹`: the weight
cancels the periodic factor of the Laplace transform of `|sin|`. -/
private theorem integral_abs_kernelIntegrand {y : ℝ} (hy : 0 < y) :
    ∫ t, |kernelIntegrand (y, t)| = (1 + y ^ 2)⁻¹ := by
  have hlt : Real.exp (-(π * y)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hne : 1 - Real.exp (-(π * y)) ≠ 0 := (sub_pos.mpr hlt).ne'
  simp only [abs_kernelIntegrand hy.le, integral_const_mul, integral_abs_sin_mul_exp_neg_mul_abs hy]
  have h := weight_mul_one_add_exp y
  field_simp
  linear_combination h

/-- **The product integrability certificate.** The integrand
`(y, t) ↦ (sin t / 2) w(y) e^{-|t| y}` is integrable on `(0, ∞) × ℝ`. Integrals against the
kernel can therefore be computed by exchanging the order of integration. -/
theorem integrable_kernelIntegrand :
    Integrable kernelIntegrand ((volume.restrict (Ioi 0)).prod volume) := by
  refine (integrable_prod_iff continuous_kernelIntegrand.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy ↦ ?_)
    refine ((integrable_abs_sin_mul_exp_neg_mul_abs hy).const_mul (weight y / 2)).mono'
      (by fun_prop) (Filter.Eventually.of_forall fun t ↦ ?_)
    rw [Real.norm_eq_abs, abs_kernelIntegrand (le_of_lt hy)]
  · simp only [Real.norm_eq_abs]
    refine integrable_inv_one_add_sq.integrableOn.congr_fun (fun y hy ↦ ?_) measurableSet_Ioi
    exact (integral_abs_kernelIntegrand hy).symm

/-- **The exact mass of the real kernel.** `∫_ℝ |r(t)| dt = π / 2`. -/
theorem integral_abs_realKernel : ∫ t, |realKernel t| = π / 2 := by
  -- `|r(t)| = ∫_{y > 0} |kernelIntegrand (y, t)| dy`, since `sin t / 2` is constant in `y` and
  -- the rest of the integrand is nonnegative.
  have hrep : ∀ t, |realKernel t| = ∫ y in Ioi (0 : ℝ), |kernelIntegrand (y, t)| := fun t ↦ by
    rw [realKernel_def, abs_mul, abs_of_nonneg (weightLaplaceTransform_nonneg t),
      weightLaplaceTransform_def, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
    rw [kernelIntegrand_def, abs_mul (Real.sin t / 2),
      abs_of_nonneg (mul_nonneg (weight_nonneg (le_of_lt hy)) (Real.exp_pos _).le)]
  simp only [hrep]
  have hπ : ∫ y in Ioi (0 : ℝ), (1 + y ^ 2)⁻¹ = π / 2 := by
    rw [integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero]
  rw [← integral_integral_swap (f := fun y t ↦ |kernelIntegrand (y, t)|)
    integrable_kernelIntegrand.abs, ← hπ]
  exact setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ integral_abs_kernelIntegrand hy

/-- **The exact mass of the Haagerup–Zsidó kernel.** `∫_ℝ ‖k(t)‖ dt = π / 2`. -/
theorem integral_norm_reciprocalKernel : ∫ t, ‖reciprocalKernel t‖ = π / 2 := by
  simp only [norm_reciprocalKernel, integral_abs_realKernel]

end TauCeti.HaagerupZsido
