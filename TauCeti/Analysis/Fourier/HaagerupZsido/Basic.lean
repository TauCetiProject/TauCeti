/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod
public import TauCeti.Analysis.SpecialFunctions.Artanh
public import TauCeti.MeasureTheory.Integral.ExpDecay

/-!
# The Haagerup–Zsidó kernel

The Haagerup–Zsidó kernel is an integrable function `k : ℝ → ℂ` whose Fourier integral
`∫ k(t) e^{itx} dt` equals `1 / x` for every `|x| ≥ 1`, and whose `L¹` norm is exactly `π / 2`.
Integrating a bounded operator-valued function against it is what gives the sharp constant `π / 2`
in the norm bound for the solution of the Sylvester equation `AX - XB = C` when the spectra of the
self-adjoint operators `A` and `B` are separated pairwise, and hence in the corresponding
Davis–Kahan `sin Θ` theorem. Those two identities are not proved in this file, which sets up the
kernel and its elementary properties.

The kernel is built in four steps from the hyperbolic weight `w(y) = tanh (π y / 2)`:

* `TauCeti.HaagerupZsido.weight`: the weight `w(y) = tanh (π y / 2)`;
* `TauCeti.HaagerupZsido.weightLaplaceTransform`: its Laplace transform at `|t|`,
  `L(t) = ∫_{y > 0} w(y) e^{-|t| y} dy`;
* `TauCeti.HaagerupZsido.realKernel`: the real kernel `r(t) = (sin t / 2) L(t)`;
* `TauCeti.HaagerupZsido.reciprocalKernel`: the kernel `k(t) = -i r(t)`.

This file proves the elementary properties of these objects: the weight is continuous, odd,
nonnegative on `[0, ∞)` and bounded there by `min 1 (π y / 2)`; the Laplace transform is a
genuine (absolutely convergent) integral for `t ≠ 0`, is even, nonnegative, measurable, and
satisfies `L(t) ≤ 1 / |t|` and `L(t) ≤ π / (2 t²)`; the two kernels are measurable and odd, with
`‖k(t)‖ = |r(t)|`. The two bounds on `L` give `|r(t)| ≤ π / (2 (1 + t²))`
(`TauCeti.HaagerupZsido.abs_realKernel_le`): near the origin `|sin t| ≤ |t|` cancels the
`1 / |t|` growth of `L`, and at infinity `L` decays like `1 / t²` because `w(y) ≤ π y / 2`
near `y = 0`. Hence both kernels are integrable on `ℝ`.

## References

* U. Haagerup, L. Zsidó, the extremal kernel attaining the constant `π / 2`; see the account in
  S. Albeverio, K. A. Makarov, A. K. Motovilov, *Graph subspaces and the spectral shift function*,
  Canad. J. Math. **55** (2003), 449–503.
* R. Bhatia, C. Davis, A. McIntosh, *Perturbation of spectral subspaces and solution of linear
  operator equations*, Linear Algebra Appl. **52/53** (1983), 45–67.
-/

public section

open MeasureTheory Set
open scoped Real

namespace TauCeti.HaagerupZsido

/-! ### The hyperbolic weight -/

/-- The hyperbolic weight `w(y) = tanh (π y / 2)` of the Haagerup–Zsidó construction. -/
noncomputable def weight (y : ℝ) : ℝ :=
  Real.tanh (π * y / 2)

theorem weight_def (y : ℝ) : weight y = Real.tanh (π * y / 2) := (rfl)

@[simp]
theorem weight_zero : weight 0 = 0 := by
  simp [weight_def]

/-- The weight is odd. -/
@[simp]
theorem weight_neg (y : ℝ) : weight (-y) = -weight y := by
  rw [weight_def, weight_def, ← Real.tanh_neg]
  ring_nf

/-- The weight is nonnegative on `[0, ∞)`. -/
theorem weight_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ weight y :=
  Real.tanh_nonneg (by positivity)

/-- The weight is less than `1`. -/
theorem weight_lt_one (y : ℝ) : weight y < 1 :=
  Real.tanh_lt_one _

/-- On `[0, ∞)` the weight lies below its tangent line `π y / 2` at the origin. -/
theorem weight_le_pi_mul_div_two {y : ℝ} (hy : 0 ≤ y) : weight y ≤ π * y / 2 :=
  Real.tanh_le_self (by positivity)

/-- The weight is continuous. -/
@[fun_prop]
theorem continuous_weight : Continuous weight := by
  unfold weight
  fun_prop

@[fun_prop]
theorem measurable_weight : Measurable weight :=
  continuous_weight.measurable

/-! ### The Laplace transform of the weight -/

/-- The Laplace transform of the weight at `|t|`,
`L(t) = ∫_{y > 0} tanh (π y / 2) e^{-|t| y} dy`. The integral converges absolutely for `t ≠ 0`
(`integrableOn_weight_mul_exp`); at `t = 0` it diverges and the Bochner integral is `0`. -/
noncomputable def weightLaplaceTransform (t : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), weight y * Real.exp (-(|t| * y))

theorem weightLaplaceTransform_def (t : ℝ) :
    weightLaplaceTransform t = ∫ y in Ioi (0 : ℝ), weight y * Real.exp (-(|t| * y)) := (rfl)

/-- For `t ≠ 0` the integrand of the Laplace transform is integrable on `(0, ∞)`: it is
dominated by `e^{-|t| y}`. -/
theorem integrableOn_weight_mul_exp {t : ℝ} (ht : t ≠ 0) :
    IntegrableOn (fun y ↦ weight y * Real.exp (-(|t| * y))) (Ioi 0) := by
  have hexp : IntegrableOn (fun y : ℝ ↦ Real.exp (-(|t| * y))) (Ioi 0) := by
    simpa using integrableOn_pow_mul_exp_neg_mul_Ioi 0 (abs_pos.mpr ht)
  refine hexp.mono' (by fun_prop) (ae_restrict_of_forall_mem measurableSet_Ioi fun y hy ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
  have h0 := weight_nonneg (le_of_lt (mem_Ioi.mp hy))
  rw [abs_of_nonneg h0]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (weight_lt_one y).le

/-- The Laplace transform of the weight is nonnegative. -/
theorem weightLaplaceTransform_nonneg (t : ℝ) : 0 ≤ weightLaplaceTransform t :=
  setIntegral_nonneg measurableSet_Ioi fun _ hy ↦
    mul_nonneg (weight_nonneg (le_of_lt hy)) (Real.exp_pos _).le

/-- The Laplace transform of the weight is even. -/
@[simp]
theorem weightLaplaceTransform_neg (t : ℝ) :
    weightLaplaceTransform (-t) = weightLaplaceTransform t := by
  simp only [weightLaplaceTransform_def, abs_neg]

/-- The Laplace transform of the weight is measurable. -/
@[fun_prop]
theorem measurable_weightLaplaceTransform : Measurable weightLaplaceTransform := by
  have hf : StronglyMeasurable fun p : ℝ × ℝ ↦ weight p.2 * Real.exp (-(|p.1| * p.2)) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ ↦ weight p.2 * Real.exp (-(|p.1| * p.2)))
      |>.stronglyMeasurable
  exact hf.integral_prod_right' (ν := volume.restrict (Ioi 0)) |>.measurable

/-- Since the weight is less than `1`, `L(t) ≤ ∫_{y > 0} e^{-|t| y} dy = 1 / |t|`. -/
theorem weightLaplaceTransform_le_inv_abs {t : ℝ} (ht : t ≠ 0) :
    weightLaplaceTransform t ≤ |t|⁻¹ := by
  have ht' : 0 < |t| := abs_pos.mpr ht
  have hexp := integral_pow_mul_exp_neg_mul_Ioi 0 ht'
  simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one,
    one_div] at hexp
  rw [← hexp, weightLaplaceTransform_def]
  refine setIntegral_mono_on (integrableOn_weight_mul_exp ht)
    (by simpa using integrableOn_pow_mul_exp_neg_mul_Ioi 0 ht') measurableSet_Ioi fun y _ ↦ ?_
  exact mul_le_of_le_one_left (Real.exp_pos _).le (weight_lt_one y).le

/-- Since the weight lies below `π y / 2`,
`L(t) ≤ (π / 2) ∫_{y > 0} y e^{-|t| y} dy = π / (2 t²)`. -/
theorem weightLaplaceTransform_le_pi_div_two_mul_sq {t : ℝ} (ht : t ≠ 0) :
    weightLaplaceTransform t ≤ π / (2 * t ^ 2) := by
  have ht' : 0 < |t| := abs_pos.mpr ht
  have hint := integrableOn_pow_mul_exp_neg_mul_Ioi 1 ht'
  have hval := integral_pow_mul_exp_neg_mul_Ioi 1 ht'
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, Nat.reduceAdd, sq_abs] at hint hval
  calc weightLaplaceTransform t
      ≤ ∫ y in Ioi (0 : ℝ), π / 2 * (y * Real.exp (-(|t| * y))) := by
        rw [weightLaplaceTransform_def]
        refine setIntegral_mono_on (integrableOn_weight_mul_exp ht) (hint.const_mul _)
          measurableSet_Ioi fun y hy ↦ ?_
        exact (mul_le_mul_of_nonneg_right (weight_le_pi_mul_div_two (le_of_lt hy))
          (Real.exp_pos _).le).trans_eq (by ring)
    _ = π / (2 * t ^ 2) := by
        rw [integral_const_mul, hval]
        field_simp

/-! ### The real and reciprocal kernels -/

/-- The real Haagerup–Zsidó kernel `r(t) = (sin t / 2) L(t)`. -/
noncomputable def realKernel (t : ℝ) : ℝ :=
  Real.sin t / 2 * weightLaplaceTransform t

theorem realKernel_def (t : ℝ) : realKernel t = Real.sin t / 2 * weightLaplaceTransform t :=
  (rfl)

/-- The Haagerup–Zsidó kernel `k(t) = -i r(t)`. For `|x| ≥ 1`, the rotation by `-i` turns the
Fourier integral `∫ r(t) e^{itx} dt = i / x` of the odd real kernel into
`∫ k(t) e^{itx} dt = 1 / x`. -/
noncomputable def reciprocalKernel (t : ℝ) : ℂ :=
  -Complex.I * realKernel t

theorem reciprocalKernel_def (t : ℝ) : reciprocalKernel t = -Complex.I * realKernel t := (rfl)

@[fun_prop]
theorem measurable_realKernel : Measurable realKernel := by
  unfold realKernel
  fun_prop

@[fun_prop]
theorem measurable_reciprocalKernel : Measurable reciprocalKernel := by
  unfold reciprocalKernel
  fun_prop

/-- The real kernel is odd. -/
@[simp]
theorem realKernel_neg (t : ℝ) : realKernel (-t) = -realKernel t := by
  simp only [realKernel_def, Real.sin_neg, weightLaplaceTransform_neg]
  ring

/-- The kernel is odd. -/
@[simp]
theorem reciprocalKernel_neg (t : ℝ) : reciprocalKernel (-t) = -reciprocalKernel t := by
  simp only [reciprocalKernel_def, realKernel_neg, Complex.ofReal_neg]
  ring

/-- The kernel has the same modulus as the real kernel. -/
@[simp]
theorem norm_reciprocalKernel (t : ℝ) : ‖reciprocalKernel t‖ = |realKernel t| := by
  simp [reciprocalKernel_def]

/-- **The decay bound for the real kernel.** For every `t`, `|r(t)| ≤ π / (2 (1 + t²))`. For
`|t| ≤ 1` this combines `|sin t| ≤ |t|` with `L(t) ≤ 1 / |t|`; for `|t| ≥ 1` it combines
`|sin t| ≤ 1` with `L(t) ≤ π / (2 t²)`. -/
theorem abs_realKernel_le (t : ℝ) : |realKernel t| ≤ π / (2 * (1 + t ^ 2)) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simpa [realKernel_def] using div_nonneg Real.pi_pos.le zero_le_two
  have hL := weightLaplaceTransform_nonneg t
  have ht' : 0 < |t| := abs_pos.mpr ht
  rw [realKernel_def, abs_mul, abs_of_nonneg hL, abs_div, abs_two]
  rcases le_total |t| 1 with h1 | h1
  · -- Near the origin: `|sin t| * L(t) ≤ |t| * |t|⁻¹ = 1`.
    have hprod : |Real.sin t| * weightLaplaceTransform t ≤ 1 :=
      calc |Real.sin t| * weightLaplaceTransform t ≤ |t| * |t|⁻¹ :=
            mul_le_mul (Real.abs_sin_le_abs) (weightLaplaceTransform_le_inv_abs ht) hL
              ht'.le
        _ = 1 := mul_inv_cancel₀ ht'.ne'
    have hsq : t ^ 2 ≤ 1 := by
      rw [← sq_abs]
      exact pow_le_one₀ ht'.le h1
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [Real.two_le_pi]
  · -- Away from the origin: `|sin t| * L(t) ≤ π / (2 t²)`.
    have hprod : |Real.sin t| * weightLaplaceTransform t ≤ π / (2 * t ^ 2) :=
      calc |Real.sin t| * weightLaplaceTransform t ≤ 1 * (π / (2 * t ^ 2)) :=
            mul_le_mul (Real.abs_sin_le_one t) (weightLaplaceTransform_le_pi_div_two_mul_sq ht)
              hL zero_le_one
        _ = π / (2 * t ^ 2) := one_mul _
    have hsq : 1 ≤ t ^ 2 := by
      rw [← sq_abs]
      exact one_le_pow₀ h1
    have ht2 : 0 < t ^ 2 := by positivity
    calc |Real.sin t| / 2 * weightLaplaceTransform t
        = |Real.sin t| * weightLaplaceTransform t / 2 := by ring
      _ ≤ π / (2 * t ^ 2) / 2 := by gcongr
      _ ≤ π / (2 * (1 + t ^ 2)) := by
        rw [div_div, div_le_div_iff_of_pos_left Real.pi_pos (by positivity) (by positivity)]
        nlinarith

/-- The real kernel is integrable on `ℝ`: it is dominated by `π / (2 (1 + t²))`. -/
theorem integrable_realKernel : Integrable realKernel := by
  refine ((integrable_inv_one_add_sq).const_mul (π / 2)).mono'
    measurable_realKernel.aestronglyMeasurable (Filter.Eventually.of_forall fun t ↦ ?_)
  rw [Real.norm_eq_abs, ← div_eq_mul_inv, div_div]
  exact abs_realKernel_le t

/-- The Haagerup–Zsidó kernel is integrable on `ℝ`. -/
theorem integrable_reciprocalKernel : Integrable reciprocalKernel := by
  refine integrable_realKernel.norm.mono' measurable_reciprocalKernel.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t ↦ ?_)
  rw [norm_reciprocalKernel, Real.norm_eq_abs]

end TauCeti.HaagerupZsido
