/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import TauCeti.Analysis.Fourier.HaagerupZsido.Basic
import TauCeti.Analysis.Fourier.ExpNegAbs
import TauCeti.Analysis.Fourier.HaagerupZsido.Mass
import TauCeti.Analysis.Fourier.HaagerupZsido.OddPole

/-!
# The Fourier integral of the Haagerup–Zsidó kernel

The Haagerup–Zsidó kernel `k(t) = -i r(t)`, `r(t) = (sin t / 2) L(t)`, inverts the variable on the
exterior of the unit interval:

`∫_ℝ e^{itx} k(t) dt = 1 / x`   for `|x| ≥ 1`.

Together with the exact mass `∫ ‖k‖ = π / 2`, this is the property that makes the kernel useful:
for self-adjoint `A`, `B` whose spectra are separated pairwise by at least `1`, integrating
`e^{itA} C e^{-itB}` against `k` solves the Sylvester equation `AX - XB = C`, and the mass bounds
the solution by `(π / 2) ‖C‖`.

For `x ≥ 1` the identity is computed by Fubini, using the absolute integrability of the
superposition `r(t) = ∫_{y > 0} (sin t / 2) w(y) e^{-|t| y} dy`
(`TauCeti.HaagerupZsido.integrable_kernelIntegrand`). Writing `sin t` through `e^{±it}`, the inner
integral in `t` is a difference of two Lorentzians
(`TauCeti.integral_exp_mul_I_mul_exp_neg_mul_abs`) centred at `x ∓ 1`, which differ by `2`. The
rotation by `-i` in `k` makes the result real, and the remaining `y`-integral of `w(y)` against
the two Lorentzians is `TauCeti.HaagerupZsido.integral_weight_mul_mul_inv_sub_inv`. The case
`x ≤ -1` follows by oddness of the kernel.

## Main results

* `TauCeti.HaagerupZsido.integral_exp_mul_I_mul_reciprocalKernel`: `∫ e^{itx} k(t) dt = 1 / x` for
  `|x| ≥ 1`;
* `TauCeti.HaagerupZsido.fourier_reciprocalKernel`: the same identity in Mathlib's normalisation of
  the Fourier transform, `𝓕 k ξ = -1 / (2 π ξ)` for `2 π |ξ| ≥ 1`.

## References

* U. Haagerup, L. Zsidó, the extremal kernel attaining the constant `π / 2`; see the account in
  S. Albeverio, K. A. Makarov, A. K. Motovilov, *Graph subspaces and the spectral shift function*,
  Canad. J. Math. **55** (2003), 449–503.
* R. Bhatia, C. Davis, A. McIntosh, *Perturbation of spectral subspaces and solution of linear
  operator equations*, Linear Algebra Appl. **52/53** (1983), 45–67.
-/

public section

open MeasureTheory Set
open scoped FourierTransform Real

namespace TauCeti.HaagerupZsido

/-- For `y > 0`, the Fourier integral in `t` of the damped oscillation
`(sin t / 2) w(y) e^{-|t| y}` is `i (w(y) y / 2) ((y² + (x - 1)²)⁻¹ - (y² + (x + 1)²)⁻¹)`. -/
private theorem integral_exp_mul_I_mul_kernelIntegrand {y : ℝ} (hy : 0 < y) (x : ℝ) :
    ∫ t : ℝ, Complex.exp ((x : ℂ) * t * Complex.I) * (kernelIntegrand (y, t) : ℂ) =
      Complex.I *
        ((weight y * y / 2 * ((y ^ 2 + (x - 1) ^ 2)⁻¹ - (y ^ 2 + (x + 1) ^ 2)⁻¹) : ℝ) : ℂ) := by
  set e : ℝ → ℂ := fun t ↦ (Real.exp (-(y * |t|)) : ℂ)
  -- Write `sin t` through `e^{±it}`: the integrand is a difference of two damped oscillations.
  have hpt (t : ℝ) : Complex.exp ((x : ℂ) * t * Complex.I) * (kernelIntegrand (y, t) : ℂ) =
      (weight y / 4 : ℝ) * Complex.I * (Complex.exp (((x - 1 : ℝ) : ℂ) * t * Complex.I) * e t -
        Complex.exp (((x + 1 : ℝ) : ℂ) * t * Complex.I) * e t) := by
    have hm : Complex.exp (((x - 1 : ℝ) : ℂ) * t * Complex.I) =
        Complex.exp ((x : ℂ) * t * Complex.I) * Complex.exp (-(t : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      push_cast
      ring_nf
    have hp : Complex.exp (((x + 1 : ℝ) : ℂ) * t * Complex.I) =
        Complex.exp ((x : ℂ) * t * Complex.I) * Complex.exp ((t : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      push_cast
      ring_nf
    have hsin := Complex.two_sin (t : ℂ)
    rw [hm, hp, kernelIntegrand_def, mul_comm |t| y]
    simp only [e]
    push_cast
    linear_combination (Complex.exp ((x : ℂ) * t * Complex.I) * (weight y : ℂ) / 4 *
      Complex.exp (-((y : ℂ) * (|t| : ℝ)))) * hsin
  have hint (b : ℝ) : Integrable fun t : ℝ ↦ Complex.exp ((b : ℂ) * t * Complex.I) * e t :=
    ((integrable_exp_neg_mul_abs hy).ofReal).bdd_mul (c := 1) (by fun_prop)
      (.of_forall fun t ↦ by simp [Complex.norm_exp])
  simp only [hpt]
  rw [integral_const_mul, integral_sub (hint _) (hint _), integral_exp_mul_I_mul_exp_neg_mul_abs hy,
    integral_exp_mul_I_mul_exp_neg_mul_abs hy]
  have h₁ : 0 < y ^ 2 + (x - 1) ^ 2 := by positivity
  have h₂ : 0 < y ^ 2 + (x + 1) ^ 2 := by positivity
  push_cast
  field_simp
  ring

/-- The Fourier integral of the kernel on the half-line `x ≥ 1`. -/
private theorem integral_exp_mul_I_mul_reciprocalKernel_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    ∫ t : ℝ, Complex.exp ((x : ℂ) * t * Complex.I) * reciprocalKernel t = (x : ℂ)⁻¹ := by
  set f : ℝ → ℝ → ℂ := fun y t ↦
    Complex.exp ((x : ℂ) * t * Complex.I) * (kernelIntegrand (y, t) : ℂ)
  have hf : Integrable (Function.uncurry f) ((volume.restrict (Ioi 0)).prod volume) :=
    integrable_kernelIntegrand.ofReal.bdd_mul (c := 1) (by fun_prop)
      (.of_forall fun p ↦ by simp [Complex.norm_exp])
  -- Expand the kernel as its `y`-integral and exchange the order of integration.
  have hk (t : ℝ) : Complex.exp ((x : ℂ) * t * Complex.I) * reciprocalKernel t =
      -Complex.I * ∫ y in Ioi (0 : ℝ), f y t := by
    simp only [f, reciprocalKernel_def, ← integral_kernelIntegrand t, integral_const_mul,
      ← integral_complex_ofReal]
    ring
  have ha : 0 ≤ x - 1 := sub_nonneg.mpr hx
  have hy : ∫ y in Ioi (0 : ℝ), ∫ t, f y t = Complex.I *
      ((∫ y in Ioi (0 : ℝ), weight y * y / 2 *
        ((y ^ 2 + (x - 1) ^ 2)⁻¹ - (y ^ 2 + (x - 1 + 2) ^ 2)⁻¹) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
    simp only [f, integral_exp_mul_I_mul_kernelIntegrand hy]
    ring_nf
  have hval : ∫ y in Ioi (0 : ℝ), weight y * y / 2 *
      ((y ^ 2 + (x - 1) ^ 2)⁻¹ - (y ^ 2 + (x - 1 + 2) ^ 2)⁻¹) = x⁻¹ := by
    have hx0 : x ≠ 0 := by positivity
    calc _ = (∫ y in Ioi (0 : ℝ), weight y * y *
          ((y ^ 2 + (x - 1) ^ 2)⁻¹ - (y ^ 2 + (x - 1 + 2) ^ 2)⁻¹)) / 2 := by
          rw [← integral_div]
          exact integral_congr_ae (.of_forall fun y ↦ by ring)
      _ = x⁻¹ := by
          rw [integral_weight_mul_mul_inv_sub_inv ha]
          field_simp
          ring
  simp only [hk]
  rw [integral_const_mul, ← integral_integral_swap hf, hy, hval]
  push_cast
  linear_combination (-(x : ℂ)⁻¹) * Complex.I_mul_I

/-- **The exterior reciprocal Fourier identity.** For `|x| ≥ 1`, the Fourier integral of the
Haagerup–Zsidó kernel is `∫ e^{itx} k(t) dt = 1 / x`. -/
theorem integral_exp_mul_I_mul_reciprocalKernel {x : ℝ} (hx : 1 ≤ |x|) :
    ∫ t : ℝ, Complex.exp ((x : ℂ) * t * Complex.I) * reciprocalKernel t = (x : ℂ)⁻¹ := by
  rcases le_abs'.mp hx with hx | hx
  · -- For `x ≤ -1`, reflect `t ↦ -t` and use that the kernel is odd.
    have h := integral_exp_mul_I_mul_reciprocalKernel_of_one_le (le_neg.mpr hx)
    rw [← integral_neg_eq_self]
    calc _ = -∫ t : ℝ, Complex.exp (((-x : ℝ) : ℂ) * t * Complex.I) * reciprocalKernel t := by
          rw [← integral_neg]
          refine integral_congr_ae (.of_forall fun t ↦ ?_)
          simp [reciprocalKernel_neg]
      _ = (x : ℂ)⁻¹ := by rw [h]; push_cast; ring
  · exact integral_exp_mul_I_mul_reciprocalKernel_of_one_le hx

/-- **The exterior reciprocal identity in Mathlib's Fourier normalisation.** With
`𝓕 f ξ = ∫ e^{-2πitξ} f(t) dt`, the Haagerup–Zsidó kernel satisfies `𝓕 k ξ = -1 / (2 π ξ)` whenever
`2 π |ξ| ≥ 1`. -/
theorem fourier_reciprocalKernel {ξ : ℝ} (hξ : 1 ≤ 2 * π * |ξ|) :
    𝓕 reciprocalKernel ξ = -((2 * π * ξ : ℝ) : ℂ)⁻¹ := by
  have hx : 1 ≤ |-(2 * π * ξ)| := by
    rwa [abs_neg, abs_mul, abs_of_pos Real.two_pi_pos]
  rw [Real.fourier_eq', neg_inv, ← Complex.ofReal_neg,
    ← integral_exp_mul_I_mul_reciprocalKernel hx]
  refine integral_congr_ae (.of_forall fun t ↦ ?_)
  simp only [smul_eq_mul]
  congr 2
  push_cast [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  ring

end TauCeti.HaagerupZsido
