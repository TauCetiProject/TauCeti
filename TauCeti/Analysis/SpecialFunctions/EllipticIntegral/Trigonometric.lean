/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Trigonometric form of the AGM integral

For nonzero `a` and `b`, the integral of
`(a² cos² θ + b² sin² θ)^(-1/2)` over a quarter period equals the integral of
`1 / √((x² + a²)(x² + b²))` over the positive half-line. This identifies the
trigonometric complete elliptic integral with the improper integral used to evaluate
it by the arithmetic-geometric mean.

For `b > 0`, the substitution is `θ = arctan (x / b)`; invariance under sign
changes covers `b < 0`. The open-interval change of variables
handles the endpoint at infinity without assigning a value to the integrand there.

## References

* J. M. Borwein and P. B. Borwein, *Pi and the AGM*, Wiley, 1987, Chapter 1.
-/

public section

open MeasureTheory Set
open scoped Real

namespace TauCeti

/-- The first-kind trigonometric integrand is continuous when both axes are nonzero. -/
theorem continuous_rpow_cos_sq_add_sin_sq {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Continuous (fun θ : ℝ =>
      (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2) ^ (-1 / 2 : ℝ)) := by
  apply Continuous.rpow_const (by fun_prop)
  intro θ
  left
  have hc := Real.cos_sq_add_sin_sq θ
  have hpos : 0 < a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2 := by
    rcases eq_or_lt_of_le (sq_nonneg (Real.cos θ)) with h | h
    · have hs : Real.sin θ ^ 2 = 1 := by linarith
      simp [← h, hs, sq_pos_of_ne_zero hb]
    · exact add_pos_of_pos_of_nonneg (mul_pos (sq_pos_of_ne_zero ha) h) (by positivity)
  exact hpos.ne'

/-- The trigonometric AGM integrand is integrable on every bounded interval. -/
theorem intervalIntegrable_rpow_cos_sq_add_sin_sq {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (u v : ℝ) :
    IntervalIntegrable (fun θ : ℝ =>
      (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2) ^ (-1 / 2 : ℝ))
      volume u v :=
  (continuous_rpow_cos_sq_add_sin_sq ha hb).intervalIntegrable u v

private theorem arctan_pullback {a b : ℝ} (ha : a ≠ 0) (hb : 0 < b) (x : ℝ) :
    b / (b ^ 2 + x ^ 2) *
        (a ^ 2 * Real.cos (Real.arctan (x / b)) ^ 2 +
          b ^ 2 * Real.sin (Real.arctan (x / b)) ^ 2) ^ (-1 / 2 : ℝ) =
      (Real.sqrt ((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)))⁻¹ := by
  have hd : 0 < b ^ 2 + x ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hb) (sq_nonneg x)
  have he : 0 < a ^ 2 + x ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg x)
  have htrig : a ^ 2 * Real.cos (Real.arctan (x / b)) ^ 2 +
      b ^ 2 * Real.sin (Real.arctan (x / b)) ^ 2 =
      b ^ 2 * (a ^ 2 + x ^ 2) / (b ^ 2 + x ^ 2) := by
    rw [Real.cos_sq_arctan, Real.sin_sq_arctan]
    field_simp
  rw [htrig, neg_div, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
  simp only [Real.sqrt_div' _ hd.le, Real.sqrt_mul (sq_nonneg b),
    Real.sqrt_sq hb.le, Real.sqrt_mul he.le, add_comm]
  have hs := Real.sq_sqrt hd.le
  have hs0 := (Real.sqrt_pos.mpr hd).ne'
  have he0 := (Real.sqrt_pos.mpr he).ne'
  field_simp
  nlinarith

/-- The trigonometric complete elliptic integral equals the improper AGM integral.
Both sides converge for nonzero `a` and `b`. -/
theorem integral_rpow_cos_sq_add_sin_sq_eq_integral_Ioi {a b : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    (∫ θ in (0 : ℝ)..Real.pi / 2,
      (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2) ^ (-1 / 2 : ℝ)) =
      ∫ x in Ioi (0 : ℝ), (Real.sqrt ((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)))⁻¹ := by
  wlog hbpos : 0 < b generalizing b
  · simpa only [sq_abs] using this (abs_ne_zero.mpr hb) (abs_pos.mpr hb)
  have himage : (fun x : ℝ => Real.arctan (x / b)) '' Ioi 0 = Ioo 0 (Real.pi / 2) := by
    ext θ
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Real.arctan_pos.mpr (div_pos hx hbpos), Real.arctan_lt_pi_div_two _⟩
    · intro hθ
      refine ⟨b * Real.tan θ, mul_pos hbpos (Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2), ?_⟩
      simp only [mul_div_cancel_left₀ _ hb]
      exact Real.arctan_tan (by linarith [Real.pi_pos, hθ.1]) hθ.2
  have hderiv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun x : ℝ => Real.arctan (x / b))
        (b / (b ^ 2 + x ^ 2)) (Ioi 0) x := by
    intro x _
    apply (((hasDerivAt_id' x).div_const b).arctan.congr_deriv ?_).hasDerivWithinAt
    field_simp
  have hinj : InjOn (fun x : ℝ => Real.arctan (x / b)) (Ioi 0) := by
    intro x _ y _ h
    exact (div_left_inj' hb).mp (Real.arctan_injective h)
  rw [intervalIntegral.integral_of_le (by positivity), integral_Ioc_eq_integral_Ioo,
    ← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  dsimp only
  rw [abs_of_pos (by positivity : 0 < b / (b ^ 2 + x ^ 2)), smul_eq_mul]
  exact arctan_pullback ha hbpos x

end TauCeti
