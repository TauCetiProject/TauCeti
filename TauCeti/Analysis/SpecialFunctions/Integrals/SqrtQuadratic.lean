/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import TauCeti.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Integrals against the square root of a quadratic between its roots

For `a < b` the quadratic `(x - a) (b - x)` is positive exactly on `(a, b)`, and the integrals of
`√((x - a) (b - x))` and its reciprocal against `1`, `x` and `1 / x` over `[a, b]` have closed
forms in terms of `π`, `a + b` and the geometric mean `√(a b)`:

* `∫ x in a..b, 1 / √((x - a) (b - x)) = π`;
* `∫ x in a..b, x / √((x - a) (b - x)) = π (a + b) / 2`;
* `∫ x in a..b, 1 / (x √((x - a) (b - x))) = π / √(a b)` for `0 < a`;
* `∫ x in a..b, √((x - a) (b - x)) / x = π ((a + b) / 2 - √(a b))` for `0 < a`.

These are the quadratures of classical mechanics in one degree of freedom between two simple
turning points: after factoring the radial kinetic energy of a Kepler orbit or an isotropic
oscillator as such a quadratic, they compute the radial action, the radial period and the angle
swept between the turning points. The first two integrands are unbounded at the endpoints but
nonnegative, so they are integrable because they are derivatives of continuous functions.

The antiderivatives are `arcsin ((2 x - a - b) / (b - a))` for `1 / √((x - a) (b - x))` and
`arcsin (((a + b) x - 2 a b) / ((b - a) x)) / √(a b)` for `1 / (x √((x - a) (b - x)))`.

## Main declarations

* `TauCeti.integral_one_div_sqrt_mul_sub_mul_sub`
* `TauCeti.integral_div_sqrt_mul_sub_mul_sub`
* `TauCeti.integral_one_div_mul_sqrt_mul_sub_mul_sub`
* `TauCeti.integral_sqrt_mul_sub_mul_sub_div`
* `TauCeti.hasDerivAt_arcsin_two_mul_sub_sub_div_sub`,
  `TauCeti.hasDerivAt_arcsin_add_mul_sub_div_sub_mul` and
  `TauCeti.hasDerivAt_sqrt_mul_sub_mul_sub`: the derivatives of the antiderivatives on `(a, b)`.

## References

* I. S. Gradshteyn, I. M. Ryzhik, *Table of Integrals, Series, and Products*, 7th ed., Academic
  Press, 2007, Section 2.26.
-/

public section

open Real Set intervalIntegral MeasureTheory

namespace TauCeti

variable {a b : ℝ}

private theorem mul_sub_mul_sub_pos {x : ℝ} (hx : x ∈ Ioo a b) : 0 < (x - a) * (b - x) :=
  mul_pos (sub_pos.2 hx.1) (sub_pos.2 hx.2)

private theorem sqrt_mul_sub_mul_sub_pos {x : ℝ} (hx : x ∈ Ioo a b) :
    0 < √((x - a) * (b - x)) :=
  sqrt_pos.2 (mul_sub_mul_sub_pos hx)

/-- `arcsin ((2 x - a - b) / (b - a))` is an antiderivative of `1 / √((x - a) (b - x))`. -/
theorem hasDerivAt_arcsin_two_mul_sub_sub_div_sub {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (fun y => arcsin ((2 * y - a - b) / (b - a))) (1 / √((x - a) * (b - x))) x := by
  have hba : 0 < b - a := sub_pos.2 (hx.1.trans hx.2)
  have hR := sqrt_mul_sub_mul_sub_pos hx
  have hsq : 1 - ((2 * x - a - b) / (b - a)) ^ 2 = (2 / (b - a)) ^ 2 * ((x - a) * (b - x)) := by
    field_simp; ring
  have hlt : ((2 * x - a - b) / (b - a)) ^ 2 < 1 := by
    have := mul_sub_mul_sub_pos hx
    nlinarith [hsq, sq_nonneg (2 / (b - a)), pow_pos (div_pos two_pos hba) 2]
  have h1 : (2 * x - a - b) / (b - a) ≠ -1 := fun h => by rw [h] at hlt; norm_num at hlt
  have h2 : (2 * x - a - b) / (b - a) ≠ 1 := fun h => by rw [h] at hlt; norm_num at hlt
  have hg : HasDerivAt (fun y => (2 * y - a - b) / (b - a)) (2 / (b - a)) x := by
    simpa using (((hasDerivAt_id x).const_mul 2).sub_const a |>.sub_const b).div_const (b - a)
  refine ((hasDerivAt_arcsin h1 h2).comp x hg).congr_deriv ?_
  rw [hsq, sqrt_mul (by positivity), sqrt_sq (by positivity)]
  field_simp

/-- `arcsin (((a + b) x - 2 a b) / ((b - a) x))` is an antiderivative of
`√(a b) / (x √((x - a) (b - x)))` for `0 < a`. -/
theorem hasDerivAt_arcsin_add_mul_sub_div_sub_mul (ha : 0 < a) {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (fun y => arcsin (((a + b) * y - 2 * a * b) / ((b - a) * y)))
      (√(a * b) / (x * √((x - a) * (b - x)))) x := by
  have hba : 0 < b - a := sub_pos.2 (hx.1.trans hx.2)
  have hx0 : 0 < x := ha.trans hx.1
  have hb : 0 < b := hx0.trans hx.2
  have hR := sqrt_mul_sub_mul_sub_pos hx
  have hab : 0 < √(a * b) := sqrt_pos.2 (mul_pos ha hb)
  have hsq : 1 - (((a + b) * x - 2 * a * b) / ((b - a) * x)) ^ 2 =
      (2 * √(a * b) / ((b - a) * x)) ^ 2 * ((x - a) * (b - x)) := by
    rw [div_pow, div_pow, mul_pow (2 : ℝ), sq_sqrt (mul_pos ha hb).le]
    field_simp
    ring
  have hlt : (((a + b) * x - 2 * a * b) / ((b - a) * x)) ^ 2 < 1 := by
    have := mul_sub_mul_sub_pos hx
    have : 0 < (2 * √(a * b) / ((b - a) * x)) ^ 2 := by positivity
    nlinarith [hsq]
  have h1 : ((a + b) * x - 2 * a * b) / ((b - a) * x) ≠ -1 := fun h => by
    rw [h] at hlt; norm_num at hlt
  have h2 : ((a + b) * x - 2 * a * b) / ((b - a) * x) ≠ 1 := fun h => by
    rw [h] at hlt; norm_num at hlt
  have hh : HasDerivAt (fun y => ((a + b) * y - 2 * a * b) / ((b - a) * y))
      (2 * a * b / ((b - a) * x ^ 2)) x := by
    have hn : HasDerivAt (fun y => (a + b) * y - 2 * a * b) (a + b) x := by
      simpa using ((hasDerivAt_id x).const_mul (a + b)).sub_const (2 * a * b)
    have hd : HasDerivAt (fun y => (b - a) * y) (b - a) x := by
      simpa using (hasDerivAt_id x).const_mul (b - a)
    refine (hn.div hd (by positivity)).congr_deriv ?_
    field_simp
    ring
  refine ((hasDerivAt_arcsin h1 h2).comp x hh).congr_deriv ?_
  rw [hsq, sqrt_mul (by positivity), sqrt_sq (by positivity)]
  have hab2 : √(a * b) ^ 2 = a * b := sq_sqrt (mul_pos ha hb).le
  field_simp
  rw [hab2]

/-- `√((x - a) (b - x))` has derivative `(a + b - 2 x) / (2 √((x - a) (b - x)))` on `(a, b)`. -/
theorem hasDerivAt_sqrt_mul_sub_mul_sub {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (fun y => √((y - a) * (b - y)))
      ((a + b - 2 * x) / (2 * √((x - a) * (b - x)))) x := by
  have hp : HasDerivAt (fun y => (y - a) * (b - y)) (a + b - 2 * x) x := by
    refine (((hasDerivAt_id x).sub_const a).mul ((hasDerivAt_id x).const_sub b)).congr_deriv ?_
    simp only [id]
    ring
  exact hp.sqrt (mul_sub_mul_sub_pos hx).ne'

private theorem continuous_arcsin_two_mul_sub_sub_div_sub :
    Continuous (fun y => arcsin ((2 * y - a - b) / (b - a))) := by
  fun_prop

private theorem arcsin_two_mul_sub_sub_div_sub_left (hab : a < b) :
    arcsin ((2 * a - a - b) / (b - a)) = -(π / 2) := by
  rw [show (2 * a - a - b) / (b - a) = -1 by field_simp [(sub_pos.2 hab).ne']; ring,
    arcsin_neg_one]

private theorem arcsin_two_mul_sub_sub_div_sub_right (hab : a < b) :
    arcsin ((2 * b - a - b) / (b - a)) = π / 2 := by
  rw [show (2 * b - a - b) / (b - a) = 1 by field_simp [(sub_pos.2 hab).ne']; ring, arcsin_one]

private theorem continuousOn_arcsin_add_mul_sub_div_sub_mul (ha : 0 < a) (hab : a < b) :
    ContinuousOn (fun y => arcsin (((a + b) * y - 2 * a * b) / ((b - a) * y))) (Icc a b) :=
  continuous_arcsin.comp_continuousOn <| ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx =>
    mul_ne_zero (sub_pos.2 hab).ne' (ha.trans_le hx.1).ne'

private theorem arcsin_add_mul_sub_div_sub_mul_left (ha : 0 < a) (hab : a < b) :
    arcsin (((a + b) * a - 2 * a * b) / ((b - a) * a)) = -(π / 2) := by
  have := (sub_pos.2 hab).ne'
  have := ha.ne'
  rw [show ((a + b) * a - 2 * a * b) / ((b - a) * a) = -1 by field_simp; ring, arcsin_neg_one]

private theorem arcsin_add_mul_sub_div_sub_mul_right (ha : 0 < a) (hab : a < b) :
    arcsin (((a + b) * b - 2 * a * b) / ((b - a) * b)) = π / 2 := by
  have := (sub_pos.2 hab).ne'
  have := (ha.trans hab).ne'
  rw [show ((a + b) * b - 2 * a * b) / ((b - a) * b) = 1 by field_simp; ring, arcsin_one]

/-- `∫ x in a..b, 1 / √((x - a) (b - x)) = π` for `a < b`. -/
theorem integral_one_div_sqrt_mul_sub_mul_sub (hab : a < b) :
    ∫ x in a..b, 1 / √((x - a) * (b - x)) = π := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le_of_nonneg hab.le
    continuous_arcsin_two_mul_sub_sub_div_sub.continuousOn
    (fun x hx => hasDerivAt_arcsin_two_mul_sub_sub_div_sub hx) (fun x _ => by positivity),
    arcsin_two_mul_sub_sub_div_sub_left hab, arcsin_two_mul_sub_sub_div_sub_right hab]
  ring

/-- `∫ x in a..b, x / √((x - a) (b - x)) = π (a + b) / 2` for `a < b`. -/
theorem integral_div_sqrt_mul_sub_mul_sub (hab : a < b) :
    ∫ x in a..b, x / √((x - a) * (b - x)) = π * (a + b) / 2 := by
  -- Split `x = (x - a) + a`; the first part is the nonnegative derivative of
  -- `-√((x - a) (b - x)) + (b - a) / 2 * arcsin ((2 x - a - b) / (b - a))`.
  have hcont : ContinuousOn (fun y => -√((y - a) * (b - y)) +
      (b - a) / 2 * arcsin ((2 * y - a - b) / (b - a))) (Icc a b) := by
    fun_prop
  have hd : ∀ x ∈ Ioo a b, HasDerivAt (fun y => -√((y - a) * (b - y)) +
      (b - a) / 2 * arcsin ((2 * y - a - b) / (b - a))) ((x - a) / √((x - a) * (b - x))) x := by
    intro x hx
    convert (hasDerivAt_sqrt_mul_sub_mul_sub hx).neg.add
      ((hasDerivAt_arcsin_two_mul_sub_sub_div_sub hx).const_mul ((b - a) / 2)) using 1
    have := (sqrt_mul_sub_mul_sub_pos hx).ne'
    field_simp
    ring
  have h₁ := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le_of_nonneg hab.le hcont hd
    (fun x hx => div_nonneg (sub_nonneg.2 hx.1.le) (sqrt_nonneg _))
  have h₀ := integral_one_div_sqrt_mul_sub_mul_sub hab
  have hIoo : Ioo (min a b) (max a b) = Ioo a b := by rw [min_eq_left hab.le, max_eq_right hab.le]
  have hi₁ : IntervalIntegrable (fun x => (x - a) / √((x - a) * (b - x))) volume a b := by
    refine intervalIntegrable_deriv_of_nonneg (by rwa [uIcc_of_le hab.le]) ?_ ?_ <;> rw [hIoo]
    exacts [hd, fun x hx => div_nonneg (sub_nonneg.2 hx.1.le) (sqrt_nonneg _)]
  have hi₀ : IntervalIntegrable (fun x => 1 / √((x - a) * (b - x))) volume a b := by
    refine intervalIntegrable_deriv_of_nonneg
      (continuous_arcsin_two_mul_sub_sub_div_sub (a := a) (b := b)).continuousOn ?_ ?_ <;>
      rw [hIoo]
    exacts [fun x hx => hasDerivAt_arcsin_two_mul_sub_sub_div_sub hx, fun x _ => by positivity]
  have hsplit : (fun x => x / √((x - a) * (b - x))) =
      fun x => (x - a) / √((x - a) * (b - x)) + a * (1 / √((x - a) * (b - x))) := by
    ext x; ring
  rw [hsplit, intervalIntegral.integral_add hi₁ (hi₀.const_mul a),
    intervalIntegral.integral_const_mul, h₁, h₀]
  simp only [sub_self, mul_zero, zero_mul, sqrt_zero, neg_zero, zero_add]
  rw [arcsin_two_mul_sub_sub_div_sub_left hab, arcsin_two_mul_sub_sub_div_sub_right hab]
  ring

/-- `∫ x in a..b, 1 / (x √((x - a) (b - x))) = π / √(a b)` for `0 < a < b`. -/
theorem integral_one_div_mul_sqrt_mul_sub_mul_sub (ha : 0 < a) (hab : a < b) :
    ∫ x in a..b, 1 / (x * √((x - a) * (b - x))) = π / √(a * b) := by
  have hb : 0 < b := ha.trans hab
  have hab' : 0 < √(a * b) := sqrt_pos.2 (mul_pos ha hb)
  have hcont : ContinuousOn (fun y => arcsin (((a + b) * y - 2 * a * b) / ((b - a) * y)) /
      √(a * b)) (Icc a b) :=
    (continuousOn_arcsin_add_mul_sub_div_sub_mul ha hab).div_const _
  have hd : ∀ x ∈ Ioo a b, HasDerivAt (fun y => arcsin (((a + b) * y - 2 * a * b) /
      ((b - a) * y)) / √(a * b)) (1 / (x * √((x - a) * (b - x)))) x := by
    intro x hx
    convert (hasDerivAt_arcsin_add_mul_sub_div_sub_mul ha hx).div_const (√(a * b)) using 1
    have := (sqrt_mul_sub_mul_sub_pos hx).ne'
    have := (ha.trans hx.1).ne'
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le_of_nonneg hab.le hcont hd fun x hx =>
    one_div_nonneg.2 (mul_nonneg (ha.trans hx.1).le (sqrt_nonneg _))]
  rw [arcsin_add_mul_sub_div_sub_mul_left ha hab, arcsin_add_mul_sub_div_sub_mul_right ha hab]
  ring

/-- `∫ x in a..b, √((x - a) (b - x)) / x = π ((a + b) / 2 - √(a b))` for `0 < a ≤ b`. -/
theorem integral_sqrt_mul_sub_mul_sub_div (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, √((x - a) * (b - x)) / x = π * ((a + b) / 2 - √(a * b)) := by
  rcases hab.eq_or_lt with rfl | hab
  · rw [integral_same, sqrt_mul_self ha.le]
    ring
  -- On `(a, b)`, `√((x - a) (b - x)) / x = (a + b - 2 x) / (2 √(…)) + (a + b) / 2 * 1 / √(…)
  -- - a b / (x √(…))`, the derivative of an explicit continuous function.
  have hb : 0 < b := ha.trans hab
  have hab' : 0 < √(a * b) := sqrt_pos.2 (mul_pos ha hb)
  set F : ℝ → ℝ := fun y => √((y - a) * (b - y)) + (a + b) / 2 *
      arcsin ((2 * y - a - b) / (b - a)) -
      √(a * b) * arcsin (((a + b) * y - 2 * a * b) / ((b - a) * y)) with hF
  have hcont : ContinuousOn F (Icc a b) :=
    ContinuousOn.sub (by fun_prop)
      (continuousOn_const.mul (continuousOn_arcsin_add_mul_sub_div_sub_mul ha hab))
  have hd : ∀ x ∈ Ioo a b, HasDerivAt F (√((x - a) * (b - x)) / x) x := by
    intro x hx
    have hR := sqrt_mul_sub_mul_sub_pos hx
    have hx0 : 0 < x := ha.trans hx.1
    convert ((hasDerivAt_sqrt_mul_sub_mul_sub hx).add
      ((hasDerivAt_arcsin_two_mul_sub_sub_div_sub hx).const_mul ((a + b) / 2))).sub
      ((hasDerivAt_arcsin_add_mul_sub_div_sub_mul ha hx).const_mul (√(a * b))) using 1
    have hRsq : √((x - a) * (b - x)) ^ 2 = (x - a) * (b - x) :=
      sq_sqrt (mul_sub_mul_sub_pos hx).le
    have hab2 : √(a * b) ^ 2 = a * b := sq_sqrt (mul_pos ha hb).le
    field_simp
    rw [hRsq, hab2]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le_of_nonneg hab.le hcont hd fun x hx =>
    div_nonneg (sqrt_nonneg _) (ha.trans hx.1).le]
  simp only [hF, sub_self, mul_zero, zero_mul, sqrt_zero, zero_add]
  rw [arcsin_two_mul_sub_sub_div_sub_left hab, arcsin_two_mul_sub_sub_div_sub_right hab,
    arcsin_add_mul_sub_div_sub_mul_left ha hab, arcsin_add_mul_sub_div_sub_mul_right ha hab]
  ring

end TauCeti
