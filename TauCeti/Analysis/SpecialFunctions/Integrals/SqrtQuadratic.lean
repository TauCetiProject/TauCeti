/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import TauCeti.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Integrals against the square root of a quadratic between its roots

For `a < b` the quadratic `(x - a) (b - x)` is positive exactly on `(a, b)`, and the integrals of
`√((x - a) (b - x))` and its reciprocal against `1`, `x` and `1 / x` over `[a, b]` have closed
forms in terms of `π`, `a + b` and the geometric mean `√(a b)`:

* `∫ x in a..b, 1 / √((x - a) (b - x)) = π`;
* `∫ x in a..b, x / √((x - a) (b - x)) = π (a + b) / 2`;
* `∫ x in a..b, 1 / (x √((x - a) (b - x))) = π / √(a b)` for `0 < a`;
* `∫ x in a..b, √((x - a) (b - x)) / x = π ((a + b) / 2 - √(a b))` for `0 ≤ a`.

These are the quadratures of classical mechanics in one degree of freedom between two simple
turning points: after factoring the radial kinetic energy of a Kepler orbit or an isotropic
oscillator as such a quadratic, they compute the radial action, the radial period and the angle
swept between the turning points. The integrands `1 / √((x - a) (b - x))`,
`(x - a) / √((x - a) (b - x))` and, for `0 < a`, `1 / (x √((x - a) (b - x)))` are in general
unbounded at the endpoints, but they are nonnegative derivatives of continuous functions, hence
integrable; `x / √((x - a) (b - x))` is handled through the split `x = (x - a) + a`.

The antiderivatives are `arcsin ((2 x - a - b) / (b - a))` for `1 / √((x - a) (b - x))` and
`arcsin (((a + b) x - 2 a b) / ((b - a) x)) / √(a b)` for `1 / (x √((x - a) (b - x)))`.

The quadratic is the model for every function with simple zeros at `a` and `b`. If `g` is continuous
on `[a, b]`, positive on `(a, b)`, and vanishes at `a` and `b` with nonzero one-sided derivatives
there, then `g` dominates a positive multiple of `(x - a) (b - x)` on `[a, b]`, so by comparison
`1 / √(g x)` is interval integrable as well. This is the convergence of the time quadrature of a
one-dimensional motion between two simple turning points.

## Main declarations

* `TauCeti.integral_one_div_sqrt_mul_sub_mul_sub`
* `TauCeti.integral_div_sqrt_mul_sub_mul_sub`
* `TauCeti.integral_one_div_mul_sqrt_mul_sub_mul_sub`
* `TauCeti.integral_sqrt_mul_sub_mul_sub_div`
* `TauCeti.intervalIntegrable_one_div_sqrt_mul_sub_mul_sub`,
  `TauCeti.intervalIntegrable_div_sqrt_mul_sub_mul_sub`,
  `TauCeti.intervalIntegrable_one_div_mul_sqrt_mul_sub_mul_sub` and
  `TauCeti.intervalIntegrable_sqrt_mul_sub_mul_sub_div`: the integrability of the
  integrands that are in general unbounded at the endpoints.
* `TauCeti.exists_pos_forall_mul_mul_sub_mul_sub_le` and
  `TauCeti.intervalIntegrable_one_div_sqrt_of_hasDerivWithinAt`: domination by the quadratic and
  integrability of `1 / √g` for a function `g` with simple zeros at both ends.
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

private theorem continuous_neg_sqrt_add_mul_arcsin :
    Continuous (fun y => -√((y - a) * (b - y)) +
      (b - a) / 2 * arcsin ((2 * y - a - b) / (b - a))) := by
  fun_prop

/-- `-√((x - a) (b - x)) + (b - a) / 2 * arcsin ((2 x - a - b) / (b - a))` is an antiderivative
of `(x - a) / √((x - a) (b - x))` on `(a, b)`. -/
private theorem hasDerivAt_neg_sqrt_add_mul_arcsin {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (fun y => -√((y - a) * (b - y)) +
      (b - a) / 2 * arcsin ((2 * y - a - b) / (b - a))) ((x - a) / √((x - a) * (b - x))) x := by
  convert (hasDerivAt_sqrt_mul_sub_mul_sub hx).neg.add
    ((hasDerivAt_arcsin_two_mul_sub_sub_div_sub hx).const_mul ((b - a) / 2)) using 1
  have := (sqrt_mul_sub_mul_sub_pos hx).ne'
  field_simp
  ring

/-- `arcsin (((a + b) x - 2 a b) / ((b - a) x)) / √(a b)` is an antiderivative of
`1 / (x √((x - a) (b - x)))` on `(a, b)` for `0 < a`. -/
private theorem hasDerivAt_arcsin_add_mul_sub_div_sub_mul_div (ha : 0 < a) {x : ℝ}
    (hx : x ∈ Ioo a b) :
    HasDerivAt (fun y => arcsin (((a + b) * y - 2 * a * b) / ((b - a) * y)) / √(a * b))
      (1 / (x * √((x - a) * (b - x)))) x := by
  have hab' : 0 < √(a * b) := sqrt_pos.2 (mul_pos ha (ha.trans (hx.1.trans hx.2)))
  convert (hasDerivAt_arcsin_add_mul_sub_div_sub_mul ha hx).div_const (√(a * b)) using 1
  have := (sqrt_mul_sub_mul_sub_pos hx).ne'
  have := (ha.trans hx.1).ne'
  field_simp

private theorem intervalIntegrable_one_div_sqrt_mul_sub_mul_sub_of_le (hab : a ≤ b) :
    IntervalIntegrable (fun x => 1 / √((x - a) * (b - x))) volume a b := by
  refine intervalIntegrable_deriv_of_nonneg
    (continuous_arcsin_two_mul_sub_sub_div_sub (a := a) (b := b)).continuousOn ?_ ?_ <;>
    rw [Ioo_min_max, uIoo_of_le hab]
  exacts [fun x hx => hasDerivAt_arcsin_two_mul_sub_sub_div_sub hx, fun x _ => by positivity]

private theorem intervalIntegrable_sub_div_sqrt_mul_sub_mul_sub_of_le (hab : a ≤ b) :
    IntervalIntegrable (fun x => (x - a) / √((x - a) * (b - x))) volume a b := by
  refine intervalIntegrable_deriv_of_nonneg
    (continuous_neg_sqrt_add_mul_arcsin (a := a) (b := b)).continuousOn ?_ ?_ <;>
    rw [Ioo_min_max, uIoo_of_le hab]
  exacts [fun x hx => hasDerivAt_neg_sqrt_add_mul_arcsin hx,
    fun x hx => div_nonneg (sub_nonneg.2 hx.1.le) (sqrt_nonneg _)]

private theorem intervalIntegrable_div_sqrt_mul_sub_mul_sub_of_le (hab : a ≤ b) :
    IntervalIntegrable (fun x => x / √((x - a) * (b - x))) volume a b := by
  have hsplit : (fun x => x / √((x - a) * (b - x))) =
      fun x => (x - a) / √((x - a) * (b - x)) + a * (1 / √((x - a) * (b - x))) := by
    ext x; ring
  rw [hsplit]
  exact (intervalIntegrable_sub_div_sqrt_mul_sub_mul_sub_of_le hab).add
    ((intervalIntegrable_one_div_sqrt_mul_sub_mul_sub_of_le hab).const_mul a)

private theorem intervalIntegrable_one_div_mul_sqrt_mul_sub_mul_sub_of_le (ha : 0 < a)
    (hab : a ≤ b) :
    IntervalIntegrable (fun x => 1 / (x * √((x - a) * (b - x)))) volume a b := by
  rcases hab.eq_or_lt with rfl | hab
  · exact .refl
  have hcont := (continuousOn_arcsin_add_mul_sub_div_sub_mul ha hab).div_const (√(a * b))
  rw [← uIcc_of_le hab.le] at hcont
  refine intervalIntegrable_deriv_of_nonneg hcont ?_ ?_ <;> rw [Ioo_min_max, uIoo_of_le hab.le]
  exacts [fun x hx => hasDerivAt_arcsin_add_mul_sub_div_sub_mul_div ha hx,
    fun x hx => one_div_nonneg.2 (mul_nonneg (ha.trans hx.1).le (sqrt_nonneg _))]

private theorem mul_sub_mul_sub_comm (x : ℝ) : (x - b) * (a - x) = (x - a) * (b - x) := by ring

/-- `x ↦ 1 / √((x - a) (b - x))` is interval integrable between `a` and `b`, although it is
in general unbounded at the endpoints. -/
theorem intervalIntegrable_one_div_sqrt_mul_sub_mul_sub :
    IntervalIntegrable (fun x => 1 / √((x - a) * (b - x))) volume a b := by
  rcases le_total a b with hab | hba
  · exact intervalIntegrable_one_div_sqrt_mul_sub_mul_sub_of_le hab
  · simpa only [mul_sub_mul_sub_comm] using
      (intervalIntegrable_one_div_sqrt_mul_sub_mul_sub_of_le hba).symm

/-- `x ↦ x / √((x - a) (b - x))` is interval integrable between `a` and `b`, although it is
in general unbounded at the endpoints. -/
theorem intervalIntegrable_div_sqrt_mul_sub_mul_sub :
    IntervalIntegrable (fun x => x / √((x - a) * (b - x))) volume a b := by
  rcases le_total a b with hab | hba
  · exact intervalIntegrable_div_sqrt_mul_sub_mul_sub_of_le hab
  · simpa only [mul_sub_mul_sub_comm] using
      (intervalIntegrable_div_sqrt_mul_sub_mul_sub_of_le hba).symm

/-- `x ↦ 1 / (x √((x - a) (b - x)))` is interval integrable between positive `a` and `b`,
although it is in general unbounded at the endpoints. -/
theorem intervalIntegrable_one_div_mul_sqrt_mul_sub_mul_sub (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x => 1 / (x * √((x - a) * (b - x)))) volume a b := by
  rcases le_total a b with hab | hba
  · exact intervalIntegrable_one_div_mul_sqrt_mul_sub_mul_sub_of_le ha hab
  · simpa only [mul_sub_mul_sub_comm] using
      (intervalIntegrable_one_div_mul_sqrt_mul_sub_mul_sub_of_le hb hba).symm

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
  have h₁ := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le_of_nonneg hab.le
    continuous_neg_sqrt_add_mul_arcsin.continuousOn
    (fun x hx => hasDerivAt_neg_sqrt_add_mul_arcsin hx)
    (fun x hx => div_nonneg (sub_nonneg.2 hx.1.le) (sqrt_nonneg _))
  have h₀ := integral_one_div_sqrt_mul_sub_mul_sub hab
  have hsplit : (fun x => x / √((x - a) * (b - x))) =
      fun x => (x - a) / √((x - a) * (b - x)) + a * (1 / √((x - a) * (b - x))) := by
    ext x; ring
  rw [hsplit, intervalIntegral.integral_add
    (intervalIntegrable_sub_div_sqrt_mul_sub_mul_sub_of_le hab.le)
    (intervalIntegrable_one_div_sqrt_mul_sub_mul_sub.const_mul a),
    intervalIntegral.integral_const_mul, h₁, h₀]
  simp only [sub_self, mul_zero, zero_mul, sqrt_zero, neg_zero, zero_add]
  rw [arcsin_two_mul_sub_sub_div_sub_left hab, arcsin_two_mul_sub_sub_div_sub_right hab]
  ring

/-- `∫ x in a..b, 1 / (x √((x - a) (b - x))) = π / √(a b)` for `0 < a < b`. -/
theorem integral_one_div_mul_sqrt_mul_sub_mul_sub (ha : 0 < a) (hab : a < b) :
    ∫ x in a..b, 1 / (x * √((x - a) * (b - x))) = π / √(a * b) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le_of_nonneg hab.le
    ((continuousOn_arcsin_add_mul_sub_div_sub_mul ha hab).div_const _)
    (fun x hx => hasDerivAt_arcsin_add_mul_sub_div_sub_mul_div ha hx) fun x hx =>
    one_div_nonneg.2 (mul_nonneg (ha.trans hx.1).le (sqrt_nonneg _))]
  rw [arcsin_add_mul_sub_div_sub_mul_left ha hab, arcsin_add_mul_sub_div_sub_mul_right ha hab]
  ring

/-- `√((x - a) (b - x)) + (a + b) / 2 * arcsin ((2 x - a - b) / (b - a))
- √(a b) * arcsin (((a + b) x - 2 a b) / ((b - a) x))` is an antiderivative of
`√((x - a) (b - x)) / x` on `(a, b)` for `0 ≤ a`; at `a = 0` its last term vanishes. -/
private theorem hasDerivAt_sqrt_add_mul_arcsin_sub_mul_arcsin (ha : 0 ≤ a) {x : ℝ}
    (hx : x ∈ Ioo a b) :
    HasDerivAt (fun y => √((y - a) * (b - y)) + (a + b) / 2 *
      arcsin ((2 * y - a - b) / (b - a)) -
      √(a * b) * arcsin (((a + b) * y - 2 * a * b) / ((b - a) * y)))
      (√((x - a) * (b - x)) / x) x := by
  have hR := sqrt_mul_sub_mul_sub_pos hx
  have hx0 : 0 < x := ha.trans_lt hx.1
  have hb : 0 < b := hx0.trans hx.2
  have h₃ : HasDerivAt (fun y => √(a * b) * arcsin (((a + b) * y - 2 * a * b) / ((b - a) * y)))
      (√(a * b) * (√(a * b) / (x * √((x - a) * (b - x))))) x := by
    rcases ha.eq_or_lt with rfl | ha
    · simpa using hasDerivAt_const x (0 : ℝ)
    exact (hasDerivAt_arcsin_add_mul_sub_div_sub_mul ha hx).const_mul _
  convert ((hasDerivAt_sqrt_mul_sub_mul_sub hx).add
    ((hasDerivAt_arcsin_two_mul_sub_sub_div_sub hx).const_mul ((a + b) / 2))).sub h₃ using 1
  have hRsq : √((x - a) * (b - x)) ^ 2 = (x - a) * (b - x) :=
    sq_sqrt (mul_sub_mul_sub_pos hx).le
  have hab2 : √(a * b) ^ 2 = a * b := sq_sqrt (mul_nonneg ha hb.le)
  field_simp
  rw [hRsq, hab2]
  ring

private theorem continuousOn_sqrt_add_mul_arcsin_sub_mul_arcsin (ha : 0 ≤ a) (hab : a < b) :
    ContinuousOn (fun y => √((y - a) * (b - y)) + (a + b) / 2 *
      arcsin ((2 * y - a - b) / (b - a)) -
      √(a * b) * arcsin (((a + b) * y - 2 * a * b) / ((b - a) * y))) (Icc a b) := by
  refine ContinuousOn.sub (by fun_prop) ?_
  rcases ha.eq_or_lt with rfl | ha
  · simpa using continuousOn_const (c := (0 : ℝ))
  exact continuousOn_const.mul (continuousOn_arcsin_add_mul_sub_div_sub_mul ha hab)

private theorem intervalIntegrable_sqrt_mul_sub_mul_sub_div_of_le (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun x => √((x - a) * (b - x)) / x) volume a b := by
  rcases hab.eq_or_lt with rfl | hab
  · exact .refl
  have hcont := continuousOn_sqrt_add_mul_arcsin_sub_mul_arcsin ha hab
  rw [← uIcc_of_le hab.le] at hcont
  refine intervalIntegrable_deriv_of_nonneg hcont ?_ ?_ <;> rw [Ioo_min_max, uIoo_of_le hab.le]
  exacts [fun x hx => hasDerivAt_sqrt_add_mul_arcsin_sub_mul_arcsin ha hx,
    fun x hx => div_nonneg (sqrt_nonneg _) (ha.trans hx.1.le)]

/-- `x ↦ √((x - a) (b - x)) / x` is interval integrable between nonnegative `a` and `b`,
although it is unbounded near `0` when an endpoint is `0`. -/
theorem intervalIntegrable_sqrt_mul_sub_mul_sub_div (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun x => √((x - a) * (b - x)) / x) volume a b := by
  rcases le_total a b with hab | hba
  · exact intervalIntegrable_sqrt_mul_sub_mul_sub_div_of_le ha hab
  · simpa only [mul_sub_mul_sub_comm] using
      (intervalIntegrable_sqrt_mul_sub_mul_sub_div_of_le hb hba).symm

/-- `∫ x in a..b, √((x - a) (b - x)) / x = π ((a + b) / 2 - √(a b))` for `0 ≤ a ≤ b`. -/
theorem integral_sqrt_mul_sub_mul_sub_div (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ x in a..b, √((x - a) * (b - x)) / x = π * ((a + b) / 2 - √(a * b)) := by
  rcases hab.eq_or_lt with rfl | hab
  · rw [integral_same, sqrt_mul_self ha]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le_of_nonneg hab.le
    (continuousOn_sqrt_add_mul_arcsin_sub_mul_arcsin ha hab)
    (fun x hx => hasDerivAt_sqrt_add_mul_arcsin_sub_mul_arcsin ha hx) fun x hx =>
    div_nonneg (sqrt_nonneg _) (ha.trans hx.1.le)]
  simp only [sub_self, mul_zero, zero_mul, sqrt_zero, zero_add]
  rw [arcsin_two_mul_sub_sub_div_sub_left hab, arcsin_two_mul_sub_sub_div_sub_right hab]
  rcases ha.eq_or_lt with rfl | ha
  · simp only [zero_mul, sqrt_zero]
    ring
  rw [arcsin_add_mul_sub_div_sub_mul_left ha hab, arcsin_add_mul_sub_div_sub_mul_right ha hab]
  ring

/-! ### Functions with simple zeros at both ends -/

section SimpleZero

open Filter Topology
open scoped Interval

variable {g : ℝ → ℝ} {ga gb : ℝ}

/-- At a simple zero `a` to the right of which `g` is positive on `(a, b)`, `g` dominates a
positive multiple of `(x - a) (b - x)` on some interval `(a, u)`. -/
private theorem exists_pos_forall_mul_le_of_left (hab : a < b)
    (hpos : ∀ x ∈ Ioo a b, 0 < g x) (ha : g a = 0) (hga : HasDerivWithinAt g ga (Ici a) a)
    (hga0 : ga ≠ 0) : ∃ c > 0, ∃ u > a, ∀ x ∈ Ioo a u, c * ((x - a) * (b - x)) ≤ g x := by
  have ht : Tendsto (slope g a) (𝓝[>] a) (𝓝 ga) :=
    (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl a)).mp hga.Ioi_of_Ici
  have hslope : ∀ x ∈ Ioo a b, slope g a x = g x / (x - a) := fun x _ ↦ by
    rw [slope_def_field, ha, sub_zero]
  have hga' : 0 < ga := by
    refine lt_of_le_of_ne (ge_of_tendsto ht ?_) hga0.symm
    filter_upwards [Ioo_mem_nhdsGT hab] with x hx
    rw [hslope x hx]
    exact (div_pos (hpos x hx) (sub_pos.2 hx.1)).le
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (inter_mem (ht.eventually (lt_mem_nhds (half_lt_self hga'))) (Ioo_mem_nhdsGT hab))
  refine ⟨ga / (2 * (b - a)), by have := sub_pos.2 hab; positivity, u, hu, fun x hx ↦ ?_⟩
  obtain ⟨hlt, hx'⟩ := hsub hx
  rw [mem_ofPred_eq, hslope x hx', lt_div_iff₀ (sub_pos.2 hx'.1)] at hlt
  have hxa := sub_pos.2 hx'.1
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith [mul_pos (mul_pos hga' hxa) hxa]

/-- At a simple zero `b` to the left of which `g` is positive on `(a, b)`, `g` dominates a
positive multiple of `(x - a) (b - x)` on some interval `(u, b)`. -/
private theorem exists_pos_forall_mul_le_of_right (hab : a < b)
    (hpos : ∀ x ∈ Ioo a b, 0 < g x) (hb : g b = 0) (hgb : HasDerivWithinAt g gb (Iic b) b)
    (hgb0 : gb ≠ 0) : ∃ c > 0, ∃ u < b, ∀ x ∈ Ioo u b, c * ((x - a) * (b - x)) ≤ g x := by
  have ht : Tendsto (slope g b) (𝓝[<] b) (𝓝 gb) :=
    (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl b)).mp hgb.Iio_of_Iic
  have hslope : ∀ x ∈ Ioo a b, slope g b x = -(g x / (b - x)) := fun x _ ↦ by
    rw [slope_def_field, hb, sub_zero, ← neg_sub b x, div_neg]
  have hgb' : gb < 0 := by
    refine lt_of_le_of_ne (le_of_tendsto ht ?_) hgb0
    filter_upwards [Ioo_mem_nhdsLT hab] with x hx
    rw [hslope x hx, neg_nonpos]
    exact (div_pos (hpos x hx) (sub_pos.2 hx.2)).le
  obtain ⟨u, hu, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp
    (inter_mem (ht.eventually (gt_mem_nhds (show gb < gb / 2 by linarith)))
      (Ioo_mem_nhdsLT hab))
  refine ⟨-gb / (2 * (b - a)), div_pos (by linarith) (by linarith), u, hu, fun x hx ↦ ?_⟩
  obtain ⟨hlt, hx'⟩ := hsub hx
  rw [mem_ofPred_eq, hslope x hx', neg_lt, lt_div_iff₀ (sub_pos.2 hx'.2)] at hlt
  have hbx := sub_pos.2 hx'.2
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith [mul_pos (mul_pos (neg_pos.2 hgb') hbx) hbx]

/-- **A function with simple zeros at both ends of an interval dominates the quadratic with the
same zeros.** If `g` is continuous on `[a, b]`, positive on `(a, b)`, and vanishes at `a` and `b`
with nonzero one-sided derivatives there, then `c (x - a) (b - x) ≤ g x` on `[a, b]` for some
`c > 0`. -/
theorem exists_pos_forall_mul_mul_sub_mul_sub_le (hab : a < b) (hg : ContinuousOn g (Icc a b))
    (hpos : ∀ x ∈ Ioo a b, 0 < g x) (ha : g a = 0) (hb : g b = 0)
    (hga : HasDerivWithinAt g ga (Ici a) a) (hga0 : ga ≠ 0)
    (hgb : HasDerivWithinAt g gb (Iic b) b) (hgb0 : gb ≠ 0) :
    ∃ c > 0, ∀ x ∈ Icc a b, c * ((x - a) * (b - x)) ≤ g x := by
  obtain ⟨c₁, hc₁, u₁, hu₁, h₁⟩ := exists_pos_forall_mul_le_of_left hab hpos ha hga hga0
  obtain ⟨c₂, hc₂, u₂, hu₂, h₂⟩ := exists_pos_forall_mul_le_of_right hab hpos hb hgb hgb0
  -- On the compact middle part `[u₁, u₂]`, `g` is bounded below by a positive constant `c₀`,
  -- while `(x - a) (b - x) ≤ (b - a)²`.
  obtain ⟨c₃, hc₃, h₃⟩ : ∃ c > 0, ∀ x ∈ Icc u₁ u₂, c * ((x - a) * (b - x)) ≤ g x := by
    rcases (Icc u₁ u₂).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    have hsub : Icc u₁ u₂ ⊆ Ioo a b := Icc_subset_Ioo hu₁ hu₂
    obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn h
      (hg.mono (hsub.trans Ioo_subset_Icc_self))
    have hc₀ := hpos y (hsub hy)
    refine ⟨g y / (b - a) ^ 2, div_pos hc₀ (pow_pos (sub_pos.2 hab) 2), fun x hx ↦ ?_⟩
    have hx' := hsub hx
    have hq : 0 < (x - a) * (b - x) := mul_pos (sub_pos.2 hx'.1) (sub_pos.2 hx'.2)
    have hgx : g y ≤ g x := hmin hx
    rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos (sub_pos.2 hab) 2)]
    exact mul_le_mul hgx (by nlinarith [sq_nonneg (x - a - (b - x))]) hq.le (hc₀.le.trans hgx)
  refine ⟨min c₁ (min c₂ c₃), lt_min hc₁ (lt_min hc₂ hc₃), fun x hx ↦ ?_⟩
  have hq : 0 ≤ (x - a) * (b - x) := mul_nonneg (sub_nonneg.2 hx.1) (sub_nonneg.2 hx.2)
  rcases eq_or_lt_of_le hx.1 with rfl | hax
  · simp [ha]
  rcases lt_or_ge x u₁ with hx₁ | hx₁
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hq).trans (h₁ x ⟨hax, hx₁⟩)
  rcases eq_or_lt_of_le hx.2 with rfl | hxb
  · simp [hb]
  rcases lt_or_ge u₂ x with hx₂ | hx₂
  · exact (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) hq).trans
      (h₂ x ⟨hx₂, hxb⟩)
  · exact (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) hq).trans
      (h₃ x ⟨hx₁, hx₂⟩)

/-- **Quadratures across simple zeros converge.** If `g` is continuous on `[a, b]`, positive on
`(a, b)`, and vanishes at `a` and `b` with nonzero one-sided derivatives there, then
`x ↦ 1 / √(g x)` is interval integrable on `[a, b]`, although it is unbounded at both ends. -/
theorem intervalIntegrable_one_div_sqrt_of_hasDerivWithinAt (hab : a < b)
    (hg : ContinuousOn g (Icc a b)) (hpos : ∀ x ∈ Ioo a b, 0 < g x) (ha : g a = 0) (hb : g b = 0)
    (hga : HasDerivWithinAt g ga (Ici a) a) (hga0 : ga ≠ 0)
    (hgb : HasDerivWithinAt g gb (Iic b) b) (hgb0 : gb ≠ 0) :
    IntervalIntegrable (fun x => 1 / √(g x)) volume a b := by
  obtain ⟨c, hc, hle⟩ :=
    exists_pos_forall_mul_mul_sub_mul_sub_le hab hg hpos ha hb hga hga0 hgb hgb0
  have hI : Ι a b = Ioc a b := uIoc_of_le hab.le
  have hae : volume.restrict (Ioc a b) = volume.restrict (Ioo a b) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  refine ((intervalIntegrable_one_div_sqrt_mul_sub_mul_sub (a := a) (b := b)).const_mul
    (1 / √c)).mono_fun' ?_ ?_
  · rw [hI, hae]
    refine ContinuousOn.aestronglyMeasurable (fun x hx ↦ ?_) measurableSet_Ioo
    have hx0 : √(g x) ≠ 0 := (sqrt_pos.2 (hpos x hx)).ne'
    exact (continuousWithinAt_const.div
      ((hg x (Ioo_subset_Icc_self hx)).mono Ioo_subset_Icc_self).sqrt hx0)
  · rw [hI, hae]
    refine (ae_restrict_mem measurableSet_Ioo).mono fun x hx ↦ ?_
    have hq : 0 < (x - a) * (b - x) := mul_pos (sub_pos.2 hx.1) (sub_pos.2 hx.2)
    have hsq : √c * √((x - a) * (b - x)) ≤ √(g x) := by
      rw [← sqrt_mul hc.le]
      exact sqrt_le_sqrt (hle x (Ioo_subset_Icc_self hx))
    have hpos' : 0 < √c * √((x - a) * (b - x)) := by positivity
    simp only [Real.norm_of_nonneg (one_div_nonneg.2 (sqrt_nonneg (g x))), one_div_mul_one_div]
    exact one_div_le_one_div_of_le hpos' hsq

end SimpleZero

end TauCeti
