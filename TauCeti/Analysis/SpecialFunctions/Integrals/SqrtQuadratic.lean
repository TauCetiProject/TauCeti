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

The quadratic also controls the general case. A function `f` that is continuous on `[a, b]`,
positive on `(a, b)` and has *simple zeros* at both endpoints, `f a = f b = 0` with nonzero
one-sided derivatives there, dominates `c (x - a) (b - x)` on `[a, b]` for some `c > 0`. By
comparison with `1 / √((x - a) (b - x))`, the quotient `g / √f` is then interval integrable for
every `g` continuous on `[a, b]`: the quadratures of a one-degree-of-freedom motion converge
between any two simple turning points.

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
* `TauCeti.hasDerivAt_arcsin_two_mul_sub_sub_div_sub`,
  `TauCeti.hasDerivAt_arcsin_add_mul_sub_div_sub_mul` and
  `TauCeti.hasDerivAt_sqrt_mul_sub_mul_sub`: the derivatives of the antiderivatives on `(a, b)`.
* `TauCeti.exists_pos_forall_mul_mul_sub_mul_sub_le`: a function with simple zeros at `a` and `b`
  dominates a positive multiple of `(x - a) (b - x)`.
* `TauCeti.intervalIntegrable_div_sqrt_of_hasDerivWithinAt`: `g / √f` is interval integrable when
  `f` has simple zeros at the endpoints.

## References

* I. S. Gradshteyn, I. M. Ryzhik, *Table of Integrals, Series, and Products*, 7th ed., Academic
  Press, 2007, Section 2.26.
-/

public section

open Real Set intervalIntegral MeasureTheory Filter Topology

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

/-! ### Functions with simple zeros at the endpoints -/

/-- A function that is positive on `(a, b)`, vanishes at both endpoints and has nonzero one-sided
derivatives there dominates a positive multiple of the quadratic `(x - a) (b - x)` on `[a, b]`. -/
theorem exists_pos_forall_mul_mul_sub_mul_sub_le {f : ℝ → ℝ} {fa fb : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hpos : ∀ x ∈ Ioo a b, 0 < f x) (ha : f a = 0)
    (hb : f b = 0) (hfa : HasDerivWithinAt f fa (Ici a) a) (hfa₀ : fa ≠ 0)
    (hfb : HasDerivWithinAt f fb (Iic b) b) (hfb₀ : fb ≠ 0) :
    ∃ c > 0, ∀ x ∈ Icc a b, c * ((x - a) * (b - x)) ≤ f x := by
  have hsa : Tendsto (slope f a) (𝓝[>] a) (𝓝 fa) := by
    simpa [Ici_sdiff_left] using hasDerivWithinAt_iff_tendsto_slope.1 hfa
  have hsb : Tendsto (slope f b) (𝓝[<] b) (𝓝 fb) := by
    simpa [Iic_sdiff_right] using hasDerivWithinAt_iff_tendsto_slope.1 hfb
  have hslope_a : ∀ x, slope f a x = f x / (x - a) := fun x ↦ by rw [slope_def_field, ha, sub_zero]
  have hslope_b : ∀ x, slope f b x = f x / (x - b) := fun x ↦ by rw [slope_def_field, hb, sub_zero]
  -- The signs of the derivatives are forced by positivity on `(a, b)`.
  have hfa_pos : 0 < fa := lt_of_le_of_ne (ge_of_tendsto hsa (mem_of_superset (Ioo_mem_nhdsGT hab)
    fun x hx ↦ by
      rw [mem_ofPred_eq, hslope_a]
      exact (div_pos (hpos x hx) (sub_pos.2 hx.1)).le)) hfa₀.symm
  have hfb_neg : fb < 0 := lt_of_le_of_ne (le_of_tendsto hsb (mem_of_superset (Ioo_mem_nhdsLT hab)
    fun x hx ↦ by
      rw [mem_ofPred_eq, hslope_b]
      exact (div_neg_of_pos_of_neg (hpos x hx) (sub_neg.2 hx.2)).le)) hfb₀
  -- Near each endpoint the slope bounds `f` below by a linear function.
  obtain ⟨u, hu, hua⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (inter_mem (hsa.eventually (lt_mem_nhds (half_lt_self hfa_pos))) (Ioo_mem_nhdsGT hab))
  obtain ⟨l, hl, hlb⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1
    (inter_mem (hsb.eventually (gt_mem_nhds (show fb < fb / 2 by linarith))) (Ioo_mem_nhdsLT hab))
  -- In between, `f` is bounded below by a positive constant.
  have hul : Icc u l ⊆ Ioo a b := fun x hx ↦ ⟨(mem_Ioi.1 hu).trans_le hx.1, hx.2.trans_lt hl⟩
  obtain ⟨μ, hμ, hμf⟩ := isCompact_Icc.exists_forall_le' (hf.mono (hul.trans Ioo_subset_Icc_self))
    fun x hx ↦ hpos x (hul hx)
  have hba : 0 < b - a := sub_pos.2 hab
  refine ⟨min (min (fa / 2 / (b - a)) (-fb / 2 / (b - a))) (μ / (b - a) ^ 2),
    lt_min (lt_min (by positivity) (div_pos (by linarith) hba)) (by positivity), fun x hx ↦ ?_⟩
  have hxa : 0 ≤ x - a := sub_nonneg.2 hx.1
  have hbx : 0 ≤ b - x := sub_nonneg.2 hx.2
  rcases lt_or_ge x u with hxu | hux
  · rcases hx.1.eq_or_lt with rfl | hax
    · simp [ha]
    have hx' := hua ⟨hax, hxu⟩
    have h₁ : fa / 2 * (x - a) < f x := by
      have := hx'.1
      rw [mem_ofPred_eq, hslope_a, lt_div_iff₀ (sub_pos.2 hax)] at this
      exact this
    calc min (min (fa / 2 / (b - a)) (-fb / 2 / (b - a))) (μ / (b - a) ^ 2) * ((x - a) * (b - x))
        ≤ fa / 2 / (b - a) * ((x - a) * (b - x)) :=
          mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _))
            (mul_nonneg hxa hbx)
      _ ≤ fa / 2 * (x - a) := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hba]
          have : 0 ≤ fa / 2 * (x - a) := by positivity
          nlinarith
      _ ≤ f x := h₁.le
  rcases lt_or_ge l x with hlx | hxl
  · rcases hx.2.eq_or_lt with rfl | hxb
    · simp [hb]
    have hx' := hlb ⟨hlx, hxb⟩
    have h₂ : -fb / 2 * (b - x) < f x := by
      have := hx'.1
      rw [mem_ofPred_eq, hslope_b, div_lt_iff_of_neg (sub_neg.2 hxb)] at this
      linarith
    calc min (min (fa / 2 / (b - a)) (-fb / 2 / (b - a))) (μ / (b - a) ^ 2) * ((x - a) * (b - x))
        ≤ -fb / 2 / (b - a) * ((x - a) * (b - x)) :=
          mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_right _ _))
            (mul_nonneg hxa hbx)
      _ ≤ -fb / 2 * (b - x) := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hba]
          have : 0 ≤ -fb / 2 * (b - x) := mul_nonneg (by linarith) hbx
          nlinarith
      _ ≤ f x := h₂.le
  calc min (min (fa / 2 / (b - a)) (-fb / 2 / (b - a))) (μ / (b - a) ^ 2) * ((x - a) * (b - x))
      ≤ μ / (b - a) ^ 2 * ((x - a) * (b - x)) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (mul_nonneg hxa hbx)
    _ ≤ μ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        have hxa' : x - a ≤ b - a := by linarith [hx.2]
        have hbx' : b - x ≤ b - a := by linarith [hx.1]
        have : (x - a) * (b - x) ≤ (b - a) ^ 2 := by
          rw [sq]; exact mul_le_mul hxa' hbx' hbx hba.le
        nlinarith
    _ ≤ f x := hμf x ⟨hux, hxl⟩

/-- Let `f` be continuous on `[a, b]`, positive on `(a, b)`, with **simple zeros** at both
endpoints: `f a = f b = 0` with nonzero one-sided derivatives there. Then `g / √f` is interval
integrable on `[a, b]` for every `g` continuous on `[a, b]`, although it is in general unbounded at
the endpoints. This is the convergence of the quadratures of a one-degree-of-freedom motion between
two simple turning points. -/
theorem intervalIntegrable_div_sqrt_of_hasDerivWithinAt {f g : ℝ → ℝ} {fa fb : ℝ} (hab : a < b)
    (hg : ContinuousOn g (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) (ha : f a = 0) (hb : f b = 0)
    (hfa : HasDerivWithinAt f fa (Ici a) a) (hfa₀ : fa ≠ 0)
    (hfb : HasDerivWithinAt f fb (Iic b) b) (hfb₀ : fb ≠ 0) :
    IntervalIntegrable (fun x ↦ g x / √(f x)) volume a b := by
  obtain ⟨c, hc, hcf⟩ :=
    exists_pos_forall_mul_mul_sub_mul_sub_le hab hf hpos ha hb hfa hfa₀ hfb hfb₀
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  refine (intervalIntegrable_one_div_sqrt_mul_sub_mul_sub.const_mul (M / √c)).mono_fun' ?_ ?_ <;>
    rw [uIoc_of_le hab.le, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  · exact ((hg.mono Ioo_subset_Icc_self).div (hf.mono Ioo_subset_Icc_self).sqrt
      fun x hx ↦ (sqrt_pos.2 (hpos x hx)).ne').aestronglyMeasurable measurableSet_Ioo
  refine (ae_restrict_mem measurableSet_Ioo).mono fun x hx ↦ ?_
  have hq : 0 < (x - a) * (b - x) := mul_pos (sub_pos.2 hx.1) (sub_pos.2 hx.2)
  have hgx : ‖g x‖ ≤ M := hM x (Ioo_subset_Icc_self hx)
  have hle : √c * √((x - a) * (b - x)) ≤ √(f x) := by
    rw [← sqrt_mul hc.le]
    exact sqrt_le_sqrt (hcf x (Ioo_subset_Icc_self hx))
  dsimp only
  rw [norm_div, Real.norm_of_nonneg (sqrt_nonneg _), mul_one_div, div_div]
  exact div_le_div₀ ((norm_nonneg _).trans hgx) hgx (by positivity) hle

end TauCeti
