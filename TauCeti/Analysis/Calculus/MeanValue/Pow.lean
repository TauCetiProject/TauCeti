/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Increment bounds at the rate of a real power

These bounds control the increment of a function `u` of time between `a` and `b` by a multiple
of `|b - a| |a| ^ (β - 1)`, for `0 ≤ β ≤ 1`. This is the time-Lipschitz estimate of a function
that is Hölder in time with exponent `β` and whose derivative grows at most like `r ^ (β - 1)`
near `0`.

For `a > 0` and `a / 2 ≤ b`, the mean value inequality gives the bound from a derivative of norm
at most `D r ^ (β - 1)` at every `r` between `a` and `b`.

The two other cases need no derivative, only data at the two endpoints, so they are stated for
two points `x` and `y` of a pseudometric space, the values of `u` at `b` and `a`. For `a < 0`,
`0 ≤ β ≤ 1` and `0 ≤ K`, the data are that `dist x y` vanishes if `b ≤ 0` and is at most `K b ^ β`
if `0 < b`. For `0 < a` and `b ≤ a / 2`, they are that `x` and `y` both lie within `K a ^ β` of a
point `c`. When `0 ≤ β`, a function equal to `c` on `(-∞, 0]` with `dist (u r) c ≤ K r ^ β` for
`r ≥ 0` meets both, for `x = u b` and `y = u a`.

## Main results

* `TauCeti.norm_sub_le_mul_abs_sub_mul_rpow_of_hasDerivWithinAt`:
  `‖u b - u a‖ ≤ 2 D |b - a| a ^ (β - 1)` for `0 < a`, `a / 2 ≤ b` and `0 ≤ β ≤ 1` when
  `u` has derivative `u' r` within `[[a, b]]` with `‖u' r‖ ≤ D r ^ (β - 1)` at every
  `r ∈ [[a, b]]`.
* `TauCeti.dist_le_mul_abs_sub_mul_rpow_of_neg_right`: `dist x y ≤ K |b - a| (-a) ^ (β - 1)`
  for `a < 0`, `0 ≤ β ≤ 1` and `0 ≤ K`, when `dist x y = 0` if `b ≤ 0` and
  `dist x y ≤ K b ^ β` if `0 < b`.
* `TauCeti.dist_le_mul_abs_sub_mul_rpow_of_le_half`: `dist x y ≤ 4 K |b - a| a ^ (β - 1)` for
  `0 < a` and `b ≤ a / 2`, when `dist x c ≤ K a ^ β` and `dist y c ≤ K a ^ β`.
-/

public section

namespace TauCeti

open Real Set

/-- Mean value bound near `a > 0`: if `a / 2 ≤ b` and `u` has derivative `f' r` within
`[[a, b]]` of norm at most `D r^(β - 1)` at every `r ∈ [[a, b]]` (`0 ≤ β ≤ 1`), then
`‖u b - u a‖ ≤ 2 D |b - a| a^(β - 1)`. -/
theorem norm_sub_le_mul_abs_sub_mul_rpow_of_hasDerivWithinAt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {u f' : ℝ → F} {β D a b : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β - 1 ≤ 0) (ha : 0 < a)
    (hb : a / 2 ≤ b) (hderiv : ∀ r ∈ uIcc a b, HasDerivWithinAt u (f' r) (uIcc a b) r)
    (hbound : ∀ r ∈ uIcc a b, ‖f' r‖ ≤ D * r ^ (β - 1)) :
    ‖u b - u a‖ ≤ 2 * D * (|b - a| * a ^ (β - 1)) := by
  have ha2 : 0 < a / 2 := half_pos ha
  have hD : 0 ≤ D := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hbound a left_mem_uIcc))
    (rpow_pos_of_pos ha _)
  have hr2 (r : ℝ) (hr : r ∈ uIcc a b) : a / 2 ≤ r := by
    rcases mem_uIcc.1 hr with h | h <;> linarith [h.1]
  have hmv := (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le (f := u)
    (f' := f') (C := D * (a / 2) ^ (β - 1)) hderiv
    (fun r hr => (hbound r hr).trans
      (mul_le_mul_of_nonneg_left (rpow_le_rpow_of_nonpos ha2 (hr2 r hr) hβ₁) hD))
    left_mem_uIcc right_mem_uIcc
  have hhalf : (a / 2) ^ (β - 1) ≤ 2 * a ^ (β - 1) := by
    rw [div_rpow ha.le zero_le_two, div_eq_mul_inv, ← rpow_neg zero_le_two, neg_sub, mul_comm]
    gcongr
    calc (2 : ℝ) ^ (1 - β) ≤ 2 ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le one_le_two (by linarith)
      _ = 2 := rpow_one 2
  rw [Real.norm_eq_abs] at hmv
  calc ‖u b - u a‖ ≤ D * (a / 2) ^ (β - 1) * |b - a| := hmv
    _ ≤ D * (2 * a ^ (β - 1)) * |b - a| := by gcongr
    _ = _ := by ring

/-- If `a < 0`, `0 ≤ β ≤ 1` and `0 ≤ K`, and `dist x y` vanishes when `b ≤ 0` and is at most
`K b ^ β` when `0 < b`, then `dist x y ≤ K |b - a| (-a) ^ (β - 1)`. This bounds the increment
`dist (u b) (u a)` of a function `u` that is constant on `(-∞, 0]` and moves away from that
constant value at rate `K r ^ β` for `r ≥ 0`. -/
theorem dist_le_mul_abs_sub_mul_rpow_of_neg_right {X : Type*} [PseudoMetricSpace X]
    {x y : X} {β K a b : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β - 1 ≤ 0) (hK : 0 ≤ K) (ha : a < 0)
    (hneg : b ≤ 0 → dist x y = 0) (hpos : 0 < b → dist x y ≤ K * b ^ β) :
    dist x y ≤ K * (|b - a| * (-a) ^ (β - 1)) := by
  have hd : 0 < -a := neg_pos.2 ha
  rcases le_or_gt b 0 with hb | hb
  · rw [hneg hb]
    positivity
  have key : b ^ β ≤ |b - a| * (-a) ^ (β - 1) :=
    calc b ^ β ≤ (b - a) ^ β := rpow_le_rpow hb.le (by linarith) hβ₀
      _ ≤ (-a) ^ (β - 1) * (b - a) ^ (1 : ℝ) :=
          rpow_le_rpow_sub_mul_rpow_of_exponent_le hd (by linarith) (by linarith)
      _ = |b - a| * (-a) ^ (β - 1) := by
          rw [rpow_one, abs_of_pos (by linarith), mul_comm]
  exact (hpos hb).trans (by gcongr)

/-- If `0 < a` and `b ≤ a / 2`, and `x` and `y` both lie within `K a ^ β` of a point `c`, then
`dist x y ≤ 4 K |b - a| a ^ (β - 1)`. This bounds the increment `dist (u b) (u a)` of a function
`u` that is constant equal to `c` on `(-∞, 0]` with `dist (u r) c ≤ K r ^ β` for `r ≥ 0`, when
`0 ≤ β`. -/
theorem dist_le_mul_abs_sub_mul_rpow_of_le_half {X : Type*} [PseudoMetricSpace X]
    {x y c : X} {β K a b : ℝ} (ha : 0 < a) (hb : b ≤ a / 2) (hx : dist x c ≤ K * a ^ β)
    (hy : dist y c ≤ K * a ^ β) :
    dist x y ≤ 4 * K * (|b - a| * a ^ (β - 1)) := by
  have hK : 0 ≤ K :=
    nonneg_of_mul_nonneg_left (dist_nonneg.trans hx) (rpow_pos_of_pos ha β)
  have h3 : a ^ β ≤ 2 * (|b - a| * a ^ (β - 1)) := by
    have hpow : a ^ β = a * a ^ (β - 1) := by
      simpa only [sub_add_cancel, mul_comm] using (rpow_add_one ha.ne' (β - 1))
    rw [hpow, abs_of_neg (by linarith : b - a < 0)]
    have : 0 ≤ a ^ (β - 1) := by positivity
    nlinarith
  calc dist x y ≤ dist x c + dist y c := dist_triangle_right _ _ _
    _ ≤ 2 * (K * a ^ β) := by linarith
    _ ≤ 2 * (K * (2 * (|b - a| * a ^ (β - 1)))) := by gcongr
    _ = _ := by ring

end TauCeti
