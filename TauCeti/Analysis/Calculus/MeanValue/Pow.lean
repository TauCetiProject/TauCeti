/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.SpecialFunctions.Pow.Scaling

/-!
# Increment bounds at the rate of a real power

These are scale-dependent increment bounds: they control the increment of a function `u` of
time between `a` and `b` by a multiple of `|b - a|` times a power `r ^ (β - 1)` of a time scale
`r` set by the endpoints (`min a b`, `-a` or `a` below). So `u` is Lipschitz in time near `a`,
with a constant that depends on the scale `r` and, for `β < 1`, blows up as `r → 0`.

For `0 < a`, `0 < b` and `β ≤ 1`, the mean value inequality gives the bound
`D |b - a| (min a b) ^ (β - 1)` from a derivative of norm at most `D r ^ (β - 1)` at every `r`
between `a` and `b`. Here `β` may be negative, and no Hölder hypothesis is involved.

The two other cases need no derivative, only data at the two endpoints, so they are stated for
two points `x` and `y` of a pseudometric space, the values of `u` at `b` and `a`. For `a < 0`,
`0 ≤ β ≤ 1` and `0 ≤ K`, the data are that `dist x y` vanishes if `b ≤ 0` and is at most `K b ^ β`
if `0 < b`. For `0 < a` and `a ≤ A |b - a|`, they are that `x` and `y` both lie within `K a ^ β`
of a point `c`.

Hölder-in-time estimates are an application of these bounds, not a premise. A function `u` equal
to `c` on `(-∞, 0]` with `dist (u r) c ≤ K r ^ β` for `r ≥ 0`, such as one that is `β`-Hölder at
time `0`, supplies, at `x = u b` and `y = u a`, the endpoint data of the first estimate for every
`β`, and of the second when `0 ≤ β` and `b ≤ a`, so that `b ^ β ≤ a ^ β` for `0 < b`. The data
alone do not give the first estimate: it still requires `0 ≤ β ≤ 1` and `0 ≤ K`.

## Main results

* `TauCeti.norm_sub_le_mul_abs_sub_mul_rpow_of_hasDerivWithinAt`:
  `‖u b - u a‖ ≤ D |b - a| (min a b) ^ (β - 1)` for `0 < a`, `0 < b` and `β ≤ 1` when
  `u` has derivative `u' r` within `[[a, b]]` with `‖u' r‖ ≤ D r ^ (β - 1)` at every
  `r ∈ [[a, b]]`.
* `TauCeti.dist_le_mul_abs_sub_mul_rpow_of_neg_right`: `dist x y ≤ K |b - a| (-a) ^ (β - 1)`
  for `a < 0`, `0 ≤ β ≤ 1` and `0 ≤ K`, when `dist x y = 0` if `b ≤ 0` and
  `dist x y ≤ K b ^ β` if `0 < b`.
* `TauCeti.dist_le_mul_abs_sub_mul_rpow_of_le_mul_abs_sub`:
  `dist x y ≤ 2 A K |b - a| a ^ (β - 1)` for `0 < a` and `a ≤ A |b - a|`, when
  `dist x c ≤ K a ^ β` and `dist y c ≤ K a ^ β`.
-/

public section

namespace TauCeti

open Real Set

/-- Mean value bound at positive times: if `0 < a`, `0 < b`, `β ≤ 1` and `u` has derivative
`f' r` within `[[a, b]]` of norm at most `D r^(β - 1)` at every `r ∈ [[a, b]]`, then
`‖u b - u a‖ ≤ D |b - a| (min a b)^(β - 1)`. -/
theorem norm_sub_le_mul_abs_sub_mul_rpow_of_hasDerivWithinAt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {u f' : ℝ → F} {β D a b : ℝ} (hβ : β ≤ 1) (ha : 0 < a) (hb : 0 < b)
    (hderiv : ∀ r ∈ uIcc a b, HasDerivWithinAt u (f' r) (uIcc a b) r)
    (hbound : ∀ r ∈ uIcc a b, ‖f' r‖ ≤ D * r ^ (β - 1)) :
    ‖u b - u a‖ ≤ D * (|b - a| * min a b ^ (β - 1)) := by
  have hm : 0 < min a b := lt_min ha hb
  have hD : 0 ≤ D := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hbound a left_mem_uIcc))
    (rpow_pos_of_pos ha _)
  have hmv := (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le (f := u)
    (f' := f') (C := D * min a b ^ (β - 1)) hderiv
    (fun r hr => (hbound r hr).trans
      (mul_le_mul_of_nonneg_left (rpow_le_rpow_of_nonpos hm hr.1 (by linarith)) hD))
    left_mem_uIcc right_mem_uIcc
  rw [Real.norm_eq_abs] at hmv
  exact hmv.trans_eq (by ring)

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

/-- If `0 < a` and `a ≤ A |b - a|`, and `x` and `y` both lie within `K a ^ β` of a point `c`,
then `dist x y ≤ 2 A K |b - a| a ^ (β - 1)`. This bounds the increment `dist (u b) (u a)` of a
function `u` that is constant equal to `c` on `(-∞, 0]` with `dist (u r) c ≤ K r ^ β` for
`r ≥ 0`, when `0 ≤ β` and `b ≤ a`; for instance, `b ≤ a / 2` gives `a ≤ 2 |b - a|`. -/
theorem dist_le_mul_abs_sub_mul_rpow_of_le_mul_abs_sub {X : Type*} [PseudoMetricSpace X]
    {x y c : X} {β K A a b : ℝ} (ha : 0 < a) (hab : a ≤ A * |b - a|) (hx : dist x c ≤ K * a ^ β)
    (hy : dist y c ≤ K * a ^ β) :
    dist x y ≤ 2 * A * K * (|b - a| * a ^ (β - 1)) := by
  have hK : 0 ≤ K :=
    nonneg_of_mul_nonneg_left (dist_nonneg.trans hx) (rpow_pos_of_pos ha β)
  have h3 : a ^ β ≤ A * (|b - a| * a ^ (β - 1)) :=
    calc a ^ β = a * a ^ (β - 1) := by
          simpa only [sub_add_cancel, mul_comm] using rpow_add_one ha.ne' (β - 1)
      _ ≤ A * |b - a| * a ^ (β - 1) := by gcongr
      _ = A * (|b - a| * a ^ (β - 1)) := mul_assoc _ _ _
  calc dist x y ≤ dist x c + dist y c := dist_triangle_right _ _ _
    _ ≤ 2 * (K * a ^ β) := by linarith
    _ ≤ 2 * (K * (A * (|b - a| * a ^ (β - 1)))) := by gcongr
    _ = _ := by ring

end TauCeti
