/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.SpecialFunctions.Pow.Scaling

/-!
# Increment bounds at the rate of a real power

These are conditional, scale-dependent increment bounds: under their hypotheses, they control the
increment of a function `u` of time between `a` and `b` by a multiple of `|b - a|` times a power
`r ^ (β - 1)` of a time scale `r` set by the endpoints (`a`, `b`, `-a` below). Each bound controls
only the pairs of times that satisfy its hypotheses.

For `0 < a` and `0 < b`, the mean value inequality gives the bound
`D |b - a| max (a ^ (β - 1)) (b ^ (β - 1))` from a derivative of norm at most `D r ^ (β - 1)` at
every `r` between `a` and `b`. Here `β` may be any real number, and no Hölder hypothesis is
involved. The factor is `(min a b) ^ (β - 1)` for `β ≤ 1` and `(max a b) ^ (β - 1)` for `1 ≤ β`.
When the derivative bound holds at every time near a positive time `t`, this estimate makes `u`
Lipschitz on a sufficiently small neighborhood of `t`, and a Lipschitz constant there can be
bounded by a multiple of `D t ^ (β - 1)`. For `β < 1` this bound grows as `t → 0`. It is only an
upper bound on the constant needed, and does not show that the best constant grows.

The two other cases need no derivative, only data at the two endpoints, so they are stated for
two points `x` and `y` of a pseudometric space, the values of `u` at `b` and `a`. For `a < 0`,
`0 ≤ β ≤ 1` and `0 ≤ K`, the data are that `dist x y` vanishes if `b ≤ 0` and is at most `K b ^ β`
if `0 < b`. For `0 < a` and `a ≤ A |b - a|`, they are that `x` and `y` both lie within `K a ^ β`
of a point `c`.

Hölder-in-time estimates are an application of these bounds, not a premise. Let `u` be equal to
`c` on `(-∞, 0]` and satisfy the pointwise power bound `dist (u r) c ≤ K r ^ β` relative to `c`
at every time `r ≥ 0`, not only at times near `0`. Then `x = u b` and `y = u a` supply the endpoint
data of the estimate for `a < 0` for every `β`, and of the estimate for `0 < a` when `0 ≤ β` and
`b ≤ a`, so that `b ^ β ≤ a ^ β` for `0 < b`. The data alone do not give the estimate for `a < 0`:
it still requires `0 ≤ β ≤ 1` and `0 ≤ K`.

## Main results

* `TauCeti.norm_sub_le_mul_abs_sub_mul_rpow_of_hasDerivWithinAt`:
  `‖u b - u a‖ ≤ D |b - a| max (a ^ (β - 1)) (b ^ (β - 1))` for `0 < a` and `0 < b` when
  `u` has derivative `f' r` within `[[a, b]]` with `‖f' r‖ ≤ D r ^ (β - 1)` at every
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

/-- Mean value bound at positive times: if `0 < a`, `0 < b` and `u` has derivative `f' r` within
`[[a, b]]` of norm at most `D r^(β - 1)` at every `r ∈ [[a, b]]`, then
`‖u b - u a‖ ≤ D |b - a| max (a^(β - 1)) (b^(β - 1))`. The exponent `β` is arbitrary: the power
`r^(β - 1)` is monotone in `r > 0`, so its largest value on `[[a, b]]` is at an endpoint. -/
theorem norm_sub_le_mul_abs_sub_mul_rpow_of_hasDerivWithinAt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {u f' : ℝ → F} {β D a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hderiv : ∀ r ∈ uIcc a b, HasDerivWithinAt u (f' r) (uIcc a b) r)
    (hbound : ∀ r ∈ uIcc a b, ‖f' r‖ ≤ D * r ^ (β - 1)) :
    ‖u b - u a‖ ≤ D * (|b - a| * max (a ^ (β - 1)) (b ^ (β - 1))) := by
  have hD : 0 ≤ D := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hbound a left_mem_uIcc))
    (rpow_pos_of_pos ha _)
  -- On `[[a, b]]`, the power `r ^ (β - 1)` is at most its larger endpoint value.
  have hle : ∀ r ∈ uIcc a b, r ^ (β - 1) ≤ max (a ^ (β - 1)) (b ^ (β - 1)) := fun r hr ↦ by
    rcases mem_uIcc.mp hr with ⟨har, hrb⟩ | ⟨hbr, hra⟩
    · simpa only [one_rpow, mul_one] using
        rpow_le_max_mul_rpow ha zero_le_one (by rwa [mul_one]) (by rwa [mul_one]) (β - 1)
    · simpa only [one_rpow, mul_one, max_comm (a ^ (β - 1))] using
        rpow_le_max_mul_rpow hb zero_le_one (by rwa [mul_one]) (by rwa [mul_one]) (β - 1)
  have hmv := (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le (f := u)
    (f' := f') (C := D * max (a ^ (β - 1)) (b ^ (β - 1))) hderiv
    (fun r hr => (hbound r hr).trans (mul_le_mul_of_nonneg_left (hle r hr) hD))
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
      _ ≤ (-a) ^ (β - 1) * (b - a) ^ (1 : ℝ) := by
          simpa only [← rpow_neg_eq_inv_rpow, neg_neg, neg_sub_neg, neg_sub] using
            rpow_le_rpow_sub_mul_rpow (inv_pos.2 (by linarith : 0 < b - a))
              (inv_anti₀ hd (by linarith)) (neg_le_neg (by linarith : β ≤ 1))
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
