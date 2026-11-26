/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Compare

/-!
# Comparisons determined by other comparisons

Two pairs of points of linear orders compare in the same way under `cmp` as soon as `≤` agrees on
them in both directions: `TauCeti.cmp_eq_cmp_of_le_iff_le`. This is the converse of Mathlib's
`le_iff_le_of_cmp_eq_cmp`.

If two points `x` and `z` compare differently with a third point `w`, then the comparison of `x`
with `z` is determined by the two comparisons with `w`: `TauCeti.cmp_eq_cmpOfNe`, where the rule
is the function `TauCeti.cmpOfNe` on `Ordering`.
-/

public section

namespace TauCeti

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- Two pairs of points of linear orders compare in the same way when `≤` agrees in both
directions; the converse of `le_iff_le_of_cmp_eq_cmp`. -/
theorem cmp_eq_cmp_of_le_iff_le {x y : α} {x' y' : β} (h₁ : x ≤ y ↔ x' ≤ y')
    (h₂ : y ≤ x ↔ y' ≤ x') : cmp x y = cmp x' y' := by
  cases h : cmp x' y' <;> grind [cmp_eq_lt_iff, cmp_eq_eq_iff, cmp_eq_gt_iff]

/-- The comparison of `x` with `z` when `x` and `z` compare with a third point `w` as `s₀` and
`s`, with `s ≠ s₀` (see `TauCeti.cmp_eq_cmpOfNe`). Its value at `s = s₀` is the junk value `.eq`.
-/
def cmpOfNe : Ordering → Ordering → Ordering
  | .lt, .eq | .lt, .gt | .eq, .gt => .gt
  | .eq, .lt | .gt, .lt | .gt, .eq => .lt
  | _, _ => .eq

/-! The values of `cmpOfNe` off the diagonal. -/

@[simp] theorem cmpOfNe_lt_eq : cmpOfNe .lt .eq = .gt := (rfl)
@[simp] theorem cmpOfNe_lt_gt : cmpOfNe .lt .gt = .gt := (rfl)
@[simp] theorem cmpOfNe_eq_gt : cmpOfNe .eq .gt = .gt := (rfl)
@[simp] theorem cmpOfNe_eq_lt : cmpOfNe .eq .lt = .lt := (rfl)
@[simp] theorem cmpOfNe_gt_lt : cmpOfNe .gt .lt = .lt := (rfl)
@[simp] theorem cmpOfNe_gt_eq : cmpOfNe .gt .eq = .lt := (rfl)

/-- If `x` and `z` compare differently with `w`, their own comparison is determined by these two
comparisons. -/
theorem cmp_eq_cmpOfNe {w x z : α} (h : cmp w z ≠ cmp w x) :
    cmp x z = cmpOfNe (cmp w x) (cmp w z) := by
  cases hwx : cmp w x <;> cases hwz : cmp w z <;>
    simp_all only [ne_eq, not_true_eq_false, reduceCtorEq, not_false_eq_true, cmp_eq_lt_iff,
      cmp_eq_eq_iff, cmp_eq_gt_iff, cmpOfNe] <;>
    first | exact hwz.trans hwx | exact hwx.trans hwz

end TauCeti
