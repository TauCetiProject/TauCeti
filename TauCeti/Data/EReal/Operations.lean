/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.EReal.Operations

/-!
# Operations on extended real numbers

This file supplements Mathlib's API for arithmetic operations on `EReal`. The common theme is
subtraction in which one operand is a *real* number: both `a - (r : EReal)` and `(r : EReal) - a`
are defined for every extended real `a`, are never of the form `∞ - ∞`, and behave like real
subtraction in the ways recorded here. The first two results below have a real subtrahend and
the last two a real minuend. The file also records that adding a finite extended nonnegative real
to a real number is real addition.

## Main results

* `EReal.iInf_sub_coe` and `EReal.iSup_sub_coe` — subtracting a real constant commutes with an
  infimum and with a supremum in `EReal`;
* `EReal.coe_sub_add_coe` — subtracting a sum whose final term is real can be reassociated when
  the minuend is real;
* `EReal.coe_sub_le_comm` — the two subtrahends of a real minuend can be exchanged across an
  inequality, as in `sub_le_comm` for groups;
* `EReal.neg_sub_coe` and `EReal.neg_coe_sub` — negating a difference with one real operand
  exchanges the operands, with no finiteness hypothesis on the other;
* `EReal.sub_sub_coe_eq_add_coe_sub` and `EReal.sub_coe_add_eq_add_sub` — a real subtrahend
  moves freely through sums and differences, as in `sub_sub_eq_add_sub` and `sub_add_eq_add_sub`
  for groups;
* `EReal.sub_coe_eq_iff_eq_add_coe` — a real subtrahend can be moved across an equation, as in
  `sub_eq_iff_eq_add` for groups;
* `EReal.add_eq_coe_iff_neg_add_neg_eq` — an equation between a sum and a real number can be
  negated term by term;
* `EReal.coe_le_coe_add_coe_ennreal_iff` — an inequality `x ≤ y + I` with `x`, `y` real and `I` a
  finite extended nonnegative real is the corresponding inequality between reals.
* `EReal.coe_add_coe_ennreal_le_coe_add_coe_ennreal_iff` — likewise for an inequality
  `x + I ≤ y + J` with `I`, `J` finite extended nonnegative reals.
-/

public section

noncomputable section

open scoped ENNReal

namespace TauCeti

/-- Subtracting a real constant commutes with an infimum in `EReal`; both sides are `⊤` when the
index type is empty. -/
theorem _root_.EReal.iInf_sub_coe {ι : Sort*} (f : ι → EReal) (a : ℝ) :
    (⨅ i, (f i - (a : EReal))) = (⨅ i, f i) - (a : EReal) := by
  refine le_antisymm ?_ (le_iInf fun i => EReal.sub_le_sub (iInf_le f i) le_rfl)
  rw [EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot a)) (.inl (EReal.coe_ne_top a))]
  exact le_iInf fun i => EReal.add_le_of_le_sub (iInf_le _ i)

/-- Subtracting a real constant commutes with a supremum in `EReal`; both sides are `⊥` when the
index type is empty. -/
theorem _root_.EReal.iSup_sub_coe {ι : Sort*} (f : ι → EReal) (a : ℝ) :
    (⨆ i, (f i - (a : EReal))) = (⨆ i, f i) - (a : EReal) := by
  refine le_antisymm (iSup_le fun i => EReal.sub_le_sub (le_iSup f i) le_rfl) ?_
  rw [EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot a)) (.inl (EReal.coe_ne_top a))]
  exact iSup_le fun i =>
    (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot a)) (.inl (EReal.coe_ne_top a))).1
      (le_iSup (fun i => f i - (a : EReal)) i)

/-- Subtracting a sum whose final term is real can be reassociated when the minuend is real. -/
theorem _root_.EReal.coe_sub_add_coe (b : EReal) (d a : ℝ) :
    (d : EReal) - (b + (a : EReal)) = (d : EReal) - b - (a : EReal) := by
  induction b with
  | bot => simp
  | coe b => norm_cast; ring
  | top => simp

/-- With a real minuend, the subtrahend and the right-hand side of an inequality can be
exchanged: `r - a ≤ b ↔ r - b ≤ a`. This is `sub_le_comm` for `EReal`, and it holds with no
finiteness hypothesis on `a` or `b`. -/
theorem _root_.EReal.coe_sub_le_comm {r : ℝ} {a b : EReal} :
    (r : EReal) - a ≤ b ↔ (r : EReal) - b ≤ a := by
  induction a <;> induction b <;> simp [← EReal.coe_sub, add_comm]

/-- Negating a difference with a real subtrahend exchanges the operands, for every extended-real
minuend. -/
theorem _root_.EReal.neg_sub_coe (b : EReal) (r : ℝ) : -(b - (r : EReal)) = (r : EReal) - b := by
  rw [EReal.neg_sub (.inr (EReal.coe_ne_bot r)) (.inr (EReal.coe_ne_top r)), add_comm,
    sub_eq_add_neg]

/-- Negating a difference with a real minuend exchanges the operands, for every extended-real
subtrahend. -/
theorem _root_.EReal.neg_coe_sub (r : ℝ) (b : EReal) : -((r : EReal) - b) = b - (r : EReal) := by
  rw [← EReal.neg_sub_coe, neg_neg]

/-- A real subtrahend inside a subtrahend can be pulled out as a summand, for all extended-real
`x` and `y`: this is `sub_sub_eq_add_sub` for `EReal`, with no finiteness hypothesis. -/
theorem _root_.EReal.sub_sub_coe_eq_add_coe_sub (x y : EReal) (a : ℝ) :
    x - (y - (a : EReal)) = x + (a : EReal) - y := by
  rw [sub_eq_add_neg x, EReal.neg_sub_coe, sub_eq_add_neg, ← add_assoc, ← sub_eq_add_neg]

/-- A real subtrahend commutes past a summand, for all extended-real `x` and `y`: this is
`sub_add_eq_add_sub` for `EReal`, with no finiteness hypothesis. -/
theorem _root_.EReal.sub_coe_add_eq_add_sub (x y : EReal) (a : ℝ) :
    x - (a : EReal) + y = x + y - (a : EReal) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_right_comm]

/-- A real subtrahend can be moved across an equation in `EReal`, for all extended-real `x` and
`y`: this is `sub_eq_iff_eq_add` for `EReal`, with no finiteness hypothesis. -/
theorem _root_.EReal.sub_coe_eq_iff_eq_add_coe {x y : EReal} {a : ℝ} :
    x - (a : EReal) = y ↔ x = y + (a : EReal) :=
  ⟨fun h => by rw [← h, EReal.sub_add_cancel], fun h => by rw [h, EReal.add_sub_cancel_right]⟩

/-- An equation between a sum of extended reals and a real number can be negated term by term.
Both sides force `x` and `y` to be real, so no finiteness hypothesis is needed, even though
`-(x + y) = -x + -y` fails in `EReal` when `x` and `y` are opposite infinities. -/
theorem _root_.EReal.add_eq_coe_iff_neg_add_neg_eq {x y : EReal} {r : ℝ} :
    x + y = (r : EReal) ↔ -x + -y = ((-r : ℝ) : EReal) := by
  induction x <;> induction y <;> simp [← EReal.coe_add, ← EReal.coe_neg, ← neg_add, -neg_add_rev]

/-- Adding a finite `I : ℝ≥0∞` to a real number in `EReal` is real addition: the inequality
`x ≤ y + I` between extended reals is `x ≤ y + I.toReal` between reals. -/
theorem _root_.EReal.coe_le_coe_add_coe_ennreal_iff {x y : ℝ} {I : ℝ≥0∞} (hI : I ≠ ∞) :
    (x : EReal) ≤ y + I ↔ x ≤ y + I.toReal := by
  rw [← EReal.coe_ennreal_toReal hI, ← EReal.coe_add, EReal.coe_le_coe_iff]

/-- Adding finite elements of `ℝ≥0∞` to real numbers in `EReal` is real addition: the inequality
`x + I ≤ y + J` between extended reals is `x + I.toReal ≤ y + J.toReal` between reals. -/
theorem _root_.EReal.coe_add_coe_ennreal_le_coe_add_coe_ennreal_iff {x y : ℝ} {I J : ℝ≥0∞}
    (hI : I ≠ ∞) (hJ : J ≠ ∞) :
    (x : EReal) + I ≤ y + J ↔ x + I.toReal ≤ y + J.toReal := by
  rw [← EReal.coe_ennreal_toReal hI, ← EReal.coe_ennreal_toReal hJ, ← EReal.coe_add,
    ← EReal.coe_add, EReal.coe_le_coe_iff]

end TauCeti

end

end
