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
the last two a real minuend.

## Main results

* `EReal.iInf_sub_coe` and `EReal.iSup_sub_coe` — subtracting a real constant commutes with an
  infimum and with a supremum in `EReal`;
* `EReal.coe_sub_add_coe` — subtracting a sum whose final term is real can be reassociated when
  the minuend is real;
* `EReal.coe_sub_le_comm` — the two subtrahends of a real minuend can be exchanged across an
  inequality, as in `sub_le_comm` for groups.
-/

public section

noncomputable section

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

end TauCeti

end

end
