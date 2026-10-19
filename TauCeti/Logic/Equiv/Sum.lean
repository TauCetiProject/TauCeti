/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Sum

/-!
# Removing a left summand from a sum type

For `a : α`, the elements of `α ⊕ β` other than `Sum.inl a` are the disjoint union of the
elements of `α` other than `a` and of `β`. This file records this equivalence,
`Equiv.sumSubtypeNe`, which identifies the columns left after deleting the column `Sum.inl a` of a
matrix whose columns are indexed by `α ⊕ β`.
-/

public section

namespace Equiv

/-- The disjoint union of the elements other than `a` and of `β`, as the subtype of `α ⊕ β` of the
elements other than `Sum.inl a`. -/
def sumSubtypeNe {α β : Type*} (a : α) : ({x // x ≠ a} ⊕ β) ≃ {j : α ⊕ β // j ≠ Sum.inl a} :=
  ((Equiv.subtypeSum (p := (· ≠ Sum.inl a))).trans (Equiv.sumCongr
    (Equiv.subtypeEquivRight fun _ ↦ Sum.inl.inj_iff.not)
    (Equiv.subtypeUnivEquiv fun _ ↦ Sum.inr_ne_inl))).symm

/-- `Equiv.sumSubtypeNe a` sends `Sum.inl x` to `Sum.inl x` and `Sum.inr y` to `Sum.inr y`. -/
@[simp]
theorem coe_sumSubtypeNe_apply {α β : Type*} (a : α) (x : {x // x ≠ a} ⊕ β) :
    (sumSubtypeNe a x : α ⊕ β) = Sum.map Subtype.val id x := by
  rcases x with x | y <;> simp [sumSubtypeNe, Equiv.subtypeSum]

end Equiv
