/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Logic.Equiv.Sum

/-!
# Removing a left summand from a sum type

For `a : α`, the elements of `α ⊕ β` other than `Sum.inl a` are the disjoint union of the
elements of `α` other than `a` and of `β`. This file records this equivalence,
`Equiv.sumSubtypeNe`, which identifies the columns left after deleting the column `Sum.inl a` of a
matrix whose columns are indexed by `α ⊕ β`.

Similarly, for an equivalence `e : γ ≃ α ⊕ β`, the elements of `γ` outside the image of `α` are
the elements of `β` (`Equiv.complRangeSymmInl`).
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

/-- For an equivalence `e : γ ≃ α ⊕ β`, the elements of `γ` which do not come from `α` are the
elements of `β`. -/
def complRangeSymmInl {α β γ : Type*} (e : γ ≃ α ⊕ β) : ↥(Set.range (e.symm ∘ Sum.inl))ᶜ ≃ β :=
  (Set.equivOfEq (by rw [Set.range_comp, ← e.symm.image_compl, Set.compl_range_inl])).trans <|
    (e.symm.image _).symm.trans (Equiv.Set.rangeInr α β)

/-- `(Equiv.complRangeSymmInl e).symm` sends `b` to `e.symm (Sum.inr b)`. -/
@[simp]
theorem coe_complRangeSymmInl_symm_apply {α β γ : Type*} (e : γ ≃ α ⊕ β) (b : β) :
    ((complRangeSymmInl e).symm b : γ) = e.symm (Sum.inr b) := by
  simp [complRangeSymmInl]

end Equiv
