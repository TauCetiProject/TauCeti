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
# Removing left summands from a sum type

For `a : α`, the elements of `α ⊕ β` other than `Sum.inl a` are the disjoint union of the
elements of `α` other than `a` and of `β`. This file records this equivalence,
`Equiv.sumSubtypeNe`, which identifies the columns left after deleting the column `Sum.inl a` of a
matrix whose columns are indexed by `α ⊕ β`.

Similarly, if `e : α ≃ β ⊕ γ`, the elements of `α` outside the image of `β` are identified with
`γ` (`Equiv.complRangeSymmInl`). This counts the new elements when `α` is presented as an old part
`β` together with new elements indexed by `γ`, as for the cells of a CW complex built from a
subcomplex by attaching cells.
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

/-- For `e : α ≃ β ⊕ γ`, the elements of `α` outside the image of `β` correspond to `γ`, through
`e`. -/
def complRangeSymmInl {α β γ : Type*} (e : α ≃ β ⊕ γ) : ↥(Set.range (e.symm ∘ Sum.inl))ᶜ ≃ γ :=
  (e.subtypeEquiv fun x ↦ not_congr
    ⟨fun ⟨b, hb⟩ ↦ ⟨b, by rw [← hb, Function.comp_apply, Equiv.apply_symm_apply]⟩,
      fun ⟨b, hb⟩ ↦ ⟨b, by rw [Function.comp_apply, hb, Equiv.symm_apply_apply]⟩⟩).trans <|
    (Set.equivOfEq Set.compl_range_inl).trans (Equiv.Set.rangeInr _ _)

/-- `Equiv.complRangeSymmInl e x` is the `γ`-component of `e x`. -/
@[simp]
theorem inr_complRangeSymmInl_apply {α β γ : Type*} (e : α ≃ β ⊕ γ)
    (x : ↥(Set.range (e.symm ∘ Sum.inl))ᶜ) : Sum.inr (e.complRangeSymmInl x) = e x := by
  rcases hex : e x with b | c
  · exact absurd ⟨b, by rw [Function.comp_apply, ← hex, Equiv.symm_apply_apply]⟩ x.2
  · simp [complRangeSymmInl, Equiv.Set.rangeInr, hex]

/-- The inverse of `Equiv.complRangeSymmInl e` sends `c` to `e.symm (Sum.inr c)`. -/
@[simp]
theorem coe_complRangeSymmInl_symm_apply {α β γ : Type*} (e : α ≃ β ⊕ γ) (c : γ) :
    (e.complRangeSymmInl.symm c : α) = e.symm (Sum.inr c) :=
  (e.symm_apply_eq.2 (by rw [← inr_complRangeSymmInl_apply, apply_symm_apply])).symm

end Equiv
