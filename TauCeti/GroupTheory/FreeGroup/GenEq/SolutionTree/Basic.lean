/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.CoordGroup
public import TauCeti.GroupTheory.FreeGroup.GenEq.Parametric
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Terminal parametric generalised equations and automorphisms of the active part

The solution tree of a parametric generalised equation `Ω` (Kharlampovich–Myasnikov, §5.6)
transforms the active and non-active part of `Ω` until only parametric sections and the constant
part remain, the constant part lying in no variable base, so that it is made of items carrying a
constant base and of free items; such an equation is *terminal*
(`TauCeti.ParamGenEq.IsTerminal`).

Along the tree, solutions are transformed by groups of canonical automorphisms of the coordinate
groups, which fix all variables in the non-active part (§5.6 of the source): the items of the
non-active, parametric and constant sections. The automorphisms of the coordinate group fixing the
coefficients and these items form the group `TauCeti.ParamGenEq.activeAut`; every group of
canonical automorphisms of `Ω` is a subgroup of it.

## Main definitions

* `TauCeti.ParamGenEq.IsTerminal`: every item is parametric, or lies in the constant part and in
  no variable base, decidable.
* `TauCeti.ParamGenEq.activeAut`: the automorphisms of the coordinate group fixing the coefficients
  and the items outside the active sections.

## Main results

* `TauCeti.ParamGenEq.apply_item_of_mem_activeAut`: the automorphisms of `activeAut` fix the
  parametric items.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.6.
-/

public section

namespace TauCeti

open GroupAlgGeom Monoid.Coprod

namespace ParamGenEq

variable {A : Type*} (Ω : ParamGenEq A)

/-- A parametric generalised equation is terminal when there are no active and no non-active
sections, and no item of the constant part lies in a variable base; every item of the constant
part is then constant (carries a constant base) or free. -/
def IsTerminal : Prop :=
  ∀ k, Ω.partition.itemKind k = .parametric ∨
    (Ω.partition.itemKind k = .constant ∧ ∀ μ, k ∉ Ω.baseItems μ)

theorem isTerminal_iff : Ω.IsTerminal ↔ ∀ k, Ω.partition.itemKind k = .parametric ∨
    (Ω.partition.itemKind k = .constant ∧ ∀ μ, k ∉ Ω.baseItems μ) :=
  Iff.rfl

-- Decided through the boundaries of the bases, so that `decide` evaluates it.
instance : Decidable Ω.IsTerminal :=
  decidable_of_iff (∀ k, Ω.partition.itemKind k = .parametric ∨
    (Ω.partition.itemKind k = .constant ∧ ∀ μ, ¬ ((Ω.left μ : ℕ) ≤ k ∧ (k : ℕ) < Ω.right μ)))
    (by simp [isTerminal_iff])

/-- The automorphisms of the coordinate group `F_{R(Ω)}` fixing the coefficients and every item
outside the active sections, that is, every variable of the non-active part. -/
def activeAut : Subgroup (MulAut Ω.coordGroup) :=
  fixingSubgroup (MulAut Ω.coordGroup)
    (Set.range (CoordGroup.coeff (MonoidHom.id (FreeGroup A)) Ω.toSystem) ∪
      Ω.item '' {k | Ω.partition.itemKind k ≠ .active})

variable {Ω} in
theorem mem_activeAut_iff {σ : MulAut Ω.coordGroup} : σ ∈ Ω.activeAut ↔
    (∀ g, σ (CoordGroup.coeff (MonoidHom.id (FreeGroup A)) Ω.toSystem g) =
      CoordGroup.coeff (MonoidHom.id (FreeGroup A)) Ω.toSystem g) ∧
      ∀ k, Ω.partition.itemKind k ≠ .active → σ (Ω.item k) = Ω.item k := by
  simp [activeAut, mem_fixingSubgroup_iff, or_imp, forall_and]

variable {Ω} in
/-- An automorphism of the coordinate group fixing the coefficients and the items outside the
active sections fixes the parametric items. -/
theorem apply_item_of_mem_activeAut {σ : MulAut Ω.coordGroup} (hσ : σ ∈ Ω.activeAut)
    {k : Fin Ω.numItems} (hk : Ω.IsParamItem k) : σ (Ω.item k) = Ω.item k :=
  (mem_activeAut_iff.1 hσ).2 k (by simp [(Ω.isParamItem_iff).1 hk])

end ParamGenEq

end TauCeti
