/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.Parametric
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Parametric generalised equations and their coordinate groups

A *parametric generalised equation* (Kharlampovich–Myasnikov, Definition 11) is a generalised
equation `Ω` together with a partition of its closed sections into active, non-active, parametric
and constant sections. We bundle the two as `TauCeti.ParamGenEq`, so that a family of parametric
generalised equations, such as the leaves of a solution tree, carries the partitions along with
the equations.

The solution tree of `Ω` with parameters (§5.6 of the source) transforms the active and
non-active part of `Ω` until only parametric sections and the constant part remain, the constant
part made of items carrying a constant base and of free items; such an equation is *terminal*
(`TauCeti.ParamGenEq.IsTerminal`).

Along the tree, solutions are transformed by groups of canonical automorphisms of the coordinate
groups, which fix all variables in the non-active part (§5.6 of the source): the items of the
non-active, parametric and constant sections. The automorphisms of the coordinate group fixing the
coefficients and these items form the group `TauCeti.ParamGenEq.activeAut`; every group of
canonical automorphisms of `Ω` is a subgroup of it.

Solutions move along the tree through `F(A)`-homomorphisms between coordinate groups
(`TauCeti.GenEq.CoordHom`), and the values of the parameters are recorded as words in the items:
`TauCeti.GenEq.item` is the image of an item in the coordinate group `F_{R(Ω)}` (a coordinate
of its generic point), and `TauCeti.GenEq.wordElem` the image of a word in the items and the
letters of `A`. Under the homomorphism `F_{R(Ω)} → F(A)` of a solution, the image of a word goes
to the element of `F(A)` represented by the word obtained by substituting the words of the
solution for the items (`TauCeti.GenEq.Solution.toHom_wordElem`).

## Main definitions

* `TauCeti.ParamGenEq`: parametric generalised equations.
* `TauCeti.ParamGenEq.IsParamItem`: the parametric items.
* `TauCeti.ParamGenEq.IsTerminal`: every item is parametric, or lies in the constant part and is
  constant or free.
* `TauCeti.ParamGenEq.activeAut`: the automorphisms of the coordinate group fixing the coefficients
  and the items outside the active sections.
* `TauCeti.GenEq.CoordHom`: `F(A)`-homomorphisms between coordinate groups.
* `TauCeti.GenEq.item`, `TauCeti.GenEq.wordElem`: an item, and the value of a word in the items
  and the letters, in the coordinate group.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §4.3 (Definition 11) and §5.6.
-/

public section

namespace TauCeti

open GroupAlgGeom Monoid.Coprod

/-- A parametric generalised equation (Kharlampovich–Myasnikov, Definition 11): a generalised
equation together with a partition of its closed sections into active, non-active, parametric and
constant sections. -/
structure ParamGenEq (A : Type*) extends GenEq A where
  /-- The partition of the closed sections into the four kinds. -/
  partition : toGenEq.SectionPartition

namespace GenEq

variable {A : Type*}

/-- `F(A)`-homomorphisms from the coordinate group of `Ω` to that of `Ω'`. -/
abbrev CoordHom (Ω Ω' : GenEq A) : Type _ :=
  GHom (CoordGroup.coeff (MonoidHom.id (FreeGroup A)) Ω.toSystem)
    (CoordGroup.coeff (MonoidHom.id (FreeGroup A)) Ω'.toSystem)

variable (Ω : GenEq A)

/-- The image of an item in the coordinate group: the coordinate of the generic point of `Ω*`
at that item. -/
abbrev item (k : Fin Ω.numItems) : Ω.coordGroup :=
  CoordGroup.genericPoint (MonoidHom.id (FreeGroup A)) Ω.toSystem k

/-- The value in the coordinate group of a word in the items and the letters of `A`. -/
def wordElem (w : List ((Fin Ω.numItems ⊕ A) × Bool)) : Ω.coordGroup :=
  ((EqIneqSystem.toGX (Fin Ω.numItems) FreeGroup.of (FreeGroup.mk w) :
    GX (FreeGroup A) (Fin Ω.numItems)) : Ω.coordGroup)

@[simp]
theorem wordElem_nil : Ω.wordElem [] = 1 := by
  simp [wordElem, ← FreeGroup.one_eq_mk]

@[simp]
theorem wordElem_append (w₁ w₂ : List ((Fin Ω.numItems ⊕ A) × Bool)) :
    Ω.wordElem (w₁ ++ w₂) = Ω.wordElem w₁ * Ω.wordElem w₂ := by
  simp [wordElem, ← FreeGroup.mul_mk]

@[simp]
theorem wordElem_singleton_inl (k : Fin Ω.numItems) :
    Ω.wordElem [(Sum.inl k, true)] = Ω.item k :=
  (congrArg ((↑) : GX (FreeGroup A) (Fin Ω.numItems) → Ω.coordGroup)
    (EqIneqSystem.toGX_of_inl FreeGroup.of k)).trans (CoordGroup.genericPoint_apply _ k).symm

@[simp]
theorem wordElem_singleton_inr (a : A) : Ω.wordElem [(Sum.inr a, true)] =
    CoordGroup.coeff (MonoidHom.id (FreeGroup A)) Ω.toSystem (FreeGroup.of a) :=
  (congrArg ((↑) : GX (FreeGroup A) (Fin Ω.numItems) → Ω.coordGroup)
    (EqIneqSystem.toGX_of_inr FreeGroup.of a)).trans (CoordGroup.coeff_apply _ _).symm

@[simp]
theorem wordElem_singleton_false (x : Fin Ω.numItems ⊕ A) :
    Ω.wordElem [(x, false)] = (Ω.wordElem [(x, true)])⁻¹ := by
  rw [wordElem, wordElem, ← QuotientGroup.mk_inv, ← map_inv, FreeGroup.inv_mk]
  simp [FreeGroup.invRev]

namespace Solution

variable {Ω} (U : Ω.Solution)

@[simp]
theorem toHom_item (k : Fin Ω.numItems) : U.toHom (Ω.item k) = FreeGroup.mk (U.word k) := by
  rw [item, CoordGroup.genericPoint_apply, U.toHom_inr_of]

/-- The homomorphism of a solution sends the image of a word to the element of `F(A)` represented
by the word obtained by substituting the words of the solution for the items. -/
@[simp]
theorem toHom_wordElem (w : List ((Fin Ω.numItems ⊕ A) × Bool)) :
    U.toHom (Ω.wordElem w) = FreeGroup.mk (FreeGroup.substituteVars U.word w) := by
  simp [wordElem]

end Solution

end GenEq

namespace ParamGenEq

variable {A : Type*} (Ω : ParamGenEq A)

/-- An item is parametric when it lies in a parametric section. -/
def IsParamItem (k : Fin Ω.numItems) : Prop :=
  Ω.partition.itemKind k = .parametric

theorem isParamItem_iff {k : Fin Ω.numItems} :
    Ω.IsParamItem k ↔ Ω.partition.itemKind k = .parametric :=
  Iff.rfl

/-- A parametric generalised equation is terminal when there are no active and no non-active
sections, and every item of the constant part is constant (carries a constant base) or free. -/
def IsTerminal : Prop :=
  ∀ k, Ω.partition.itemKind k = .parametric ∨
    (Ω.partition.itemKind k = .constant ∧ (Ω.IsConstantItem k ∨ Ω.IsFreeItem k))

theorem isTerminal_iff : Ω.IsTerminal ↔ ∀ k, Ω.partition.itemKind k = .parametric ∨
    (Ω.partition.itemKind k = .constant ∧ (Ω.IsConstantItem k ∨ Ω.IsFreeItem k)) :=
  Iff.rfl

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
