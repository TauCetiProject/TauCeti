/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
public import Mathlib.CategoryTheory.ConcreteCategory.Basic

/-!
# Gluing sections of sheaves on disjoint opens

Sections of a sheaf with values in a concrete category on two disjoint open sets glue to a section
on their union, provided the forgetful functor preserves binary products. There is no compatibility
condition on the intersection: the sections over the empty open form a terminal object, so the
sections over the union form the binary product of those over the two opens, and the forgetful
functor sends this product to the product of the underlying types. The hypothesis holds in
particular for sheaves of commutative rings.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace

universe w

namespace TopCat.Sheaf

variable {X : TopCat.{w}}

/-- Sections of a sheaf with values in a concrete category on two disjoint opens glue to a section
on their union, assuming that the forgetful functor preserves binary products. -/
theorem exists_section_sup_of_disjoint {C : Type*} [Category* C] {FC : C → C → Type*}
    {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [PreservesLimitsOfShape (Discrete WalkingPair) (CategoryTheory.forget C)]
    (F : X.Sheaf C) {A B : Opens X} (hAB : Disjoint A B) (σ : ToType (F.obj.obj (op A)))
    (ρ : ToType (F.obj.obj (op B))) :
    ∃ τ : ToType (F.obj.obj (op (A ⊔ B))),
      F.obj.map (homOfLE le_sup_left).op τ = σ ∧ F.obj.map (homOfLE le_sup_right).op τ = ρ := by
  have hprod := F.isProductOfDisjoint A B hAB.eq_bot
  have hl := mapIsLimitOfPreservesOfIsLimit (CategoryTheory.forget C) _ _ hprod
  have h₁ := BinaryFan.IsLimit.lift_fst hl (↾fun _ : PUnit => σ) (↾fun _ : PUnit => ρ)
  have h₂ := BinaryFan.IsLimit.lift_snd hl (↾fun _ : PUnit => σ) (↾fun _ : PUnit => ρ)
  exact ⟨BinaryFan.IsLimit.lift hl (↾fun _ : PUnit => σ) (↾fun _ : PUnit => ρ) PUnit.unit,
    ConcreteCategory.congr_hom h₁ PUnit.unit, ConcreteCategory.congr_hom h₂ PUnit.unit⟩

end TopCat.Sheaf
