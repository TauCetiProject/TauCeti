/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells

/-!
# Attaching no cells

In a category with an initial object, an isomorphism `f : X₁ ⟶ X₂` is obtained by attaching an
empty family of cells (`HomotopicalAlgebra.AttachCells.ofIsIso`): both empty coproducts are the
initial object, and the square formed by its identity and `f` is a pushout because both vertical
maps are isomorphisms. This fills the stages of a relative cell complex at which nothing is
attached, for instance when all cells are attached at a single stage.

## References

* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press,
  1990.
-/

public section

open CategoryTheory Limits

universe w v u

namespace HomotopicalAlgebra.AttachCells

variable {C : Type u} [Category.{v} C] [HasInitial C]
  {α : Type*} {A B : α → C} (g : ∀ a, A a ⟶ B a) {X₁ X₂ : C} (f : X₁ ⟶ X₂) [IsIso f]

/-- An isomorphism is obtained by attaching no cells. -/
noncomputable def ofIsIso : AttachCells.{w} g f where
  ι := PEmpty.{w + 1}
  π := PEmpty.elim
  cofan₁ := Cofan.mk (⊥_ C) fun i ↦ i.elim
  cofan₂ := Cofan.mk (⊥_ C) fun i ↦ i.elim
  isColimit₁ := isColimitChangeEmptyCocone C initialIsInitial _ (Iso.refl _)
  isColimit₂ := isColimitChangeEmptyCocone C initialIsInitial _ (Iso.refl _)
  m := 𝟙 _
  hm i := i.elim
  g₁ := initial.to X₁
  g₂ := initial.to X₂
  -- Both vertical maps, `𝟙 (⊥_ C)` and `f`, are isomorphisms.
  isPushout := IsPushout.of_vert_isIso ⟨initial.hom_ext _ _⟩

/-- No cells are attached in `AttachCells.ofIsIso`. -/
instance : IsEmpty (ofIsIso.{w} g f).ι :=
  ⟨fun i ↦ i.elim⟩

end HomotopicalAlgebra.AttachCells
