/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scharmberg, The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.AlgebraicTopology.EilenbergSteenrod

/-!
# Maps and vanishing for homology pretheories

Mathlib supplies the exactness, additivity and dimension axioms for homology
pretheories. This file proves naturality of the ambient-to-relative map, its
compatibility with morphisms of pretheories, and vanishing of relative homology
of a pair `(X, A)` whose inclusion `A ⟶ X` is an isomorphism (for instance a diagonal pair
`(A, A)`) under the pair-sequence axiom.

## References

* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Chapter I.
* J. Scharmberg, [mathlib4#38369](https://github.com/leanprover-community/mathlib4/pull/38369),
  the homology-pretheory interfaces now provided by Mathlib.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace TopPair.HomologyPretheory

section

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
  (HP : HomologyPretheory.{u} C c)

/-- The map `Hᵢ(X) ⟶ Hᵢ(X, A)` is natural in the pair `(X, A)`. -/
@[reassoc]
lemma hFstToHₚ_naturality {X Y : TopPair.{u}} (f : X ⟶ Y) (i : ι) :
    HP.hFstToHₚ i X ≫ (HP.Hₚ i).map f = (HP.H i).map (Hom.fst f) ≫ HP.hFstToHₚ i Y := by
  have h : X.j ≫ f = incl.map (Hom.fst f) ≫ Y.j :=
    MorphismProperty.Arrow.Hom.ext (TopCat.isInitialPEmpty.hom_ext _ _) (by cat_disch)
  simp [← CategoryTheory.Functor.map_comp, h]

/-- A morphism of homology pretheories commutes with the maps `Hᵢ(X) ⟶ Hᵢ(X, A)`. -/
@[reassoc]
lemma Hom.hFstToHₚ_comm {HP' : HomologyPretheory.{u} C c} (f : HP ⟶ HP') (i : ι)
    (X : TopPair.{u}) :
    HP.hFstToHₚ i X ≫ (f.homₚ i).app X = (f.hom i).app X.fst ≫ HP'.hFstToHₚ i X := by
  simp [Hom.iso_comm_app_assoc]

/-- When `i` has no successor in the complex shape, the map `Hᵢ(X) ⟶ Hᵢ(X, A)` of a pretheory
with the long exact sequence of pairs is an epimorphism. -/
lemma epi_hFstToHₚ_of_not_rel [HP.HasPairSequence] (i : ι) (hi : ∀ j, ¬ c.Rel i j)
    (X : TopPair.{u}) : Epi (HP.hFstToHₚ i X) :=
  have := HasPairSequence.epi_map_of_not_rel (HP := HP) X i hi
  epi_comp _ _

end

section Preadditive

variable {C : Type*} [Category* C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
  (HP : HomologyPretheory.{u} C c)

/-- In a homology pretheory with the long exact sequence of pairs, the relative homology of a
pair `(X, A)` whose inclusion `A ⟶ X` is an isomorphism vanishes. -/
lemma isZero_Hₚ_of_isIso_map [HP.HasPairSequence] (i : ι) (X : TopPair.{u}) [IsIso X.map] :
    IsZero ((HP.Hₚ i).obj X) := by
  -- The map `Hᵢ(X) ⟶ Hᵢ(X, A)` vanishes, since it follows the isomorphism `Hᵢ(A) ⟶ Hᵢ(X)`.
  have h₀ : HP.hFstToHₚ i X = 0 := by
    rw [← cancel_epi ((HP.H i).map X.map), comp_zero]
    exact (HP.exact_fst X i).toIsComplex.zero 0
  by_cases hi : ∃ j, c.Rel i j
  · obtain ⟨j, hij⟩ := hi
    -- The boundary `Hᵢ(X, A) ⟶ Hⱼ(A)` vanishes, since it precedes the isomorphism
    -- `Hⱼ(A) ⟶ Hⱼ(X)`; with `h₀`, exactness at `Hᵢ(X, A)` makes that object zero.
    have hδ : (HP.δ i j).app X = 0 :=
      (cancel_mono ((HP.H j).map X.map)).mp
        (((HP.exact_snd X i j hij).toIsComplex.zero 0).trans zero_comp.symm)
    exact ((HP.exact_pair X i j hij).exact 0).isZero_X₂ h₀ hδ
  · -- Otherwise `Hᵢ(X) ⟶ Hᵢ(X, A)` is an epimorphism.
    push Not at hi
    have := HP.epi_hFstToHₚ_of_not_rel i hi X
    exact IsZero.of_epi_eq_zero _ h₀

end Preadditive

end TopPair.HomologyPretheory
