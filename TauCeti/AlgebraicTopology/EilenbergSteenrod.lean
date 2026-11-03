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
for a diagonal pair `(A, A)` under the pair-sequence axiom.

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
-- `hFstToHₚ` is now an abbreviation; general functor and naturality rules simplify its body.
@[reassoc]
lemma hFstToHₚ_naturality {X Y : TopPair.{u}} (f : X ⟶ Y) (i : ι) :
    HP.hFstToHₚ i X ≫ (HP.Hₚ i).map f = (HP.H i).map (Hom.fst f) ≫ HP.hFstToHₚ i Y := by
  have h : X.j ≫ f = incl.map (Hom.fst f) ≫ Y.j :=
    MorphismProperty.Arrow.Hom.ext (TopCat.isInitialPEmpty.hom_ext _ _) (by cat_disch)
  rw [hFstToHₚ, hFstToHₚ, Category.assoc, ← CategoryTheory.Functor.map_comp, h,
    CategoryTheory.Functor.map_comp]
  exact ((HP.iso i).hom.naturality_assoc (Hom.fst f) _).symm

/-- A morphism of homology pretheories commutes with the maps `Hᵢ(X) ⟶ Hᵢ(X, A)`. -/
@[reassoc]
lemma Hom.hFstToHₚ_comm {HP' : HomologyPretheory.{u} C c} (f : HP ⟶ HP') (i : ι)
    (X : TopPair.{u}) :
    HP.hFstToHₚ i X ≫ (f.homₚ i).app X = (f.hom i).app X.fst ≫ HP'.hFstToHₚ i X := by
  rw [hFstToHₚ, hFstToHₚ, Category.assoc, (f.homₚ i).naturality, ← Category.assoc]
  exact (Hom.iso_comm_app f i X.fst =≫ _).trans (Category.assoc _ _ _)

/-- When `i` has no successor in the complex shape, the map `Hᵢ(X) ⟶ Hᵢ(X, A)` of a pretheory
with the long exact sequence of pairs is an epimorphism. -/
lemma epi_hFstToHₚ_of_not_rel [HP.HasPairSequence] (i : ι) (hi : ∀ j, ¬ c.Rel i j)
    (X : TopPair.{u}) : Epi (HP.hFstToHₚ i X) := by
  have := HasPairSequence.epi_map_of_not_rel (HP := HP) X i hi
  rw [hFstToHₚ]
  infer_instance


end

section Preadditive

variable {C : Type*} [Category* C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
  (HP : HomologyPretheory.{u} C c)

/-- In a homology pretheory with the long exact sequence of pairs, the relative homology of a
pair `(A, A)` vanishes. -/
lemma isZero_Hₚ_diag [HP.HasPairSequence] (i : ι) (A : TopCat.{u}) :
    IsZero ((HP.Hₚ i).obj (diag.obj A)) := by
  -- The map `Hᵢ(A) ⟶ Hᵢ(A, A)` vanishes, since it follows the identity of `Hᵢ(A)`.
  have h₀ : HP.hFstToHₚ i (diag.obj A) = 0 := by
    have h : (HP.H i).map (𝟙 A) ≫ HP.hFstToHₚ i (diag.obj A) = 0 :=
      (HP.exact_fst (diag.obj A) i).toIsComplex.zero 0
    rw [CategoryTheory.Functor.map_id] at h
    exact (Category.id_comp _).symm.trans h
  by_cases hi : ∃ j, c.Rel i j
  · -- The boundary `Hᵢ(A, A) ⟶ Hⱼ(A)` is then a monomorphism, and it vanishes, since it is
    -- followed by the identity of `Hⱼ(A)`.
    obtain ⟨j, hij⟩ := hi
    have hδ : (HP.δ i j).app (diag.obj A) = 0 := by
      have h : (HP.δ i j).app (diag.obj A) ≫ (HP.H j).map (𝟙 _) = 0 :=
        (HP.exact_snd (diag.obj A) i j hij).toIsComplex.zero 0
      rw [CategoryTheory.Functor.map_id] at h
      exact (Category.comp_id _).symm.trans h
    have : Mono ((HP.δ i j).app (diag.obj A)) :=
      ((HP.exact_pair (diag.obj A) i j hij).exact 0).mono_g h₀
    exact IsZero.of_mono_eq_zero _ hδ
  · -- Otherwise `Hᵢ(A) ⟶ Hᵢ(A, A)` is an epimorphism.
    push Not at hi
    have := HP.epi_hFstToHₚ_of_not_rel i hi (diag.obj A)
    exact IsZero.of_epi_eq_zero _ h₀

end Preadditive

end TopPair.HomologyPretheory
