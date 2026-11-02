/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scharmberg, The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.AlgebraicTopology.EilenbergSteenrod

/-!
# The exactness, additivity and dimension axioms for homology pretheories

Mathlib's `TopPair.HomologyPretheory` bundles relative homology functors `Hₚ i`, absolute
homology functors `H i`, their comparison on pairs `(X, ∅)` and boundary morphisms
`δ i j : Hₚ i ⟶ proj₂ ⋙ H j`, and states homotopy invariance as the class
`HomologyPretheory.IsHomotopyInvariant`. This file adds three further Eilenberg--Steenrod axioms
as classes on a homology pretheory:

* `HomologyPretheory.HasPairSequence`: for every topological pair `(X, A)` the sequence
  `⋯ ⟶ Hᵢ(A) ⟶ Hᵢ(X) ⟶ Hᵢ(X, A) ⟶ Hⱼ(A) ⟶ Hⱼ(X) ⟶ ⋯` (for `c.Rel i j`) is exact, and the
  map `Hᵢ(X) ⟶ Hᵢ(X, A)` is an epimorphism when `i` has no successor in the complex shape.
* `HomologyPretheory.IsAdditive`: every absolute homology functor `H i` preserves coproducts of
  families of spaces, so the homology of a disjoint union is the coproduct of the homologies of
  its summands, with the maps induced by the inclusions of the summands as the coprojections.
* `HomologyPretheory.HasDimensionAxiom`: for the complex shape `ComplexShape.down ℕ`, the
  homology of a point vanishes in every positive degree.

The map `Hᵢ(X) ⟶ Hᵢ(X, A)` of the pair sequence is `HomologyPretheory.hFstToHₚ`, the comparison
`H i ≅ incl ⋙ Hₚ i` followed by the map induced by the pair map `(X, ∅) ⟶ (X, A)`. It is natural
in the pair (`HomologyPretheory.hFstToHₚ_naturality`) and commutes with morphisms of pretheories
(`HomologyPretheory.Hom.hFstToHₚ_comm`). Under the pair-sequence axiom, the relative homology of a
pair `(A, A)` vanishes (`HomologyPretheory.isZero_Hₚ_diag`).

## References

* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Chapter I.
* J. Scharmberg, [mathlib4#38369](https://github.com/leanprover-community/mathlib4/pull/38369):
  `hFstToHₚ`, `HasPairSequence`, `IsAdditive` and `HasDimensionAxiom` are adapted from this
  formalization.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace TopPair.HomologyPretheory

section

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
  (HP : HomologyPretheory.{u} C c)

/-- The map `H i X.fst ⟶ Hₚ i X` from the homology of the ambient space of a pair to the
relative homology of the pair, induced by the pair map `(X.fst, ∅) ⟶ X`. -/
@[no_expose]
def hFstToHₚ (i : ι) (X : TopPair.{u}) : (HP.H i).obj X.fst ⟶ (HP.Hₚ i).obj X :=
  (HP.iso i).hom.app _ ≫ (HP.Hₚ i).map X.j

/-- The ambient-to-relative map is the comparison on `(X.fst, ∅)` followed by the map induced
by the pair inclusion `(X.fst, ∅) ⟶ X`. -/
lemma hFstToHₚ_def (i : ι) (X : TopPair.{u}) :
    HP.hFstToHₚ i X = (HP.iso i).hom.app X.fst ≫ (HP.Hₚ i).map X.j := by
  rw [hFstToHₚ.eq_def]

/-- The map `Hᵢ(X) ⟶ Hᵢ(X, A)` is natural in the pair `(X, A)`. -/
@[reassoc (attr := simp)]
lemma hFstToHₚ_naturality {X Y : TopPair.{u}} (f : X ⟶ Y) (i : ι) :
    HP.hFstToHₚ i X ≫ (HP.Hₚ i).map f = (HP.H i).map (Hom.fst f) ≫ HP.hFstToHₚ i Y := by
  have h : X.j ≫ f = incl.map (Hom.fst f) ≫ Y.j :=
    MorphismProperty.Arrow.Hom.ext (TopCat.isInitialPEmpty.hom_ext _ _) (by cat_disch)
  rw [hFstToHₚ_def, hFstToHₚ_def, Category.assoc, ← Functor.map_comp, h, Functor.map_comp]
  exact ((HP.iso i).hom.naturality_assoc (Hom.fst f) _).symm

/-- A morphism of homology pretheories commutes with the maps `Hᵢ(X) ⟶ Hᵢ(X, A)`. -/
@[reassoc (attr := simp)]
lemma Hom.hFstToHₚ_comm {HP' : HomologyPretheory.{u} C c} (f : HP ⟶ HP') (i : ι)
    (X : TopPair.{u}) :
    HP.hFstToHₚ i X ≫ (f.homₚ i).app X = (f.hom i).app X.fst ≫ HP'.hFstToHₚ i X := by
  rw [hFstToHₚ_def, hFstToHₚ_def, Category.assoc, (f.homₚ i).naturality, ← Category.assoc]
  exact (Hom.iso_comm_app f i X.fst =≫ _).trans (Category.assoc _ _ _)

/-- A homology pretheory has the long exact sequence of topological pairs
`⋯ ⟶ H i X.snd ⟶ H i X.fst ⟶ Hₚ i X ⟶ H j X.snd ⟶ H j X.fst ⟶ ⋯` for `c.Rel i j`. -/
class HasPairSequence : Prop where
  /-- Exactness of the sequence `H i X.fst ⟶ Hₚ i X ⟶ H j X.snd`. -/
  exact_pair (X : TopPair.{u}) (i j : ι) (hij : c.Rel i j) :
    (ComposableArrows.mk₂ (HP.hFstToHₚ i X) ((HP.δ i j).app X)).Exact
  /-- Exactness of the sequence `Hₚ i X ⟶ H j X.snd ⟶ H j X.fst`. -/
  exact_snd (X : TopPair.{u}) (i j : ι) (hij : c.Rel i j) :
    (ComposableArrows.mk₂ ((HP.δ i j).app X) ((HP.H j).map X.map)).Exact
  /-- Exactness of the sequence `H i X.snd ⟶ H i X.fst ⟶ Hₚ i X`. -/
  exact_fst (X : TopPair.{u}) (i : ι) :
    (ComposableArrows.mk₂ ((HP.H i).map X.map) (HP.hFstToHₚ i X)).Exact
  /-- The map on relative homology induced by the pair inclusion `(X.fst, ∅) ⟶ X` is an
  epimorphism when `i` has no successor in the complex shape, where the long exact sequence ends.
  Composing it with `HP.iso` gives the epimorphism `HP.hFstToHₚ i X`. -/
  epi_map_of_not_rel (X : TopPair.{u}) (i : ι) (hi : ∀ j : ι, ¬ c.Rel i j) :
    Epi ((HP.Hₚ i).map X.j)

export HasPairSequence (exact_pair exact_snd exact_fst)

/-- When `i` has no successor in the complex shape, the map `Hᵢ(X) ⟶ Hᵢ(X, A)` of a pretheory
with the long exact sequence of pairs is an epimorphism. -/
lemma epi_hFstToHₚ_of_not_rel [HP.HasPairSequence] (i : ι) (hi : ∀ j, ¬ c.Rel i j)
    (X : TopPair.{u}) : Epi (HP.hFstToHₚ i X) := by
  have := HasPairSequence.epi_map_of_not_rel (HP := HP) X i hi
  rw [hFstToHₚ_def]
  infer_instance

/-- A homology pretheory is additive if each of its absolute homology functors preserves
coproducts of families of spaces indexed by a type in the universe of the spaces. -/
class IsAdditive : Prop where
  /-- The absolute homology functor `H i` preserves coproducts indexed by `J`. -/
  preservesColimitsOfShape_discrete (J : Type u) (i : ι) :
    PreservesColimitsOfShape (Discrete J) (HP.H i)

attribute [instance] IsAdditive.preservesColimitsOfShape_discrete

/-- A homology pretheory indexed by `ComplexShape.down ℕ` has the dimension axiom if the
homology of a point vanishes in every positive degree. -/
class HasDimensionAxiom (HP : HomologyPretheory.{u} C (ComplexShape.down ℕ)) : Prop where
  isZero_PUnit_of_gt_zero (n : ℕ) (hn : n ≠ 0) : IsZero ((HP.H n).obj (TopCat.of PUnit))

export HasDimensionAxiom (isZero_PUnit_of_gt_zero)

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
