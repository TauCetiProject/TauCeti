/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scharmberg, The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.AlgebraicTopology.EilenbergSteenrod

/-!
# The exactness and dimension axioms for homology pretheories

Mathlib's `TopPair.HomologyPretheory` bundles relative homology functors `Hₚ i`, absolute
homology functors `H i`, their comparison on pairs `(X, ∅)` and boundary morphisms
`δ i j : Hₚ i ⟶ proj₂ ⋙ H j`, and states homotopy invariance as the class
`HomologyPretheory.IsHomotopyInvariant`. This file adds two further Eilenberg--Steenrod axioms
as classes on a homology pretheory:

* `HomologyPretheory.HasPairSequence`: for every topological pair `(X, A)` the sequence
  `⋯ ⟶ Hᵢ(A) ⟶ Hᵢ(X) ⟶ Hᵢ(X, A) ⟶ Hⱼ(A) ⟶ Hⱼ(X) ⟶ ⋯` (for `c.Rel i j`) is exact, and the
  map `Hᵢ(X) ⟶ Hᵢ(X, A)` is an epimorphism when `i` has no successor in the complex shape.
* `HomologyPretheory.HasDimensionAxiom`: for the complex shape `ComplexShape.down ℕ`, the
  homology of a point vanishes in every positive degree.

The map `Hᵢ(X) ⟶ Hᵢ(X, A)` of the pair sequence is `HomologyPretheory.hFstToHₚ`, the comparison
`H i ≅ incl ⋙ Hₚ i` followed by the map induced by the pair map `(X, ∅) ⟶ (X, A)`.

## References

* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Chapter I.
* J. Scharmberg, [mathlib4#38369](https://github.com/leanprover-community/mathlib4/pull/38369):
  `hFstToHₚ`, `HasPairSequence` and `HasDimensionAxiom` are adapted from this formalization.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace TopPair.HomologyPretheory

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
  (HP : HomologyPretheory.{u} C c)

/-- The map `H i X.fst ⟶ Hₚ i X` from the homology of the ambient space of a pair to the
relative homology of the pair, induced by the pair map `(X.fst, ∅) ⟶ X`. -/
abbrev hFstToHₚ (i : ι) (X : TopPair.{u}) : (HP.H i).obj X.fst ⟶ (HP.Hₚ i).obj X :=
  (HP.iso i).hom.app _ ≫ (HP.Hₚ i).map X.j

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

/-- A homology pretheory indexed by `ComplexShape.down ℕ` has the dimension axiom if the
homology of a point vanishes in every positive degree. -/
class HasDimensionAxiom (HP : HomologyPretheory.{u} C (ComplexShape.down ℕ)) : Prop where
  isZero_PUnit_of_gt_zero (n : ℕ) (hn : n ≠ 0) : IsZero ((HP.H n).obj (TopCat.of PUnit))

export HasDimensionAxiom (isZero_PUnit_of_gt_zero)

end TopPair.HomologyPretheory
