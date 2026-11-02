/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Triple.Basic

/-!
# Naturality of the triple sequence with local coefficients

A map of triples `(X,A,B) ⟶ (Y,C,D)` induces a map of the short exact sequences
of relative twisted chains and hence of their long exact homology sequences.
The source coefficients are pulled back from `Y`. On `(A,B)`, restriction of
this pullback is identified with pullback of the restricted system on `C` by
`TopPair.subspaceSystemPullbackIso`. Thus the connecting-map square retains the
coefficient transport and applies to nonconstant systems over any ring.

The construction extends the pair-sequence naturality in
`TopPair.twistedChainComplexShortComplexMap` and the triple sequence in
`TauCeti.TopTriple.twistedChainComplexShortComplex`, using Mathlib's
`HomologicalComplex.HomologySequence.δ_naturality`.

## References

* A. Hatcher, *Algebraic Topology*, Sections 2.1 and 3.H.
* A. Dold, *Lectures on Algebraic Topology*, Chapters VII–VIII.
-/

public section

noncomputable section

open CategoryTheory
open TauCeti.LocalCoefficientSystem

universe u v w

namespace TauCeti.TopTriple

variable {R : Type u} [Ring R] {T T' : TopTriple.{v}} (φ : T ⟶ T')
  (L : LocalCoefficientSystem.{u, v, max v w} R T'.fst)

/-- The map on the inner relative chains, with restriction and pullback of
the coefficient system compared through the ambient square of the triple map. -/
def twistedInnerChainComplexMap :
    (innerPair.obj T).twistedChainComplex
        ((outerPair.obj T).subspaceSystem ((pullback (Hom.fst φ).hom).obj L)) ⟶
      (innerPair.obj T').twistedChainComplex ((outerPair.obj T').subspaceSystem L) :=
  (innerPair.obj T).twistedChainComplexCoefficientMap
      (TopPair.subspaceSystemPullbackIso (outerPair.map φ) L).hom ≫
    TopPair.twistedChainComplexMap (innerPair.map φ) ((outerPair.obj T').subspaceSystem L)

/-- The inner relative map is characterized on ambient chains by the map
of middle spaces, with the canonical restriction-pullback coefficient comparison. -/
@[reassoc (attr := simp)]
lemma twistedChainComplexπ_comp_twistedInnerChainComplexMap :
    (innerPair.obj T).twistedChainComplexπ
        ((outerPair.obj T).subspaceSystem ((pullback (Hom.fst φ).hom).obj L)) ≫
      twistedInnerChainComplexMap φ L =
    TopPair.twistedSubspaceChainComplexMap (outerPair.map φ) L ≫
      (innerPair.obj T').twistedChainComplexπ ((outerPair.obj T').subspaceSystem L) := by
  dsimp only [twistedInnerChainComplexMap]
  erw [TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc,
    TopPair.twistedChainComplexπ_comp_twistedChainComplexMap]
  rw [TopPair.twistedSubspaceChainComplexMap_def, Category.assoc]
  -- Both pair projections compute to the map of middle spaces.
  rfl

/-- The inclusion from inner to total relative chains commutes with maps of triples. -/
@[reassoc]
lemma twistedChainComplexMap_innerToTotal_naturality :
    TopPair.twistedChainComplexMap (innerToTotal.app T)
        ((pullback (Hom.fst φ).hom).obj L) ≫
      TopPair.twistedChainComplexMap (totalPair.map φ) L =
    twistedInnerChainComplexMap φ L ≫
      TopPair.twistedChainComplexMap (innerToTotal.app T') L := by
  apply (cancel_epi ((innerPair.obj T).twistedChainComplexπ
    ((outerPair.obj T).subspaceSystem ((pullback (Hom.fst φ).hom).obj L)))).1
  -- The three pair functors share their ambient spaces by definition. `erw` matches
  -- those presentations while the quotient formulas remove the relative wrappers.
  erw [TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc,
    TopPair.twistedChainComplexπ_comp_twistedChainComplexMap,
    twistedChainComplexπ_comp_twistedInnerChainComplexMap_assoc,
    Category.assoc, TopPair.twistedChainComplexπ_comp_twistedChainComplexMap]
  have h := congrArg (fun f ↦ f ≫ (totalPair.obj T').twistedChainComplexπ L)
    (TopPair.twistedChainComplexMap_naturality_pair (outerPair.map φ) L)
  dsimp only [innerToTotal, TopPair.Hom.fst, TopPair.ofHom, outerPair, totalPair,
    TopPair.map, TopPair.subspaceSystem, MorphismProperty.Arrow.homMk,
    MorphismProperty.Comma.Hom.hom, Arrow.homMk] at h ⊢
  simpa only [Category.assoc] using h

/-- The quotient from total to outer relative chains commutes with maps of triples. -/
@[reassoc]
lemma twistedChainComplexTotalToOuter_naturality_triple :
    T.twistedChainComplexTotalToOuter ((pullback (Hom.fst φ).hom).obj L) ≫
        TopPair.twistedChainComplexMap (outerPair.map φ) L =
      TopPair.twistedChainComplexMap (totalPair.map φ) L ≫
        T'.twistedChainComplexTotalToOuter L := by
  apply (cancel_epi ((totalPair.obj T).twistedChainComplexπ
    ((pullback (Hom.fst φ).hom).obj L))).1
  erw [T.twistedChainComplexπ_comp_totalToOuter_assoc,
    TopPair.twistedChainComplexπ_comp_twistedChainComplexMap,
    TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc,
    T'.twistedChainComplexπ_comp_totalToOuter]
  -- Both pair maps have ambient component `Hom.fst φ`.
  rfl

/-- The morphism of short exact relative twisted chain sequences induced by a map of triples. -/
def twistedChainComplexShortComplexMap :
    T.twistedChainComplexShortComplex ((pullback (Hom.fst φ).hom).obj L) ⟶
      T'.twistedChainComplexShortComplex L :=
  ShortComplex.homMk (twistedInnerChainComplexMap φ L)
    (TopPair.twistedChainComplexMap (totalPair.map φ) L)
    (TopPair.twistedChainComplexMap (outerPair.map φ) L)
    (twistedChainComplexMap_innerToTotal_naturality φ L).symm
    (twistedChainComplexTotalToOuter_naturality_triple φ L).symm

@[simp]
lemma twistedChainComplexShortComplexMap_τ₁ :
    (twistedChainComplexShortComplexMap φ L).τ₁ = twistedInnerChainComplexMap φ L := (rfl)

@[simp]
lemma twistedChainComplexShortComplexMap_τ₂ :
    (twistedChainComplexShortComplexMap φ L).τ₂ =
      TopPair.twistedChainComplexMap (totalPair.map φ) L := (rfl)

@[simp]
lemma twistedChainComplexShortComplexMap_τ₃ :
    (twistedChainComplexShortComplexMap φ L).τ₃ =
      TopPair.twistedChainComplexMap (outerPair.map φ) L := (rfl)

/-- On homology the inner chain map is coefficient change followed by the
relative homology map of the inner pair. -/
lemma homologyMap_twistedInnerChainComplexMap (k : ℕ) :
    HomologicalComplex.homologyMap (twistedInnerChainComplexMap φ L) k =
      (innerPair.obj T).twistedHomologyCoefficientMap
          (TopPair.subspaceSystemPullbackIso (outerPair.map φ) L).hom k ≫
        TopPair.twistedHomologyMap (innerPair.map φ) ((outerPair.obj T').subspaceSystem L) k := by
  dsimp only [twistedInnerChainComplexMap]
  exact HomologicalComplex.homologyMap_comp _ _ _

/-- Naturality of the inclusion in the long exact triple sequence. -/
@[reassoc]
lemma twistedHomologyMap_innerToTotal_naturality (k : ℕ) :
    TopPair.twistedHomologyMap (innerToTotal.app T) ((pullback (Hom.fst φ).hom).obj L) k ≫
        TopPair.twistedHomologyMap (totalPair.map φ) L k =
      (innerPair.obj T).twistedHomologyCoefficientMap
          (TopPair.subspaceSystemPullbackIso (outerPair.map φ) L).hom k ≫
        TopPair.twistedHomologyMap (innerPair.map φ) ((outerPair.obj T').subspaceSystem L) k ≫
          TopPair.twistedHomologyMap (innerToTotal.app T') L k := by
  have h := ((CategoryTheory.CommSq.mk
    (twistedChainComplexMap_innerToTotal_naturality φ L)).map
      (HomologicalComplex.homologyFunctor _ _ k)).w
  dsimp only [HomologicalComplex.homologyFunctor] at h
  erw [homologyMap_twistedInnerChainComplexMap] at h
  -- Normalize pair components in the implicit homology objects before reassociating.
  dsimp only [innerToTotal, TopPair.Hom.fst, TopPair.ofHom, outerPair, TopPair.map,
    TopPair.subspaceSystem, MorphismProperty.Arrow.homMk,
    MorphismProperty.Comma.Hom.hom, Arrow.homMk, TopPair.twistedHomology,
    TopPair.twistedHomologyMap] at h ⊢
  simpa only [Category.assoc] using h

/-- Naturality of the quotient in the long exact triple sequence. -/
@[reassoc]
lemma twistedHomologyTotalToOuter_naturality_triple (k : ℕ) :
    T.twistedHomologyTotalToOuter ((pullback (Hom.fst φ).hom).obj L) k ≫
        TopPair.twistedHomologyMap (outerPair.map φ) L k =
      TopPair.twistedHomologyMap (totalPair.map φ) L k ≫
        T'.twistedHomologyTotalToOuter L k := by
  exact ((CategoryTheory.CommSq.mk
    (twistedChainComplexTotalToOuter_naturality_triple φ L)).map
      (HomologicalComplex.homologyFunctor _ _ k)).w

/-- The connecting map of the local-coefficient triple sequence is natural
under maps of triples, with the canonical comparison of the inner coefficient systems. -/
@[reassoc]
lemma twistedHomologyδ_naturality (n m : ℕ) (h : m + 1 = n := by lia) :
    T.twistedHomologyδ ((pullback (Hom.fst φ).hom).obj L) n m h ≫
        (innerPair.obj T).twistedHomologyCoefficientMap
          (TopPair.subspaceSystemPullbackIso (outerPair.map φ) L).hom m ≫
        TopPair.twistedHomologyMap (innerPair.map φ) ((outerPair.obj T').subspaceSystem L) m =
      TopPair.twistedHomologyMap (outerPair.map φ) L n ≫ T'.twistedHomologyδ L n m h := by
  have key := HomologicalComplex.HomologySequence.δ_naturality
    (twistedChainComplexShortComplexMap φ L)
    (T.shortExact_twistedChainComplexShortComplex ((pullback (Hom.fst φ).hom).obj L))
    (T'.shortExact_twistedChainComplexShortComplex L) n m (by simpa)
  -- The pair presentations of the inner term require semireducible matching.
  erw [twistedChainComplexShortComplexMap_τ₁, twistedChainComplexShortComplexMap_τ₃,
    homologyMap_twistedInnerChainComplexMap] at key
  -- Unfold only the named connecting maps, rather than their chain constructions.
  rw [T.twistedHomologyδ_def _ n m h, T'.twistedHomologyδ_def L n m h]
  dsimp only [innerToTotal, TopPair.Hom.fst, TopPair.ofHom, outerPair, TopPair.map,
    TopPair.subspaceSystem, MorphismProperty.Arrow.homMk,
    MorphismProperty.Comma.Hom.hom, Arrow.homMk, TopPair.twistedHomology,
    TopPair.twistedHomologyMap] at key ⊢
  exact key

end TauCeti.TopTriple
