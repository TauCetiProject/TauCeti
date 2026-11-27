/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Triple

/-!
# Naturality of the triple sequence with local coefficients

A map of triples induces `TopTriple.twistedChainComplexShortComplexMap` from the triple
sequence with pulled-back coefficients to the triple sequence with the original coefficients.
The map on the inner term uses `TopPair.subspaceSystemPullbackIso` to compare restriction
after pullback with pullback after restriction. The short exact sequence
`TopTriple.shortExact_twistedChainComplexShortComplex` and Mathlib's naturality of the
connecting morphism give `TopTriple.twistedHomologyδ_naturality`.

See A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
Section 3.H, for relative homology with local coefficients and its exact sequence.
-/

public section

noncomputable section

open CategoryTheory

universe u v w

namespace TauCeti.TopTriple

open LocalCoefficientSystem

variable {R : Type u} [Ring R] {T T' : TopTriple.{v}} (φ : T ⟶ T')
  (L : LocalCoefficientSystem.{u, v, max v w} R T'.fst)

-- The commutativity proofs are used by the short-complex constructor below.
private lemma twistedChainComplexShortComplexMap_comm₁₂ :
    ((innerPair.obj T).twistedChainComplexCoefficientMap
        (TopPair.subspaceSystemPullbackIso (outerPair.map φ) L).hom ≫
      TopPair.twistedChainComplexMap (innerPair.map φ) ((outerPair.obj T').subspaceSystem L)) ≫
        (T'.twistedChainComplexShortComplex L).f =
      (T.twistedChainComplexShortComplex ((pullback (homFst φ).hom).obj L)).f ≫
        TopPair.twistedChainComplexMap (totalPair.map φ) L := by
  let K := (pullback (homFst φ).hom).obj L
  let M := (outerPair.obj T').subspaceSystem L
  -- Use the same pullback in the types of the coefficient map and each adjacent pair map.
  let N := (pullback (homSnd φ).hom).obj M
  let e : (outerPair.obj T).subspaceSystem K ⟶ N :=
    (TopPair.subspaceSystemPullbackIso (outerPair.map φ) L).hom
  let inner : (innerPair.obj T).twistedChainComplex N ⟶ (innerPair.obj T').twistedChainComplex M :=
    TopPair.twistedChainComplexMap (innerPair.map φ) M
  let incl : (innerPair.obj T).twistedChainComplex ((outerPair.obj T).subspaceSystem K) ⟶
      (totalPair.obj T).twistedChainComplex K :=
    TopPair.twistedChainComplexMap (innerToTotal.app T) K
  let incl' : (innerPair.obj T').twistedChainComplex M ⟶ (totalPair.obj T').twistedChainComplex L :=
    TopPair.twistedChainComplexMap (innerToTotal.app T') L
  let total : (totalPair.obj T).twistedChainComplex K ⟶ (totalPair.obj T').twistedChainComplex L :=
    TopPair.twistedChainComplexMap (totalPair.map φ) L
  let π := (innerPair.obj T).twistedChainComplexπ ((outerPair.obj T).subspaceSystem K)
  apply (innerPair.obj T).twistedChainComplex_hom_ext ((outerPair.obj T).subspaceSystem K)
  have square : π ≫ ((innerPair.obj T).twistedChainComplexCoefficientMap e ≫ inner) ≫ incl' =
      π ≫ incl ≫ total := by
    have hInner : (innerPair.obj T).twistedChainComplexπ N ≫ inner =
        twistedChainComplexMap (homSnd φ) M ≫ (innerPair.obj T').twistedChainComplexπ M :=
      TopPair.twistedChainComplexπ_comp_twistedChainComplexMap (innerPair.map φ) M
    have hIncl' : (innerPair.obj T').twistedChainComplexπ M ≫ incl' =
        twistedChainComplexMap T'.outerMap L ≫ (totalPair.obj T').twistedChainComplexπ L :=
      TopPair.twistedChainComplexπ_comp_twistedChainComplexMap (innerToTotal.app T') L
    have hIncl : π ≫ incl = twistedChainComplexMap T.outerMap K ≫
        (totalPair.obj T).twistedChainComplexπ K :=
      TopPair.twistedChainComplexπ_comp_twistedChainComplexMap (innerToTotal.app T) K
    have hTotal : (totalPair.obj T).twistedChainComplexπ K ≫ total =
        twistedChainComplexMap (homFst φ) L ≫ (totalPair.obj T').twistedChainComplexπ L :=
      TopPair.twistedChainComplexπ_comp_twistedChainComplexMap (totalPair.map φ) L
    rw [Category.assoc,
      (innerPair.obj T).twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc,
      reassoc_of% hInner, hIncl', reassoc_of% hIncl, hTotal]
    refine Eq.trans ?_ (TopPair.twistedChainComplexMap_naturality_pair_assoc (outerPair.map φ) L
      ((totalPair.obj T').twistedChainComplexπ L)).symm
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) (TopPair.twistedSubspaceChainComplexMap_def (outerPair.map φ) L).symm)
  exact square

private lemma twistedChainComplexShortComplexMap_comm₂₃ :
    TopPair.twistedChainComplexMap (totalPair.map φ) L ≫ T'.twistedChainComplexTotalToOuter L =
      T.twistedChainComplexTotalToOuter ((pullback (homFst φ).hom).obj L) ≫
        TopPair.twistedChainComplexMap (outerPair.map φ) L := by
  let K := (pullback (homFst φ).hom).obj L
  -- Give both pair maps their common pullback explicitly so the identity maps can simplify.
  let outer : (outerPair.obj T).twistedChainComplex K ⟶ _ :=
    TopPair.twistedChainComplexMap (outerPair.map φ) L
  let total : (totalPair.obj T).twistedChainComplex K ⟶ _ :=
    TopPair.twistedChainComplexMap (totalPair.map φ) L
  have square :
      T.twistedChainComplexTotalToOuter K ≫ (outerPair.obj T).twistedChainComplexCoefficientMap
        (𝟙 K) ≫ outer =
      (totalPair.obj T).twistedChainComplexCoefficientMap (𝟙 K) ≫ total ≫
        T'.twistedChainComplexTotalToOuter L :=
    T.twistedChainComplexTotalToOuter_naturality_of_fst_eq K
      (outerPair.map φ) (totalPair.map φ) rfl (𝟙 _) (𝟙 _) (Category.comp_id _)
  rw [(outerPair.obj T).twistedChainComplexCoefficientMap_id K,
    (totalPair.obj T).twistedChainComplexCoefficientMap_id K, Category.id_comp, Category.id_comp]
    at square
  exact square.symm

/-- A map of triples induces a morphism of the short exact sequences of relative twisted
chains, with the source coefficients pulled back along the ambient map. -/
def twistedChainComplexShortComplexMap :
    T.twistedChainComplexShortComplex ((pullback (homFst φ).hom).obj L) ⟶
      T'.twistedChainComplexShortComplex L :=
  ShortComplex.homMk
    ((innerPair.obj T).twistedChainComplexCoefficientMap
      (TopPair.subspaceSystemPullbackIso (outerPair.map φ) L).hom ≫
        TopPair.twistedChainComplexMap (innerPair.map φ) ((outerPair.obj T').subspaceSystem L))
    (TopPair.twistedChainComplexMap (totalPair.map φ) L)
    (TopPair.twistedChainComplexMap (outerPair.map φ) L)
    (twistedChainComplexShortComplexMap_comm₁₂ φ L)
    (twistedChainComplexShortComplexMap_comm₂₃ φ L)

/-- The inner projection formula identifies the coefficient systems before applying the pair map. -/
@[simp]
lemma twistedChainComplexShortComplexMap_τ₁ :
    (twistedChainComplexShortComplexMap φ L).τ₁ =
      (innerPair.obj T).twistedChainComplexCoefficientMap
        (TopPair.subspaceSystemPullbackIso (outerPair.map φ) L).hom ≫
      TopPair.twistedChainComplexMap (innerPair.map φ) ((outerPair.obj T').subspaceSystem L) :=
  (rfl)

/-- The middle projection formula identifies this component with the map of total pairs. -/
@[simp]
lemma twistedChainComplexShortComplexMap_τ₂ :
    (twistedChainComplexShortComplexMap φ L).τ₂ =
      TopPair.twistedChainComplexMap (totalPair.map φ) L := (rfl)

/-- The last projection formula identifies this component with the map of outer pairs. -/
@[simp]
lemma twistedChainComplexShortComplexMap_τ₃ :
    (twistedChainComplexShortComplexMap φ L).τ₃ =
      TopPair.twistedChainComplexMap (outerPair.map φ) L := (rfl)

/-- The connecting morphism of the triple sequence with local coefficients commutes with
the maps induced by a morphism of triples, using the canonical comparison of the systems
on the middle space. -/
@[reassoc]
lemma twistedHomologyδ_naturality (n m : ℕ) (h : m + 1 = n := by lia) :
    T.twistedHomologyδ ((pullback (homFst φ).hom).obj L) n m h ≫
        (innerPair.obj T).twistedHomologyCoefficientMap
          (TopPair.subspaceSystemPullbackIso (outerPair.map φ) L).hom m ≫
        TopPair.twistedHomologyMap (innerPair.map φ) ((outerPair.obj T').subspaceSystem L) m =
      TopPair.twistedHomologyMap (outerPair.map φ) L n ≫ T'.twistedHomologyδ L n m h := by
  rw [T.twistedHomologyδ_def _ n m h, T'.twistedHomologyδ_def L n m h]
  have hδ := HomologicalComplex.HomologySequence.δ_naturality
    (twistedChainComplexShortComplexMap φ L) (T.shortExact_twistedChainComplexShortComplex _)
    (T'.shortExact_twistedChainComplexShortComplex L) n m (by simpa)
  rw [twistedChainComplexShortComplexMap_τ₁, twistedChainComplexShortComplexMap_τ₃] at hδ
  exact (congrArg (_ ≫ ·) (HomologicalComplex.homologyMap_comp _ _ _).symm).trans hδ

end TauCeti.TopTriple
