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
  let e := (TopPair.subspaceSystemPullbackIso (outerPair.map φ) L).hom
  let π := (innerPair.obj T).twistedChainComplexπ ((outerPair.obj T).subspaceSystem K)
  let π' := (innerPair.obj T').twistedChainComplexπ M
  let incl' := TopPair.twistedChainComplexMap (innerToTotal.app T') L
  let subspaceMap := TopPair.twistedSubspaceChainComplexMap (outerPair.map φ) L
  let q' := (totalPair.obj T').twistedChainComplexπ L
  apply (innerPair.obj T).twistedChainComplex_hom_ext ((outerPair.obj T).subspaceSystem K)
  have hInner : π ≫ (innerPair.obj T).twistedChainComplexCoefficientMap e ≫
      TopPair.twistedChainComplexMap (innerPair.map φ) M = subspaceMap ≫ π' := by
    calc
      _ = twistedChainComplexCoefficientMap e ≫
          (innerPair.obj T).twistedChainComplexπ _ ≫
          TopPair.twistedChainComplexMap (innerPair.map φ) M :=
        (innerPair.obj T).twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc e _
      _ = twistedChainComplexCoefficientMap e ≫
          twistedChainComplexMap (homSnd φ) M ≫ π' :=
        congrArg (twistedChainComplexCoefficientMap e ≫ ·)
          (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap (innerPair.map φ) M)
      _ = subspaceMap ≫ π' :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ π') (TopPair.twistedSubspaceChainComplexMap_def (outerPair.map φ) L).symm)
  have hRight : π ≫ TopPair.twistedChainComplexMap (innerToTotal.app T) K ≫
      TopPair.twistedChainComplexMap (totalPair.map φ) L =
      twistedChainComplexMap T.outerMap K ≫ twistedChainComplexMap (homFst φ) L ≫ q' :=
    (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc (innerToTotal.app T) K _).trans
      (congrArg (twistedChainComplexMap T.outerMap K ≫ ·)
        (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap (totalPair.map φ) L))
  have hLeft : π ≫ ((innerPair.obj T).twistedChainComplexCoefficientMap e ≫
      TopPair.twistedChainComplexMap (innerPair.map φ) M) ≫ incl' =
      subspaceMap ≫ twistedChainComplexMap T'.outerMap L ≫ q' :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ incl') hInner).trans
      ((Category.assoc _ _ _).trans (congrArg (subspaceMap ≫ ·)
        (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap (innerToTotal.app T') L))))
  exact hLeft.trans
    ((TopPair.twistedChainComplexMap_naturality_pair_assoc (outerPair.map φ) L q').symm.trans
      hRight.symm)

private lemma twistedChainComplexShortComplexMap_comm₂₃ :
    TopPair.twistedChainComplexMap (totalPair.map φ) L ≫ T'.twistedChainComplexTotalToOuter L =
      T.twistedChainComplexTotalToOuter ((pullback (homFst φ).hom).obj L) ≫
        TopPair.twistedChainComplexMap (outerPair.map φ) L := by
  let K := (pullback (homFst φ).hom).obj L
  let totalMap := TopPair.twistedChainComplexMap (totalPair.map φ) L
  let outerMap := TopPair.twistedChainComplexMap (outerPair.map φ) L
  let q := T.twistedChainComplexTotalToOuter K
  let q' := T'.twistedChainComplexTotalToOuter L
  have hTotal : (totalPair.obj T).twistedChainComplexCoefficientMap (𝟙 K) ≫ totalMap ≫ q' =
      totalMap ≫ q' :=
    (congrArg (· ≫ totalMap ≫ q') ((totalPair.obj T).twistedChainComplexCoefficientMap_id K)).trans
      (Category.id_comp _)
  have hOuter : (outerPair.obj T).twistedChainComplexCoefficientMap (𝟙 K) ≫ outerMap = outerMap :=
    (congrArg (· ≫ outerMap) ((outerPair.obj T).twistedChainComplexCoefficientMap_id K)).trans
      (Category.id_comp _)
  exact hTotal.symm.trans
    ((T.twistedChainComplexTotalToOuter_naturality_of_fst_eq K (outerPair.map φ) (totalPair.map φ)
      rfl (𝟙 _) (𝟙 _) (Category.comp_id _)).symm.trans (congrArg (q ≫ ·) hOuter))

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
  let F := twistedChainComplexShortComplexMap φ L
  have h₁ : HomologicalComplex.homologyMap F.τ₁ m =
      (innerPair.obj T).twistedHomologyCoefficientMap
          (TopPair.subspaceSystemPullbackIso (outerPair.map φ) L).hom m ≫
        TopPair.twistedHomologyMap (innerPair.map φ) ((outerPair.obj T').subspaceSystem L) m :=
    (congrArg (fun g ↦ HomologicalComplex.homologyMap g m)
      (twistedChainComplexShortComplexMap_τ₁ φ L)).trans (HomologicalComplex.homologyMap_comp _ _ _)
  have h₃ : HomologicalComplex.homologyMap F.τ₃ n =
      TopPair.twistedHomologyMap (outerPair.map φ) L n :=
    congrArg (fun g ↦ HomologicalComplex.homologyMap g n)
      (twistedChainComplexShortComplexMap_τ₃ φ L)
  have hδ : T.twistedHomologyδ _ n m h ≫ HomologicalComplex.homologyMap F.τ₁ m =
      HomologicalComplex.homologyMap F.τ₃ n ≫ T'.twistedHomologyδ L n m h := by
    rw [T.twistedHomologyδ_def _ n m h, T'.twistedHomologyδ_def L n m h]
    exact HomologicalComplex.HomologySequence.δ_naturality F
      (T.shortExact_twistedChainComplexShortComplex _)
      (T'.shortExact_twistedChainComplexShortComplex L) n m (by simpa)
  exact (congrArg (T.twistedHomologyδ _ n m h ≫ ·) h₁.symm).trans
    (hδ.trans (congrArg (· ≫ T'.twistedHomologyδ L n m h) h₃))

end TauCeti.TopTriple
