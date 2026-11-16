/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Restriction.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Discrete

/-!
# Functoriality and naturality of Borel–Moore open restriction

This file establishes the functoriality and naturality laws for open restriction in Borel–Moore
homology (`TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrictOfExhaustion` and
`TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrict`):

* naturality in morphisms of local coefficient systems (`borelMooreHomologyRestrict_naturality`),
* identity law (`borelMooreHomologyRestrict_id`),
* contravariant composition law for composable open embeddings `W ⟶ V ⟶ X`
  (`borelMooreHomologyRestrict_comp`),
* concrete degree-zero verification on a discrete space
  (`borelMooreHomologyRestrict_zero_comp_isoPi`), showing that under `borelMooreHomologyZeroIsoPi`
  open restriction corresponds to restricting a family of point coefficients to the open subset.

## Main results

* `TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrictOfExhaustion_naturality` and
  `TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrict_naturality`: naturality in local
  coefficient morphisms.
* `TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrictOfExhaustion_id` and
  `TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrict_id`: restriction along the identity.
* `TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrictOfExhaustion_comp` and
  `TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrict_comp`: contravariant functoriality
  under composition of open embeddings.
* `TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrict_zero_comp_isoPi`: degree-zero check on
  discrete spaces.

## References

* A. Borel and J. C. Moore, *Homology theory for locally compact spaces*, Michigan Math. J. 7
  (1960), 137–159.
* G. E. Bredon, *Sheaf Theory*, 2nd ed., Graduate Texts in Mathematics 170, Chapter V.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite SimplexCategory Topology
open scoped Simplicial

universe u v w

namespace TauCeti.LocalCoefficientSystem

private lemma locallyFiniteChainComplexToRelative_congr {R : Type u} [Ring R] {X : TopCat.{v}}
    (L : LocalCoefficientSystem.{u, v, max v w} R X) {S T : Set X} (h : S = T)
    (hS : IsCompact (Set.range (TopPair.ofSubset S).map)ᶜ)
    (hT : IsCompact (Set.range (TopPair.ofSubset T).map)ᶜ) :
    (TopPair.ofSubset S).locallyFiniteChainComplexToRelative L hS ≫
        eqToHom (congrArg (fun A : Set X ↦ (TopPair.ofSubset A).twistedChainComplex L) h) =
      (TopPair.ofSubset T).locallyFiniteChainComplexToRelative L hT := by
  subst h
  simp

variable {R : Type u} [Ring R]

section ExhaustionRestriction

variable {V X : TopCat.{v}} {j : V ⟶ X}
  (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- A morphism of local coefficient systems induces a morphism of ambient relative towers. -/
def ambientRelativeChainComplexTowerCoeffMap
    {L K : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ K) (E : CompactExhaustion V) :
    ambientRelativeChainComplexTower j L E ⟶ ambientRelativeChainComplexTower j K E where
  app n := (TopPair.ofSubset (j.hom '' E n.unop)ᶜ).twistedChainComplexCoefficientMap η
  naturality {m n} f := by
    apply (TopPair.ofSubset (j.hom '' E m.unop)ᶜ).twistedChainComplex_hom_ext L
    exact (twistedChainComplexπ_comp_ambientRelativeChainComplexTower_map_assoc j L E f _).trans <|
      ((TopPair.ofSubset
          (j.hom '' E n.unop)ᶜ).twistedChainComplexπ_comp_twistedChainComplexCoefficientMap
          η).trans <|
        ((TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc
            (TopPair.ofSubset (j.hom '' E m.unop)ᶜ) η _).trans <|
          congrArg (_ ≫ ·)
            (twistedChainComplexπ_comp_ambientRelativeChainComplexTower_map j K E f)).symm

/-- On each level, `ambientRelativeChainComplexTowerCoeffMap` is the relative coefficient map. -/
@[simp]
lemma ambientRelativeChainComplexTowerCoeffMap_app
    {L K : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ K)
    (E : CompactExhaustion V) (n : ℕ) :
    (ambientRelativeChainComplexTowerCoeffMap (j := j) η E).app (op n) =
      (TopPair.ofSubset (j.hom '' E n)ᶜ).twistedChainComplexCoefficientMap η :=
  (rfl)

private lemma locallyFiniteChainComplexToAmbientTower_naturality
    {L K : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ K) (E : CompactExhaustion V) :
    locallyFiniteChainComplexCoefficientMap η ≫
        locallyFiniteChainComplexToAmbientTower j K E =
      locallyFiniteChainComplexToAmbientTower j L E ≫
        ComplexTower.limComplexMap (ambientRelativeChainComplexTowerCoeffMap (j := j) η E) := by
  apply (ambientRelativeChainComplexTower j K E).isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  let φ := ambientRelativeChainComplexTowerCoeffMap (j := j) η E
  exact (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·)
      (locallyFiniteChainComplexToAmbientTower_comp_limComplexπ j K E n)).trans <|
      (TopPair.locallyFiniteChainComplexCoefficientMap_comp_toRelative
          (TopPair.ofSubset (j.hom '' E n)ᶜ) η
          ((E.isCompact n).image j.hom.continuous).compl_range_ofSubset_compl_map).trans <|
        ((Category.assoc _ _ _).trans <|
          (congrArg (_ ≫ ·) (ComplexTower.limComplexMap_comp_π φ n)).trans
            (locallyFiniteChainComplexToAmbientTower_comp_limComplexπ_assoc j L E n
              (φ.app (op n)))).symm

/-- The excision right leg is natural in morphisms of local coefficient systems. -/
@[reassoc]
lemma openEmbeddingRightLeg_naturality (hj : Function.Injective j.hom)
    {L K : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ K) (E : CompactExhaustion V) :
    locallyFiniteChainComplexCoefficientMap ((pullback j.hom).map η) ≫
        openEmbeddingRightLeg K E hj =
      openEmbeddingRightLeg L E hj ≫
        ComplexTower.limComplexMap (ambientRelativeChainComplexTowerCoeffMap (j := j) η E) := by
  apply (ambientRelativeChainComplexTower j K E).isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  let φ := ambientRelativeChainComplexTowerCoeffMap (j := j) η E
  exact (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (openEmbeddingRightLeg_comp_limComplexπ K E hj n)).trans <|
      (TopPair.locallyFiniteChainComplexCoefficientMap_comp_toRelative_assoc
          (TopPair.ofSubset (E n)ᶜ) ((pullback j.hom).map η)
          (E.isCompact n).compl_range_ofSubset_compl_map
          (TopPair.twistedChainComplexMap (injectivePairMap hj (E n)) K)).trans <|
        (congrArg
          ((TopPair.ofSubset (E n)ᶜ).locallyFiniteChainComplexToRelative ((pullback j.hom).obj L)
            (E.isCompact n).compl_range_ofSubset_compl_map ≫ ·)
          (TopPair.twistedChainComplexMap_naturality (injectivePairMap hj (E n)) L η).symm).trans
          <| (Category.assoc _ _ _).symm.trans <|
            ((Category.assoc _ _ _).trans <|
              (congrArg (_ ≫ ·) (ComplexTower.limComplexMap_comp_π φ n)).trans
                (openEmbeddingRightLeg_comp_limComplexπ_assoc L E hj n (φ.app (op n)))).symm

/-- Open restriction via an explicit exhaustion is natural in morphisms of local coefficient
systems. -/
@[reassoc]
theorem borelMooreHomologyRestrictOfExhaustion_naturality (hj : IsOpenEmbedding j.hom)
    {L K : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ K)
    (E : CompactExhaustion V) (hE : ∀ n, closure (j.hom '' E n) ⊆ Set.range j.hom) (k : ℕ) :
    borelMooreHomologyCoefficientMap η k ≫
        borelMooreHomologyRestrictOfExhaustion K hj E hE k =
      borelMooreHomologyRestrictOfExhaustion L hj E hE k ≫
        borelMooreHomologyCoefficientMap ((pullback j.hom).map η) k := by
  have := quasiIso_openEmbeddingRightLeg K E hj hE
  rw [← cancel_mono (HomologicalComplex.homologyMap (openEmbeddingRightLeg K E hj.injective) k),
    Category.assoc, borelMooreHomologyRestrictOfExhaustion_comp_rightLeg]
  calc borelMooreHomologyCoefficientMap η k ≫
        HomologicalComplex.homologyMap (locallyFiniteChainComplexToAmbientTower j K E) k
    _ = HomologicalComplex.homologyMap (locallyFiniteChainComplexToAmbientTower j L E) k ≫
          HomologicalComplex.homologyMap
            (ComplexTower.limComplexMap
              (ambientRelativeChainComplexTowerCoeffMap (j := j) η E)) k := by
        rw [← HomologicalComplex.homologyMap_comp,
          locallyFiniteChainComplexToAmbientTower_naturality, HomologicalComplex.homologyMap_comp]
    _ = borelMooreHomologyRestrictOfExhaustion L hj E hE k ≫
          borelMooreHomologyCoefficientMap ((pullback j.hom).map η) k ≫
            HomologicalComplex.homologyMap (openEmbeddingRightLeg K E hj.injective) k := by
        rw [← borelMooreHomologyRestrictOfExhaustion_comp_rightLeg L hj E hE k, Category.assoc,
          ← HomologicalComplex.homologyMap_comp, ← openEmbeddingRightLeg_naturality,
          HomologicalComplex.homologyMap_comp]
    _ = (borelMooreHomologyRestrictOfExhaustion L hj E hE k ≫
          borelMooreHomologyCoefficientMap ((pullback j.hom).map η) k) ≫
          HomologicalComplex.homologyMap (openEmbeddingRightLeg K E hj.injective) k :=
        (Category.assoc _ _ _).symm

/-- Open restriction along the identity map is the coefficient comparison `pullbackIdIso.inv`. -/
theorem borelMooreHomologyRestrictOfExhaustion_id
    (hid : IsOpenEmbedding (TopCat.Hom.hom (𝟙 X)))
    (K : CompactExhaustion X)
    (hK : ∀ n, closure (TopCat.Hom.hom (𝟙 X) '' K n) ⊆ Set.range (TopCat.Hom.hom (𝟙 X)))
    (k : ℕ) :
    borelMooreHomologyRestrictOfExhaustion L (j := 𝟙 X) hid K hK k =
      borelMooreHomologyCoefficientMap ((pullbackIdIso X).inv.app L) k := by
  refine ((eq_borelMooreHomologyRestrictOfExhaustion_iff L (j := 𝟙 X) hid K hK k _).2 ?_).symm
  rw [← HomologicalComplex.homologyMap_comp]
  congr 1
  apply (ambientRelativeChainComplexTower (𝟙 X) L K).isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  have hEq : (K n)ᶜ = (TopCat.Hom.hom (𝟙 X) '' K n)ᶜ := by simp
  have hcomp : (TopPair.ofSubset (K n)ᶜ).twistedChainComplexCoefficientMap
        ((pullbackIdIso X).inv.app L) ≫
      TopPair.twistedChainComplexMap (injectivePairMap (j := 𝟙 X) hid.injective (K n)) L =
      eqToHom (congrArg (fun A : Set X ↦ (TopPair.ofSubset A).twistedChainComplex L) hEq) := by
    apply (TopPair.ofSubset (K n)ᶜ).twistedChainComplex_hom_ext L
    have hfst : twistedChainComplexCoefficientMap ((pullbackIdIso X).inv.app L) ≫
        twistedChainComplexMap (𝟙 X) L = 𝟙 (twistedChainComplex L) := by
      rw [twistedChainComplexMap_id, ← twistedChainComplexCoefficientMap_comp]
      simp
    have h1 : (TopPair.ofSubset (K n)ᶜ).twistedChainComplexπ L ≫
        (TopPair.ofSubset (K n)ᶜ).twistedChainComplexCoefficientMap
          ((pullbackIdIso X).inv.app L) ≫
        TopPair.twistedChainComplexMap (injectivePairMap (j := 𝟙 X) hid.injective (K n)) L =
        (TopPair.ofSubset (TopCat.Hom.hom (𝟙 X) '' K n)ᶜ).twistedChainComplexπ L :=
      (TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc
        (TopPair.ofSubset (K n)ᶜ) ((pullbackIdIso X).inv.app L) _).trans <|
        (congrArg (_ ≫ ·) (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap
          (injectivePairMap (j := 𝟙 X) hid.injective (K n)) L)).trans <|
          (Category.assoc _ _ _).symm.trans <|
            (congrArg (· ≫
              (TopPair.ofSubset (TopCat.Hom.hom (𝟙 X) '' K n)ᶜ).twistedChainComplexπ L)
              hfst).trans (Category.id_comp _)
    refine h1.trans ?_
    generalize hS : (TopCat.Hom.hom (𝟙 X) '' K n)ᶜ = S at hEq ⊢
    subst hEq
    simp
  exact (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·)
      (openEmbeddingRightLeg_comp_limComplexπ L (j := 𝟙 X) K hid.injective n)).trans
      <| (TopPair.locallyFiniteChainComplexCoefficientMap_comp_toRelative_assoc
        (TopPair.ofSubset (K n)ᶜ) ((pullbackIdIso X).inv.app L) _ _).trans <|
        (congrArg (_ ≫ ·) hcomp).trans <|
          (locallyFiniteChainComplexToRelative_congr L hEq _ _).trans
            (locallyFiniteChainComplexToAmbientTower_comp_limComplexπ (𝟙 X) L K n).symm

section CompHelpers

variable {W : TopCat.{v}} {i : W ⟶ V}

private lemma image_comp_subset_of_subset {KW : CompactExhaustion W} {KV' : CompactExhaustion V}
    (hsub : ∀ n, i.hom '' KW n ⊆ KV' n) (n : ℕ) :
    (j.hom '' KV' n)ᶜ ⊆ ((i ≫ j).hom '' KW n)ᶜ :=
  Set.compl_subset_compl.2 <| by
    have h : (i ≫ j).hom '' KW n = j.hom '' (i.hom '' KW n) := by simp [Set.image_image]
    rw [h]
    exact Set.image_mono (hsub n)

-- Uses `TopPair.ofHom` rather than `TopPair.ofSubsetMap` so `Hom.fst` stays definitionally `j`.
private abbrev compExcisionJPairMap (hj : Function.Injective j.hom) (KW : CompactExhaustion W)
    (n : ℕ) :
    TopPair.ofSubset (i.hom '' KW n)ᶜ ⟶ TopPair.ofSubset ((i ≫ j).hom '' KW n)ᶜ :=
  TopPair.ofHom j
    (TopCat.ofHom ⟨Set.MapsTo.restrict j.hom (i.hom '' KW n)ᶜ ((i ≫ j).hom '' KW n)ᶜ
        (fun _ hx ⟨w, hw, hwx⟩ ↦ hx ⟨w, hw, hj hwx⟩),
      j.hom.continuous.restrict _⟩)

private def compTowerQuotX (KW : CompactExhaustion W) (KV' : CompactExhaustion V)
    (hsub : ∀ n, i.hom '' KW n ⊆ KV' n) :
    ambientRelativeChainComplexTower j L KV' ⟶
      ambientRelativeChainComplexTower (i ≫ j) L KW where
  app n := (TopTriple.ofSubset
    (image_comp_subset_of_subset (i := i) (j := j) hsub n.unop)).twistedChainComplexTotalToOuter L
  naturality {m n} f := by
    apply (TopPair.ofSubset (j.hom '' KV' m.unop)ᶜ).twistedChainComplex_hom_ext L
    have hN := image_comp_subset_of_subset (i := i) (j := j) hsub n.unop
    have hM := image_comp_subset_of_subset (i := i) (j := j) hsub m.unop
    exact (twistedChainComplexπ_comp_ambientRelativeChainComplexTower_map_assoc j L KV' f _).trans
      <| ((TopTriple.ofSubset hN).twistedChainComplexπ_comp_totalToOuter L).trans <|
        (((TopTriple.ofSubset hM).twistedChainComplexπ_comp_totalToOuter_assoc L _).trans
          (twistedChainComplexπ_comp_ambientRelativeChainComplexTower_map (i ≫ j) L KW f)).symm

private def compTowerQuotV (KW : CompactExhaustion W) (KV' : CompactExhaustion V)
    (hsub : ∀ n, i.hom '' KW n ⊆ KV' n) :
    relativeChainComplexTower ((pullback j.hom).obj L) KV' ⟶
      ambientRelativeChainComplexTower i ((pullback j.hom).obj L) KW where
  app n := (TopTriple.ofSubset
    (Set.compl_subset_compl.2 (hsub n.unop))).twistedChainComplexTotalToOuter
      ((pullback j.hom).obj L)
  naturality {m n} f := by
    apply (TopPair.ofSubset (KV' m.unop)ᶜ).twistedChainComplex_hom_ext ((pullback j.hom).obj L)
    have hN : (KV' n.unop)ᶜ ⊆ (i.hom '' KW n.unop)ᶜ := Set.compl_subset_compl.2 (hsub n.unop)
    have hM : (KV' m.unop)ᶜ ⊆ (i.hom '' KW m.unop)ᶜ := Set.compl_subset_compl.2 (hsub m.unop)
    exact (twistedChainComplexπ_comp_relativeChainComplexTower_map_assoc _ KV' f _).trans <|
      ((TopTriple.ofSubset hN).twistedChainComplexπ_comp_totalToOuter _).trans <|
        (((TopTriple.ofSubset hM).twistedChainComplexπ_comp_totalToOuter_assoc _ _).trans
          (twistedChainComplexπ_comp_ambientRelativeChainComplexTower_map i _ KW f)).symm

private def compTowerExcisionJ (hj : Function.Injective j.hom) (KW : CompactExhaustion W) :
    ambientRelativeChainComplexTower i ((pullback j.hom).obj L) KW ⟶
      ambientRelativeChainComplexTower (i ≫ j) L KW where
  app n := TopPair.twistedChainComplexMap (compExcisionJPairMap (i := i) (j := j) hj KW n.unop) L
  naturality {m n} f := by
    apply (TopPair.ofSubset (i.hom '' KW m.unop)ᶜ).twistedChainComplex_hom_ext
      ((pullback j.hom).obj L)
    exact (twistedChainComplexπ_comp_ambientRelativeChainComplexTower_map_assoc
        i ((pullback j.hom).obj L) KW f _).trans <|
      (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap
        (compExcisionJPairMap (i := i) (j := j) hj KW n.unop) L).trans <|
        ((TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc
            (compExcisionJPairMap (i := i) (j := j) hj KW m.unop) L _).trans <|
          congrArg (_ ≫ ·)
            (twistedChainComplexπ_comp_ambientRelativeChainComplexTower_map (i ≫ j) L KW f)).symm

private lemma comp_left_square (KW : CompactExhaustion W) (KV' : CompactExhaustion V)
    (hsub : ∀ n, i.hom '' KW n ⊆ KV' n) :
    locallyFiniteChainComplexToAmbientTower j L KV' ≫
        ComplexTower.limComplexMap (compTowerQuotX (i := i) (j := j) L KW KV' hsub) =
      locallyFiniteChainComplexToAmbientTower (i ≫ j) L KW := by
  apply (ambientRelativeChainComplexTower (i ≫ j) L KW).isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  exact (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (ComplexTower.limComplexMap_comp_π _ n)).trans <|
      (locallyFiniteChainComplexToAmbientTower_comp_limComplexπ_assoc j L KV' n _).trans <|
        (TopTriple.locallyFiniteChainComplexToRelative_comp_twistedChainComplexTotalToOuter
          (TopTriple.ofSubset (image_comp_subset_of_subset (i := i) (j := j) hsub n))
          L _ _).trans
          (locallyFiniteChainComplexToAmbientTower_comp_limComplexπ (i ≫ j) L KW n).symm

private lemma comp_middle_square (hj : Function.Injective j.hom)
    (KW : CompactExhaustion W) (KV' : CompactExhaustion V)
    (hsub : ∀ n, i.hom '' KW n ⊆ KV' n) :
    openEmbeddingRightLeg L KV' hj ≫
        ComplexTower.limComplexMap (compTowerQuotX (i := i) (j := j) L KW KV' hsub) =
      locallyFiniteChainComplexToAmbientTower i ((pullback j.hom).obj L) KW ≫
        ComplexTower.limComplexMap (compTowerExcisionJ (i := i) (j := j) L hj KW) := by
  apply (ambientRelativeChainComplexTower (i ≫ j) L KW).isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  have hsqn : TopPair.twistedChainComplexMap (injectivePairMap hj (KV' n)) L ≫
        (compTowerQuotX (i := i) (j := j) L KW KV' hsub).app (op n) =
      (compTowerQuotV (i := i) (j := j) L KW KV' hsub).app (op n) ≫
        (compTowerExcisionJ (i := i) (j := j) L hj KW).app (op n) := by
    apply (TopPair.ofSubset (KV' n)ᶜ).twistedChainComplex_hom_ext ((pullback j.hom).obj L)
    have hsubN := image_comp_subset_of_subset (i := i) (j := j) hsub n
    exact (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc
        (injectivePairMap hj (KV' n)) L _).trans <|
      (congrArg (_ ≫ ·)
        ((TopTriple.ofSubset hsubN).twistedChainComplexπ_comp_totalToOuter L)).trans <|
        (((TopTriple.ofSubset
            (Set.compl_subset_compl.2 (hsub n))).twistedChainComplexπ_comp_totalToOuter_assoc
            ((pullback j.hom).obj L) _).trans
          (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap
            (compExcisionJPairMap (i := i) (j := j) hj KW n) L)).symm
  exact (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (ComplexTower.limComplexMap_comp_π _ n)).trans <|
      (openEmbeddingRightLeg_comp_limComplexπ_assoc L KV' hj n _).trans <|
        (Category.assoc _ _ _).trans <|
          (congrArg (_ ≫ ·) hsqn).trans <|
            (Category.assoc _ _ _).symm.trans <|
              (congrArg (· ≫ _)
                (TopTriple.locallyFiniteChainComplexToRelative_comp_twistedChainComplexTotalToOuter
                  (TopTriple.ofSubset (Set.compl_subset_compl.2 (hsub n)))
                  ((pullback j.hom).obj L) _ _)).trans <|
                ((Category.assoc _ _ _).trans <|
                  (congrArg (_ ≫ ·) (ComplexTower.limComplexMap_comp_π _ n)).trans
                    (locallyFiniteChainComplexToAmbientTower_comp_limComplexπ_assoc
                      i ((pullback j.hom).obj L) KW n _)).symm

private lemma comp_right_square (hi : Function.Injective i.hom) (hj : Function.Injective j.hom)
    (hij : Function.Injective (i ≫ j).hom) (KW : CompactExhaustion W) :
    locallyFiniteChainComplexCoefficientMap ((pullbackCompIso i.hom j.hom).hom.app L) ≫
        openEmbeddingRightLeg ((pullback j.hom).obj L) KW hi ≫
          ComplexTower.limComplexMap (compTowerExcisionJ (i := i) (j := j) L hj KW) =
      openEmbeddingRightLeg L KW hij := by
  apply (ambientRelativeChainComplexTower (i ≫ j) L KW).isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  let φ := compTowerExcisionJ (i := i) (j := j) L hj KW
  have hmap : (TopPair.ofSubset (KW n)ᶜ).twistedChainComplexCoefficientMap
        ((pullbackCompIso i.hom j.hom).hom.app L) ≫
      TopPair.twistedChainComplexMap (injectivePairMap hi (KW n)) ((pullback j.hom).obj L) ≫
        φ.app (op n) =
      TopPair.twistedChainComplexMap (injectivePairMap hij (KW n)) L := by
    apply (TopPair.ofSubset (KW n)ᶜ).twistedChainComplex_hom_ext _
    exact (TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc
        (TopPair.ofSubset (KW n)ᶜ) ((pullbackCompIso i.hom j.hom).hom.app L) _).trans <|
      (congrArg (_ ≫ ·) (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc
        (injectivePairMap hi (KW n)) ((pullback j.hom).obj L) _)).trans <|
        (congrArg (_ ≫ ·) (congrArg (_ ≫ ·)
          (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap
            (compExcisionJPairMap (i := i) (j := j) hj KW n) L))).trans <|
          (Category.assoc _ _ _).symm.trans <|
            (Category.assoc _ _ _).symm.trans <|
              (congrArg (· ≫ _) (twistedChainComplexMap_comp i j L).symm).trans
                (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap
                  (injectivePairMap hij (KW n)) L).symm
  exact (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans <|
      (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (ComplexTower.limComplexMap_comp_π φ n))).trans <|
        (congrArg (_ ≫ ·)
          (openEmbeddingRightLeg_comp_limComplexπ_assoc ((pullback j.hom).obj L) KW hi n
            (φ.app (op n)))).trans <|
          (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans <|
            (TopPair.locallyFiniteChainComplexCoefficientMap_comp_toRelative_assoc
              (TopPair.ofSubset (KW n)ᶜ) ((pullbackCompIso i.hom j.hom).hom.app L)
              (KW.isCompact n).compl_range_ofSubset_compl_map
              (TopPair.twistedChainComplexMap (injectivePairMap hi (KW n))
                  ((pullback j.hom).obj L) ≫ φ.app (op n))).trans <|
              (Category.assoc _ _ _).trans <|
                (congrArg
                  ((TopPair.ofSubset (KW n)ᶜ).locallyFiniteChainComplexToRelative
                    ((pullback (i ≫ j).hom).obj L)
                    (KW.isCompact n).compl_range_ofSubset_compl_map ≫ ·)
                  hmap).trans
                  (openEmbeddingRightLeg_comp_limComplexπ L KW hij n).symm

end CompHelpers

/-- Composition law for exhaustion-explicit open restrictions. -/
theorem borelMooreHomologyRestrictOfExhaustion_comp {W : TopCat.{v}} {i : W ⟶ V}
    (hi : IsOpenEmbedding i.hom) (hj : IsOpenEmbedding j.hom)
    (KW : CompactExhaustion W) (KV : CompactExhaustion V)
    (hKW_V : ∀ n, closure (i.hom '' KW n) ⊆ Set.range i.hom)
    (hKW_X : ∀ n, closure ((i ≫ j).hom '' KW n) ⊆ Set.range (i ≫ j).hom)
    (hKV_X : ∀ n, closure (j.hom '' KV n) ⊆ Set.range j.hom) (k : ℕ) :
    borelMooreHomologyRestrictOfExhaustion L hj KV hKV_X k ≫
        borelMooreHomologyRestrictOfExhaustion ((pullback j.hom).obj L) hi KW hKW_V k =
      borelMooreHomologyRestrictOfExhaustion L (j := i ≫ j)
          (by simpa using hj.comp hi) KW hKW_X k ≫
        borelMooreHomologyCoefficientMap ((pullbackCompIso i.hom j.hom).hom.app L) k := by
  let KV' := KV.unionImage KW hi.continuous hi.isOpenMap
  have hsub (n : ℕ) : i.hom '' KW n ⊆ KV' n := by
    simp only [KV', CompactExhaustion.unionImage_apply]
    exact Set.subset_union_right
  have hKV'_X (n : ℕ) : closure (j.hom '' KV' n) ⊆ Set.range j.hom := by
    simp only [KV', CompactExhaustion.unionImage_apply, Set.image_union, closure_union,
      ← Set.image_comp]
    exact Set.union_subset (hKV_X n)
      ((hKW_X n).trans (by rintro _ ⟨w, rfl⟩; exact ⟨i.hom w, rfl⟩))
  rw [borelMooreHomologyRestrictOfExhaustion_eq L hj KV KV' hKV_X hKV'_X k]
  have hij : IsOpenEmbedding (i ≫ j).hom := by simpa using hj.comp hi
  have hq_ij := quasiIso_openEmbeddingRightLeg L KW hij hKW_X
  let eJ := compTowerExcisionJ (i := i) (j := j) L hj.injective KW
  have h3 := comp_right_square (i := i) (j := j) L hi.injective hj.injective hij.injective KW
  have hIsoComp : IsIso (HomologicalComplex.homologyMap
      (openEmbeddingRightLeg ((pullback j.hom).obj L) KW hi.injective ≫
        ComplexTower.limComplexMap eJ) k) := by
    have : IsIso (borelMooreHomologyCoefficientMap
        ((pullbackCompIso i.hom j.hom).hom.app L) k) :=
      borelMooreHomologyCoefficientIso_hom ((pullbackCompIso i.hom j.hom).app L) k ▸
        inferInstanceAs (IsIso (borelMooreHomologyCoefficientIso
          ((pullbackCompIso i.hom j.hom).app L) k).hom)
    have h3H : borelMooreHomologyCoefficientMap ((pullbackCompIso i.hom j.hom).hom.app L) k ≫
        HomologicalComplex.homologyMap (openEmbeddingRightLeg ((pullback j.hom).obj L) KW
          hi.injective ≫ ComplexTower.limComplexMap eJ) k =
        HomologicalComplex.homologyMap (openEmbeddingRightLeg L KW hij.injective) k := by
      rw [← HomologicalComplex.homologyMap_comp, h3]
    have : IsIso (borelMooreHomologyCoefficientMap ((pullbackCompIso i.hom j.hom).hom.app L) k ≫
        HomologicalComplex.homologyMap (openEmbeddingRightLeg ((pullback j.hom).obj L) KW
          hi.injective ≫ ComplexTower.limComplexMap eJ) k) := h3H.symm ▸ inferInstance
    exact IsIso.of_isIso_comp_left
      (borelMooreHomologyCoefficientMap ((pullbackCompIso i.hom j.hom).hom.app L) k) _
  rw [← cancel_mono (HomologicalComplex.homologyMap
    (openEmbeddingRightLeg ((pullback j.hom).obj L) KW hi.injective ≫
      ComplexTower.limComplexMap eJ) k)]
  calc (borelMooreHomologyRestrictOfExhaustion L hj KV' hKV'_X k ≫
          borelMooreHomologyRestrictOfExhaustion ((pullback j.hom).obj L) hi KW hKW_V k) ≫
        HomologicalComplex.homologyMap
          (openEmbeddingRightLeg ((pullback j.hom).obj L) KW hi.injective ≫
            ComplexTower.limComplexMap eJ) k
    _ = borelMooreHomologyRestrictOfExhaustion L hj KV' hKV'_X k ≫
          HomologicalComplex.homologyMap
            (locallyFiniteChainComplexToAmbientTower i ((pullback j.hom).obj L) KW ≫
              ComplexTower.limComplexMap eJ) k := by
        rw [HomologicalComplex.homologyMap_comp, Category.assoc,
          borelMooreHomologyRestrictOfExhaustion_comp_rightLeg_assoc,
          ← HomologicalComplex.homologyMap_comp]
    _ = HomologicalComplex.homologyMap
          (locallyFiniteChainComplexToAmbientTower (i ≫ j) L KW) k := by
        rw [← comp_middle_square L hj.injective KW KV' hsub, HomologicalComplex.homologyMap_comp,
          ← Category.assoc, borelMooreHomologyRestrictOfExhaustion_comp_rightLeg,
          ← HomologicalComplex.homologyMap_comp, comp_left_square]
    _ = (borelMooreHomologyRestrictOfExhaustion L (j := i ≫ j) hij KW hKW_X k ≫
          borelMooreHomologyCoefficientMap ((pullbackCompIso i.hom j.hom).hom.app L) k) ≫
          HomologicalComplex.homologyMap
            (openEmbeddingRightLeg ((pullback j.hom).obj L) KW hi.injective ≫
              ComplexTower.limComplexMap eJ) k := by
        rw [← borelMooreHomologyRestrictOfExhaustion_comp_rightLeg L hij KW hKW_X k, ← h3,
          HomologicalComplex.homologyMap_comp, Category.assoc]

end ExhaustionRestriction


section CanonicalRestriction

variable {V X : TopCat.{v}}

/-- Open restriction along the identity is the canonical coefficient comparison. -/
@[simp]
theorem borelMooreHomologyRestrict_id [T2Space X] [WeaklyLocallyCompactSpace X]
    [SigmaCompactSpace X] (hid : IsOpenEmbedding (TopCat.Hom.hom (𝟙 X)))
    (L : LocalCoefficientSystem.{u, v, max v w} R X) (k : ℕ) :
    borelMooreHomologyRestrict (𝟙 X) hid L k =
      borelMooreHomologyCoefficientMap ((pullbackIdIso X).inv.app L) k := by
  rw [borelMooreHomologyRestrict_eq_ofExhaustion (𝟙 X) hid L (CompactExhaustion.choice X)
    (closure_image_compactExhaustion_subset_range (𝟙 X) (CompactExhaustion.choice X)) k]
  exact borelMooreHomologyRestrictOfExhaustion_id L hid (CompactExhaustion.choice X) _ k

/-- Open restriction is contravariantly functorial for composable open embeddings. -/
@[reassoc]
theorem borelMooreHomologyRestrict_comp [T2Space X] [T2Space V]
    {W : TopCat.{v}} [WeaklyLocallyCompactSpace W] [SigmaCompactSpace W]
    [WeaklyLocallyCompactSpace V] [SigmaCompactSpace V]
    (i : W ⟶ V) (j : V ⟶ X) (hi : IsOpenEmbedding i.hom) (hj : IsOpenEmbedding j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R X) (k : ℕ) :
    borelMooreHomologyRestrict j hj L k ≫
        borelMooreHomologyRestrict i hi ((pullback j.hom).obj L) k =
      borelMooreHomologyRestrict (i ≫ j) (by simpa using hj.comp hi) L k ≫
        borelMooreHomologyCoefficientMap ((pullbackCompIso i.hom j.hom).hom.app L) k := by
  rw [borelMooreHomologyRestrict_eq_ofExhaustion j hj L (CompactExhaustion.choice V)
      (closure_image_compactExhaustion_subset_range j (CompactExhaustion.choice V)) k,
    borelMooreHomologyRestrict_eq_ofExhaustion i hi ((pullback j.hom).obj L)
      (CompactExhaustion.choice W)
      (closure_image_compactExhaustion_subset_range i (CompactExhaustion.choice W)) k,
    borelMooreHomologyRestrict_eq_ofExhaustion (i ≫ j) (by simpa using hj.comp hi) L
      (CompactExhaustion.choice W)
      (closure_image_compactExhaustion_subset_range (i ≫ j) (CompactExhaustion.choice W)) k]
  exact borelMooreHomologyRestrictOfExhaustion_comp L hi hj
    (CompactExhaustion.choice W) (CompactExhaustion.choice V) _ _ _ k

/-- Open restriction is natural in morphisms of local coefficient systems. -/
@[reassoc]
theorem borelMooreHomologyRestrict_naturality [T2Space X] [WeaklyLocallyCompactSpace V]
    [SigmaCompactSpace V] (j : V ⟶ X) (hj : IsOpenEmbedding j.hom)
    {L K : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ K) (k : ℕ) :
    borelMooreHomologyCoefficientMap η k ≫ borelMooreHomologyRestrict j hj K k =
      borelMooreHomologyRestrict j hj L k ≫
        borelMooreHomologyCoefficientMap ((pullback j.hom).map η) k := by
  rw [borelMooreHomologyRestrict_eq_ofExhaustion j hj K (CompactExhaustion.choice V)
      (closure_image_compactExhaustion_subset_range j (CompactExhaustion.choice V)) k,
    borelMooreHomologyRestrict_eq_ofExhaustion j hj L (CompactExhaustion.choice V)
      (closure_image_compactExhaustion_subset_range j (CompactExhaustion.choice V)) k]
  exact borelMooreHomologyRestrictOfExhaustion_naturality hj η (CompactExhaustion.choice V) _ k

end CanonicalRestriction

section DiscreteCheck

private lemma borelMooreHomologyZero_eq_of_isoPi {X : TopCat.{v}} [DiscreteTopology X]
    (L : LocalCoefficientSystem.{u, v, max v w} R X) (x : borelMooreHomology L 0) :
    x = (locallyFiniteChainComplex L).isoHomologyι₀.inv.hom
      (((locallyFiniteChainComplex L).pOpcycles 0).hom
        ((eqToHom (locallyFiniteChainComplex_X L 0).symm).hom
          ((locallyFiniteChainsZeroEquivPi L).symm
            ((borelMooreHomologyZeroIsoPi L).hom.hom x)))) := by
  have hinv := congrArg (fun f ↦ f.hom ((borelMooreHomologyZeroIsoPi L).hom.hom x))
    (borelMooreHomologyZeroIsoPi_inv L)
  have h1 : (borelMooreHomologyZeroIsoPi L).inv.hom
      ((borelMooreHomologyZeroIsoPi L).hom.hom x) = x := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.hom_inv_id]
    rfl
  rw [h1] at hinv
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearEquiv.toModuleIso_inv,
    ModuleCat.hom_ofHom, LinearEquiv.coe_coe] using hinv

private lemma evalZeroRelativeCoeff_comp (P : TopPair.{v})
    (L : LocalCoefficientSystem.{u, v, max v w} R P.fst)
    {C' : ChainComplex (ModuleCat.{max v w} R) ℕ} (φ : C' ⟶ P.twistedChainComplex L)
    (hd0 : (P.twistedChainComplex L).d 1 0 = 0)
    (σ : (TopCat.toSSet.obj P.fst) _⦋0⦌)
    (hσ : ¬Set.range (TopCat.simplexMap σ) ⊆ Set.range P.map) (z : C'.X 0) :
    (((P.twistedChainComplex L).isoHomologyι₀.hom ≫
        ((P.twistedChainComplex L).pOpcyclesIso 1 0 (by simp) hd0).inv ≫
        P.twistedChainComplexCoeff L σ hσ).hom
      ((HomologicalComplex.homologyMap φ 0).hom
        (C'.isoHomologyι₀.inv.hom ((C'.pOpcycles 0).hom z)))) =
      (P.twistedChainComplexCoeff L σ hσ).hom ((φ.f 0).hom z) := by
  have h1 : C'.pOpcycles 0 ≫ C'.isoHomologyι₀.inv ≫ HomologicalComplex.homologyMap φ 0 ≫
      (P.twistedChainComplex L).isoHomologyι₀.hom ≫
      ((P.twistedChainComplex L).pOpcyclesIso 1 0 (by simp) hd0).inv = φ.f 0 := by
    rw [ChainComplex.isoHomologyι₀_inv_naturality_assoc, Iso.inv_hom_id_assoc,
      HomologicalComplex.p_opcyclesMap_assoc, HomologicalComplex.pOpcyclesIso_hom_inv_id,
      Category.comp_id]
  have h2 := congrArg (fun g ↦ g.hom z)
    (congrArg (· ≫ P.twistedChainComplexCoeff L σ hσ) h1)
  simpa only [Category.assoc, ModuleCat.hom_comp, LinearMap.comp_apply] using h2

private lemma twistedChainComplexCoeff_ι_of_eq {X : TopCat.{v}}
    (L : LocalCoefficientSystem.{u, v, max v w} R X) {k : ℕ}
    {σ τ : (TopCat.toSSet.obj X) _⦋k⦌} (h : σ = τ) (z : L.obj (initialVertex σ)) :
    (L.twistedChainComplexCoeff τ).hom ((L.ιTwistedChainComplex k σ).hom z) =
      (eqToHom (congrArg (fun ρ ↦ L.obj (initialVertex ρ)) h)).hom z := by
  subst h
  simp [twistedChainComplexCoeff_ιTwistedChainComplex_apply]

private lemma injectivePairMap_f_zero_comp_coeff {V X : TopCat.{v}}
    (j : V ⟶ X) (hj : Function.Injective j.hom) (L : LocalCoefficientSystem.{u, v, max v w} R X)
    {S : Set V} {v : V}
    (hρ : ¬Set.range (TopCat.simplexMap (TopCat.toSSetObj₀Equiv.symm (j.hom v))) ⊆
      Set.range (TopPair.ofSubset (j.hom '' S)ᶜ).map)
    (hρV : ¬Set.range (TopCat.simplexMap (TopCat.toSSetObj₀Equiv.symm v)) ⊆
      Set.range (TopPair.ofSubset Sᶜ).map) :
    (TopPair.twistedChainComplexMap (injectivePairMap hj S) L).f 0 ≫
        (TopPair.ofSubset (j.hom '' S)ᶜ).twistedChainComplexCoeff L
          (TopCat.toSSetObj₀Equiv.symm (j.hom v)) hρ =
      (TopPair.ofSubset Sᶜ).twistedChainComplexCoeff ((pullback j.hom).obj L)
        (TopCat.toSSetObj₀Equiv.symm v) hρV := by
  have hcore : (twistedChainComplexMap j L).f 0 ≫
      twistedChainComplexCoeff L (TopCat.toSSetObj₀Equiv.symm (j.hom v)) =
      twistedChainComplexCoeff ((pullback j.hom).obj L) (TopCat.toSSetObj₀Equiv.symm v) := by
    refine twistedChainComplex_hom_ext _ fun σ ↦ ModuleCat.hom_ext <| LinearMap.ext fun z ↦ ?_
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, twistedChainComplexMap_f_ι_apply]
    let z' : L.obj (initialVertex ((TopCat.toSSet.map j).app (op ⦋0⦌) σ)) := z
    by_cases hσ : σ = TopCat.toSSetObj₀Equiv.symm v
    · subst hσ
      have hmap : (TopCat.toSSet.map j).app (op ⦋0⦌) (TopCat.toSSetObj₀Equiv.symm v) =
          TopCat.toSSetObj₀Equiv.symm (j.hom v) :=
        TopCat.toSSetObj₀Equiv.injective rfl
      exact (twistedChainComplexCoeff_ι_of_eq L hmap z').trans
        (twistedChainComplexCoeff_ιTwistedChainComplex_apply ((pullback j.hom).obj L)
          (TopCat.toSSetObj₀Equiv.symm v) z).symm
    · have hne : (TopCat.toSSet.map j).app (op ⦋0⦌) σ ≠
          TopCat.toSSetObj₀Equiv.symm (j.hom v) := by
        intro hEq
        exact hσ (TopCat.toSSetObj₀Equiv.injective (hj (by
          simpa using congrArg TopCat.toSSetObj₀Equiv hEq)))
      exact (twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne L hne z').trans
        (twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne
          ((pullback j.hom).obj L) hσ z).symm
  have hpi : (((TopPair.ofSubset Sᶜ).twistedChainComplexπ ((pullback j.hom).obj L)).f 0) ≫
      (TopPair.twistedChainComplexMap (injectivePairMap hj S) L).f 0 ≫
        (TopPair.ofSubset (j.hom '' S)ᶜ).twistedChainComplexCoeff L
          (TopCat.toSSetObj₀Equiv.symm (j.hom v)) hρ =
      (((TopPair.ofSubset Sᶜ).twistedChainComplexπ ((pullback j.hom).obj L)).f 0) ≫
        (TopPair.ofSubset Sᶜ).twistedChainComplexCoeff ((pullback j.hom).obj L)
          (TopCat.toSSetObj₀Equiv.symm v) hρV := by
    have hπ0 : (((TopPair.ofSubset Sᶜ).twistedChainComplexπ ((pullback j.hom).obj L)).f 0) ≫
        (TopPair.twistedChainComplexMap (injectivePairMap hj S) L).f 0 =
        (twistedChainComplexMap j L).f 0 ≫
          ((TopPair.ofSubset (j.hom '' S)ᶜ).twistedChainComplexπ L).f 0 :=
      congrArg (fun φ ↦ φ.f 0)
        (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap (injectivePairMap hj S) L)
    exact (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ _) hπ0).trans <|
        (Category.assoc _ _ _).trans <|
          (congrArg (_ ≫ ·)
            ((TopPair.ofSubset (j.hom '' S)ᶜ).twistedChainComplexπ_f_twistedChainComplexCoeff L
              _ hρ)).trans <|
            hcore.trans
              ((TopPair.ofSubset Sᶜ).twistedChainComplexπ_f_twistedChainComplexCoeff
                ((pullback j.hom).obj L) _ hρV).symm
  refine ModuleCat.hom_ext <| LinearMap.ext fun y ↦ ?_
  obtain ⟨a, rfl⟩ := (TopPair.ofSubset Sᶜ).twistedChainComplexπ_f_surjective
    ((pullback j.hom).obj L) y
  exact congrArg (fun φ ↦ φ.hom a) hpi

private lemma twistedChainComplex_d_one_zero_eq_zero_ofSubset {X : TopCat.{v}}
    [DiscreteTopology X] (L : LocalCoefficientSystem.{u, v, max v w} R X) (S : Set X) :
    ((TopPair.ofSubset S).twistedChainComplex L).d 1 0 = 0 := by
  refine ModuleCat.hom_ext <| LinearMap.ext fun y ↦ ?_
  obtain ⟨a, rfl⟩ := (TopPair.ofSubset S).twistedChainComplexπ_f_surjective L y
  have h0 : (L.twistedChainComplex.d 1 0).hom a = 0 := by
    rw [twistedChainComplex_d_one_zero_eq_zero L]
    rfl
  exact (congrArg (fun f ↦ f.hom a)
    (((TopPair.ofSubset S).twistedChainComplexπ L).comm 1 0)).trans <|
    (congrArg (((TopPair.ofSubset S).twistedChainComplexπ L).f 0).hom h0).trans (map_zero _)

private lemma borelMooreHomologyRestrict_zero_comp_toRelative {V X : TopCat.{v}} [T2Space X]
    [WeaklyLocallyCompactSpace V] [SigmaCompactSpace V] (j : V ⟶ X) (hj : IsOpenEmbedding j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R X) (n : ℕ) :
    borelMooreHomologyRestrict j hj L 0 ≫
      HomologicalComplex.homologyMap
        ((TopPair.ofSubset (CompactExhaustion.choice V n)ᶜ).locallyFiniteChainComplexToRelative
            ((pullback j.hom).obj L)
            ((CompactExhaustion.choice V).isCompact n).compl_range_ofSubset_compl_map ≫
          TopPair.twistedChainComplexMap
            (injectivePairMap hj.injective (CompactExhaustion.choice V n)) L) 0 =
      HomologicalComplex.homologyMap
        (TopPair.locallyFiniteChainComplexToRelative
          (TopPair.ofSubset (j.hom '' CompactExhaustion.choice V n)ᶜ) L
          (((CompactExhaustion.choice V).isCompact n).image
            j.hom.continuous).compl_range_ofSubset_compl_map) 0 := by
  let K := CompactExhaustion.choice V
  rw [borelMooreHomologyRestrict_eq_ofExhaustion j hj L K
    (closure_image_compactExhaustion_subset_range j K) 0]
  exact (congrArg (borelMooreHomologyRestrictOfExhaustion L hj K
      (closure_image_compactExhaustion_subset_range j K) 0 ≫ ·)
    ((congrArg (fun φ ↦ HomologicalComplex.homologyMap φ 0)
        (openEmbeddingRightLeg_comp_limComplexπ L K hj.injective n)).symm.trans
      (HomologicalComplex.homologyMap_comp _ _ 0))).trans <|
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ _)
        (borelMooreHomologyRestrictOfExhaustion_comp_rightLeg L hj K
          (closure_image_compactExhaustion_subset_range j K) 0)).trans <|
        (HomologicalComplex.homologyMap_comp _ _ 0).symm.trans
          (congrArg (fun φ ↦ HomologicalComplex.homologyMap φ 0)
            (locallyFiniteChainComplexToAmbientTower_comp_limComplexπ j L K n))

/-- **Discrete check.** On a discrete space in degree zero, open restriction along an open
embedding `j : V ⟶ X` corresponds under `borelMooreHomologyZeroIsoPi` to precomposing families
of point coefficients with `j`. -/
theorem borelMooreHomologyRestrict_zero_comp_isoPi {V X : TopCat.{v}}
    [DiscreteTopology X] [DiscreteTopology V] [SigmaCompactSpace V]
    (j : V ⟶ X) (hj : IsOpenEmbedding j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R X)
    (x : borelMooreHomology L 0) (v : V) :
    (borelMooreHomologyZeroIsoPi ((pullback j.hom).obj L)).hom.hom
        ((borelMooreHomologyRestrict j hj L 0).hom x) v =
      (borelMooreHomologyZeroIsoPi L).hom.hom x (j.hom v) := by
  let K := CompactExhaustion.choice V
  obtain ⟨n, hn⟩ := K.exists_mem v
  have hρ : ¬Set.range (TopCat.simplexMap (TopCat.toSSetObj₀Equiv.symm (j.hom v))) ⊆
      Set.range (TopPair.ofSubset (j.hom '' K n)ᶜ).map :=
    TopPair.not_range_simplexMap_subset_range_ofSubset_compl_map_iff.2
      ⟨j.hom v, ⟨toTopInitialVertex _, rfl⟩, ⟨v, hn, rfl⟩⟩
  have hρV : ¬Set.range (TopCat.simplexMap (TopCat.toSSetObj₀Equiv.symm v)) ⊆
      Set.range (TopPair.ofSubset (K n)ᶜ).map :=
    TopPair.not_range_simplexMap_subset_range_ofSubset_compl_map_iff.2
      ⟨v, ⟨toTopInitialVertex _, rfl⟩, hn⟩
  have hd0 := twistedChainComplex_d_one_zero_eq_zero_ofSubset L (j.hom '' K n)ᶜ
  have hzigH := borelMooreHomologyRestrict_zero_comp_toRelative j hj L n
  let eval := ((TopPair.ofSubset (j.hom '' K n)ᶜ).twistedChainComplex L).isoHomologyι₀.hom ≫
    (((TopPair.ofSubset (j.hom '' K n)ᶜ).twistedChainComplex L).pOpcyclesIso 1 0
      (by simp) hd0).inv ≫
    (TopPair.ofSubset (j.hom '' K n)ᶜ).twistedChainComplexCoeff L
      (TopCat.toSSetObj₀Equiv.symm (j.hom v)) hρ
  have hLHS : eval.hom ((HomologicalComplex.homologyMap
        ((TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative ((pullback j.hom).obj L)
            (K.isCompact n).compl_range_ofSubset_compl_map ≫
          TopPair.twistedChainComplexMap (injectivePairMap hj.injective (K n)) L) 0).hom
      ((borelMooreHomologyRestrict j hj L 0).hom x)) =
      (borelMooreHomologyZeroIsoPi ((pullback j.hom).obj L)).hom.hom
        ((borelMooreHomologyRestrict j hj L 0).hom x) v := by
    conv_lhs => rw [borelMooreHomologyZero_eq_of_isoPi ((pullback j.hom).obj L)
      ((borelMooreHomologyRestrict j hj L 0).hom x)]
    have hc := (Category.assoc _ _ _).trans <| congrArg
      (((TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative ((pullback j.hom).obj L)
          (K.isCompact n).compl_range_ofSubset_compl_map).f 0 ≫ ·)
      (injectivePairMap_f_zero_comp_coeff j hj.injective L hρ hρV)
    let y0 : (((pullback j.hom).obj L).locallyFiniteChainComplex).X 0 :=
      (eqToHom (locallyFiniteChainComplex_X ((pullback j.hom).obj L) 0).symm).hom
        (((pullback j.hom).obj L).locallyFiniteChainsZeroEquivPi.symm
          ((borelMooreHomologyZeroIsoPi ((pullback j.hom).obj L)).hom.hom
            ((borelMooreHomologyRestrict j hj L 0).hom x)))
    exact (evalZeroRelativeCoeff_comp
        (TopPair.ofSubset (j.hom '' K n)ᶜ) L _ hd0 _ hρ y0).trans <|
      (congrArg (fun f ↦ f.hom y0) hc).trans <|
        (TopPair.twistedChainComplexCoeff_locallyFiniteChainComplexToRelative_f_apply
          (TopPair.ofSubset (K n)ᶜ) ((pullback j.hom).obj L)
          (K.isCompact n).compl_range_ofSubset_compl_map _ _ hρV).trans
          (locallyFiniteChainsZeroEquivPi_symm_apply ((pullback j.hom).obj L) _ v)
  have hRHS : eval.hom ((HomologicalComplex.homologyMap
        ((TopPair.ofSubset (j.hom '' K n)ᶜ).locallyFiniteChainComplexToRelative L
          ((K.isCompact n).image j.hom.continuous).compl_range_ofSubset_compl_map) 0).hom x) =
      (borelMooreHomologyZeroIsoPi L).hom.hom x (j.hom v) := by
    conv_lhs => rw [borelMooreHomologyZero_eq_of_isoPi L x]
    exact (evalZeroRelativeCoeff_comp (TopPair.ofSubset (j.hom '' K n)ᶜ) L _ hd0 _ hρ _).trans <|
      (TopPair.twistedChainComplexCoeff_locallyFiniteChainComplexToRelative_f_apply
        (TopPair.ofSubset (j.hom '' K n)ᶜ) L
        ((K.isCompact n).image j.hom.continuous).compl_range_ofSubset_compl_map _ _ hρ).trans
        (locallyFiniteChainsZeroEquivPi_symm_apply L _ (j.hom v))
  exact hLHS.symm.trans <| (congrArg (fun f ↦ eval.hom (f.hom x)) hzigH).trans hRHS

/-- **Check: restricting a countable discrete set to its even points deletes the odd
coordinates.** -/
example (L : LocalCoefficientSystem.{u, 0, w} R (TopCat.of ℕ))
    (x : borelMooreHomology L 0) (n : Set.ofPred Even) :
    (borelMooreHomologyZeroIsoPi
      ((pullback (TopCat.ofHom (ContinuousMap.subtypeVal (Set.ofPred Even))).hom).obj L)).hom.hom
        ((borelMooreHomologyRestrict
          (TopCat.ofHom (ContinuousMap.subtypeVal (Set.ofPred Even)))
          (isOpen_discrete _).isOpenEmbedding_subtypeVal L 0).hom x) n =
      (borelMooreHomologyZeroIsoPi L).hom.hom x n.1 :=
  borelMooreHomologyRestrict_zero_comp_isoPi
    (TopCat.ofHom (ContinuousMap.subtypeVal (Set.ofPred Even)))
    (isOpen_discrete _).isOpenEmbedding_subtypeVal L x n

end DiscreteCheck

end TauCeti.LocalCoefficientSystem
