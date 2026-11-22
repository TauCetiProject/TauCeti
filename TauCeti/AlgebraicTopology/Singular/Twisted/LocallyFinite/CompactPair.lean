/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.DeformationRetract
public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Restriction

/-!
# Compact pairs and Borel–Moore homology of complements

For closed `A` in a Hausdorff space `X`, `relativeToOpenRestrictionLim` and inverse excision define
`twistedHomologyToBorelMooreHomologyCompl : H_j(X, A; L) ⟶ H_j^{BM}(X \ A; L|_{X \ A})`,
exhaustion-independent, natural in `L`, closed-subset enlargement, proper complement pair maps, and
open restriction; it is an isomorphism on compact Hausdorff `X` when `A` has a countable cofinal
open neighbourhood family with quasi-isomorphic triple quotients (e.g. deformation retractions).
-/

public section
noncomputable section
open CategoryTheory Limits Opposite Topology
universe u v w
namespace TauCeti.LocalCoefficientSystem
variable {R : Type u} [Ring R]

section ComparisonMap
variable {X : TopCat.{v}}
section RelativeToLim
variable (A : Set X) (L : LocalCoefficientSystem.{u, v, max v w} R X)
  (K : CompactExhaustion (Aᶜ : Set X))

private def relativeOpenRestrictionCone :
    Cone (openRestrictionTower (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K) where
  pt := (TopPair.ofSubset A).twistedChainComplex L
  π := NatTrans.ofOpSequence
    (fun n ↦ (TopTriple.ofSubset (Set.subset_compl_comm.2
      (Subtype.coe_image_subset Aᶜ (K n)))).twistedChainComplexTotalToOuter L)
    fun n ↦ (TopPair.ofSubset A).twistedChainComplex_hom_ext L <| by
      erw [Category.id_comp, TopTriple.twistedChainComplexπ_comp_totalToOuter,
        TopTriple.twistedChainComplexπ_comp_totalToOuter_assoc,
        twistedChainComplexπ_comp_complChainComplexTower_map]; rfl
/-- Canonical chain map from `C(X, A; L)` to `(openRestrictionTower _ L K).limComplex`. -/
def relativeToOpenRestrictionLim :
    (TopPair.ofSubset A).twistedChainComplex L ⟶
      (openRestrictionTower (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K).limComplex :=
  (openRestrictionTower (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K).isLimitLimComplexCone.lift
    (relativeOpenRestrictionCone A L K)
@[reassoc (attr := simp)] lemma relativeToOpenRestrictionLim_comp_π (n : ℕ) :
    relativeToOpenRestrictionLim A L K ≫
        (openRestrictionTower (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K).limComplexπ n =
      (TopTriple.ofSubset (Set.subset_compl_comm.2
        (Subtype.coe_image_subset Aᶜ (K n)))).twistedChainComplexTotalToOuter L :=
  ((openRestrictionTower (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L
    K).isLimitLimComplexCone.fac (relativeOpenRestrictionCone A L K) (op n)).trans
    (rfl : (relativeOpenRestrictionCone A L K).π.app (op n) = _)
/-- On absolute chains, `relativeToOpenRestrictionLim` agrees with locally finite restriction. -/
@[reassoc (attr := simp)] theorem twistedChainComplexπ_comp_relativeToOpenRestrictionLim :
    (TopPair.ofSubset A).twistedChainComplexπ L ≫ relativeToOpenRestrictionLim A L K =
      toLocallyFiniteChainComplex L ≫ locallyFiniteChainComplexToOpenRestrictionLim
        (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K :=
  (openRestrictionTower (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K).limComplex_hom_ext
    fun n ↦ (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (relativeToOpenRestrictionLim_comp_π A L K n)).trans <|
        ((TopTriple.ofSubset (Set.subset_compl_comm.2
          (Subtype.coe_image_subset Aᶜ (K n)))).twistedChainComplexπ_comp_totalToOuter L).trans <|
          ((TopPair.ofSubset (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ) ''
            K n)ᶜ).toLocallyFiniteChainComplex_comp_locallyFiniteChainComplexToRelative
              L _).symm.trans <| (congrArg (toLocallyFiniteChainComplex L ≫ ·)
                (locallyFiniteChainComplexToComplLim_comp_π L
                  (fun n ↦ TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ) '' K n) _ _ n).symm).trans
                (Category.assoc _ _ _).symm
end RelativeToLim

private lemma comp_relativeToOpenRestrictionLim_eq {X₁ X₂ : TopCat.{v}} {A₁ : Set X₁} {A₂ : Set X₂}
    {L₁ : LocalCoefficientSystem.{u, v, max v w} R X₁}
    {L₂ : LocalCoefficientSystem.{u, v, max v w} R X₂}
    {K₁ : CompactExhaustion (A₁ᶜ : Set X₁)} {K₂ : CompactExhaustion (A₂ᶜ : Set X₂)}
    (g : L₁.twistedChainComplex ⟶ L₂.twistedChainComplex)
    (p : (TopPair.ofSubset A₁).twistedChainComplex L₁ ⟶
      (TopPair.ofSubset A₂).twistedChainComplex L₂)
    (q : openRestrictionTower (TopCat.ofHom (ContinuousMap.subtypeVal A₁ᶜ)) L₁ K₁ ⟶
      openRestrictionTower (TopCat.ofHom (ContinuousMap.subtypeVal A₂ᶜ)) L₂ K₂)
    (hp : (TopPair.ofSubset A₁).twistedChainComplexπ L₁ ≫ p =
      g ≫ (TopPair.ofSubset A₂).twistedChainComplexπ L₂)
    (hq : ∀ n, (TopPair.ofSubset (TopCat.ofHom (ContinuousMap.subtypeVal A₁ᶜ) ''
        K₁ n)ᶜ).twistedChainComplexπ L₁ ≫ q.app (op n) =
      g ≫ (TopPair.ofSubset (TopCat.ofHom (ContinuousMap.subtypeVal A₂ᶜ) ''
        K₂ n)ᶜ).twistedChainComplexπ L₂) :
    p ≫ relativeToOpenRestrictionLim A₂ L₂ K₂ =
      relativeToOpenRestrictionLim A₁ L₁ K₁ ≫ ComplexTower.limComplexMap q :=
  (openRestrictionTower (TopCat.ofHom (ContinuousMap.subtypeVal A₂ᶜ)) L₂ K₂).limComplex_hom_ext
    fun n ↦ (TopPair.ofSubset A₁).twistedChainComplex_hom_ext L₁ <|
      let h₁ := (TopTriple.ofSubset (Set.subset_compl_comm.2
        (Subtype.coe_image_subset A₁ᶜ (K₁ n)))).twistedChainComplexπ_comp_totalToOuter L₁
      let h₂ := (TopTriple.ofSubset (Set.subset_compl_comm.2
        (Subtype.coe_image_subset A₂ᶜ (K₂ n)))).twistedChainComplexπ_comp_totalToOuter L₂
      ((congrArg (_ ≫ ·) <| (Category.assoc _ _ _).trans <| congrArg (_ ≫ ·)
        (relativeToOpenRestrictionLim_comp_π A₂ L₂ K₂ n)).trans <|
        (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hp).trans <|
          (Category.assoc _ _ _).trans <| congrArg (_ ≫ ·) h₂).trans
        ((congrArg (_ ≫ ·) <| (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·)
          (ComplexTower.limComplexMap_comp_π q n)).trans <| (Category.assoc _ _ _).symm.trans <|
          congrArg (· ≫ _) (relativeToOpenRestrictionLim_comp_π A₁ L₁ K₁ n)).trans <|
          (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) h₁).trans (hq n)).symm

@[reassoc (attr := simp)] lemma relativeToOpenRestrictionLim_comp_limComplexMap
    (L : LocalCoefficientSystem.{u, v, max v w} R X) {A : Set X}
    {K K' : CompactExhaustion (Aᶜ : Set X)} (h : ∀ n, K n ⊆ K' n) :
    relativeToOpenRestrictionLim A L K' ≫ ComplexTower.limComplexMap
        (openRestrictionTowerMap (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L h) =
      relativeToOpenRestrictionLim A L K :=
  (comp_relativeToOpenRestrictionLim_eq (𝟙 _) (𝟙 _)
    (openRestrictionTowerMap (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L h)
    ((Category.comp_id _).trans (Category.id_comp _).symm) fun n ↦
      (twistedChainComplexπ_comp_complChainComplexTowerMap_app L
        (fun n ↦ Set.image_mono (K.subset_succ n)) (fun n ↦ Set.image_mono (K'.subset_succ n))
        (fun n ↦ Set.image_mono (h n)) n).trans (Category.id_comp _).symm).symm.trans
    (Category.id_comp _)
@[reassoc] lemma twistedChainComplexCoefficientMap_comp_relativeToOpenRestrictionLim
    (A : Set X) (K : CompactExhaustion (Aᶜ : Set X))
    {L L' : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ L') :
    (TopPair.ofSubset A).twistedChainComplexCoefficientMap η ≫
        relativeToOpenRestrictionLim A L' K =
      relativeToOpenRestrictionLim A L K ≫ ComplexTower.limComplexMap
        (openRestrictionTowerCoefficientMap (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) K η) :=
  comp_relativeToOpenRestrictionLim_eq (twistedChainComplexCoefficientMap η) _ _
    ((TopPair.ofSubset A).twistedChainComplexπ_comp_twistedChainComplexCoefficientMap η) fun n ↦
      (congrArg (_ ≫ ·) (complChainComplexTowerCoefficientMap_app _ _ η n)).trans
        ((TopPair.ofSubset _).twistedChainComplexπ_comp_twistedChainComplexCoefficientMap η)

section T2
variable [T2Space X] {A : Set X} (hA : IsClosed A)
  (L : LocalCoefficientSystem.{u, v, max v w} R X) (K : CompactExhaustion (Aᶜ : Set X))

/-- **Comparison morphism `H_j(X, A; L) ⟶ H_j^{BM}(X \ A; L|_{X \ A})`** for exhaustion `K`. -/
def twistedHomologyToBorelMooreHomologyComplOfExhaustion (j : ℕ) :
    (TopPair.ofSubset A).twistedHomology L j ⟶
      borelMooreHomology ((pullback (X := TopCat.of (Aᶜ : Set X))
        (ContinuousMap.subtypeVal Aᶜ)).obj L) j :=
  have := isIso_homologyMap_locallyFiniteChainComplexOpenRestrictionExcision
    (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K hA.isOpen_compl.isOpenEmbedding_subtypeVal j
  HomologicalComplex.homologyMap (relativeToOpenRestrictionLim A L K) j ≫
    inv (HomologicalComplex.homologyMap (locallyFiniteChainComplexOpenRestrictionExcision
      (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K
      hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective) j)
@[reassoc (attr := simp)]
theorem twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap (j : ℕ) :
    twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j ≫
        HomologicalComplex.homologyMap (locallyFiniteChainComplexOpenRestrictionExcision
          (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K
          hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective) j =
      HomologicalComplex.homologyMap (relativeToOpenRestrictionLim A L K) j := by
  have := isIso_homologyMap_locallyFiniteChainComplexOpenRestrictionExcision
    (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K hA.isOpen_compl.isOpenEmbedding_subtypeVal j
  simp [twistedHomologyToBorelMooreHomologyComplOfExhaustion]
/-- Uniqueness criterion for `twistedHomologyToBorelMooreHomologyComplOfExhaustion`. -/
theorem eq_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion {M : ModuleCat.{max v w} R}
    {j : ℕ} {g : M ⟶ (TopPair.ofSubset A).twistedHomology L j}
    {f : M ⟶ borelMooreHomology ((pullback (X := TopCat.of (Aᶜ : Set X))
      (ContinuousMap.subtypeVal Aᶜ)).obj L) j}
    (hf : f ≫ HomologicalComplex.homologyMap (locallyFiniteChainComplexOpenRestrictionExcision
        (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K
        hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective) j =
      g ≫ HomologicalComplex.homologyMap (relativeToOpenRestrictionLim A L K) j) :
    f = g ≫ twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j := by
  have := isIso_homologyMap_locallyFiniteChainComplexOpenRestrictionExcision
    (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K hA.isOpen_compl.isOpenEmbedding_subtypeVal j
  rw [← cancel_mono (HomologicalComplex.homologyMap
      (locallyFiniteChainComplexOpenRestrictionExcision
        (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K
        hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective) j),
    Category.assoc, twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap, hf]

private lemma twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq_of_subset
    {K' : CompactExhaustion (Aᶜ : Set X)} (h : ∀ n, K n ⊆ K' n) (j : ℕ) :
    twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K' j =
      twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j := by
  refine (eq_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K (g := 𝟙 _) ?_).trans
    (Category.id_comp _)
  rw [Category.id_comp, ← locallyFiniteChainComplexOpenRestrictionExcision_comp_limComplexMap
      (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L
      hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective h, HomologicalComplex.homologyMap_comp,
    twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap_assoc,
    ← HomologicalComplex.homologyMap_comp, relativeToOpenRestrictionLim_comp_limComplexMap]
/-- **Exhaustion independence** of `twistedHomologyToBorelMooreHomologyComplOfExhaustion`. -/
theorem twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq
    (K' : CompactExhaustion (Aᶜ : Set X)) (j : ℕ) :
    twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j =
      twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K' j :=
  (twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq_of_subset hA L K
    (CompactExhaustion.subset_sup_left K K') j).symm.trans
    (twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq_of_subset hA L K'
      (CompactExhaustion.subset_sup_right K K') j)
/-- **Naturality in local coefficients** for the compact-pair comparison map. -/
@[reassoc] theorem twistedHomologyToBorelMooreHomologyComplOfExhaustion_naturality
    {L' : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ L') (j : ℕ) :
    (TopPair.ofSubset A).twistedHomologyCoefficientMap η j ≫
        twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L' K j =
      twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j ≫
        borelMooreHomologyCoefficientMap
          ((pullback (X := TopCat.of (Aᶜ : Set X)) (ContinuousMap.subtypeVal Aᶜ)).map η) j := by
  symm; refine eq_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L' K ?_
  have hchain : locallyFiniteChainComplexCoefficientMap
        ((pullback (X := TopCat.of (Aᶜ : Set X)) (ContinuousMap.subtypeVal Aᶜ)).map η) ≫
      locallyFiniteChainComplexOpenRestrictionExcision (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ))
        L' K hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective =
      locallyFiniteChainComplexOpenRestrictionExcision (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ))
        L K hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective ≫
        ComplexTower.limComplexMap
          (openRestrictionTowerCoefficientMap (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) K η) :=
    locallyFiniteChainComplexCoefficientMap_comp_openRestrictionExcision
      (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) K
      hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective η
  rw [Category.assoc, ← HomologicalComplex.homologyMap_comp, hchain,
    HomologicalComplex.homologyMap_comp,
    twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap_assoc,
    ← HomologicalComplex.homologyMap_comp,
    ← twistedChainComplexCoefficientMap_comp_relativeToOpenRestrictionLim,
    HomologicalComplex.homologyMap_comp]

/-- **Compatibility with closed-subset enlargement:** for closed `A ⊆ B`, the comparison morphism
intertwines the triple quotient with open restriction along `Bᶜ ↪ Aᶜ`. -/
@[reassoc]
theorem twistedHomologyTotalToOuter_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion
    {B : Set X} (hB : IsClosed B) (hAB : A ⊆ B) (K_B : CompactExhaustion (Bᶜ : Set X)) (j : ℕ) :
    (TopTriple.ofSubset hAB).twistedHomologyTotalToOuter L j ≫
        twistedHomologyToBorelMooreHomologyComplOfExhaustion hB L K_B j ≫
          borelMooreHomologyCoefficientMap
            ((pullbackCompIso (X := TopCat.of (Bᶜ : Set X)) (Y := TopCat.of (Aᶜ : Set X))
              (ContinuousMap.inclusion (Set.compl_subset_compl.2 hAB))
              (ContinuousMap.subtypeVal Aᶜ)).hom.app L) j =
      twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j ≫
        borelMooreHomologyOpenRestrictionOfExhaustion
          (TopCat.ofHom (ContinuousMap.inclusion (Set.compl_subset_compl.2 hAB)))
          (IsOpenEmbedding.of_comp (ContinuousMap.inclusion (Set.compl_subset_compl.2 hAB))
            hA.isOpen_compl.isOpenEmbedding_subtypeVal hB.isOpen_compl.isOpenEmbedding_subtypeVal)
          ((pullback (X := TopCat.of (Aᶜ : Set X)) (ContinuousMap.subtypeVal Aᶜ)).obj L) K_B j := by
  let iA : TopCat.of (Aᶜ : Set X) ⟶ X := TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)
  let ι : TopCat.of (Bᶜ : Set X) ⟶ TopCat.of (Aᶜ : Set X) :=
    TopCat.ofHom (ContinuousMap.inclusion (Set.compl_subset_compl.2 hAB))
  have hiA := hA.isOpen_compl.isOpenEmbedding_subtypeVal
  have hι : IsOpenEmbedding ι.hom :=
    IsOpenEmbedding.of_comp ι.hom hiA hB.isOpen_compl.isOpenEmbedding_subtypeVal
  let K' := K.supImage ι.hom.continuous hι.isOpenMap K_B
  rw [twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq hA L K K' j]
  have hBA := K.image_subset_supImage ι.hom.continuous hι.isOpenMap K_B
  have hXA (n : ℕ) : (ι ≫ iA) '' K_B n ⊆ iA '' K' n := by
    rw [TopCat.coe_comp, Set.image_comp]; exact Set.image_mono (hBA n)
  have hRel : (TopTriple.ofSubset hAB).twistedChainComplexTotalToOuter L ≫
        relativeToOpenRestrictionLim B L K_B =
      relativeToOpenRestrictionLim A L K' ≫
        ComplexTower.limComplexMap (complChainComplexTowerMap L _ _ hXA) :=
    comp_relativeToOpenRestrictionLim_eq (𝟙 _) _ _
      (((TopTriple.ofSubset hAB).twistedChainComplexπ_comp_totalToOuter L).trans
        (Category.id_comp _).symm)
      fun n ↦ (twistedChainComplexπ_comp_complChainComplexTowerMap_app L _ _ hXA n).trans
        (Category.id_comp _).symm
  suffices hmain : twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K' j ≫
        borelMooreHomologyOpenRestrictionOfExhaustion ι hι ((pullback iA.hom).obj L) K_B j ≫
          borelMooreHomologyCoefficientMap ((pullbackCompIso ι.hom iA.hom).inv.app L) j =
      (TopTriple.ofSubset hAB).twistedHomologyTotalToOuter L j ≫
        twistedHomologyToBorelMooreHomologyComplOfExhaustion hB L K_B j by
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hmain.symm)).trans <|
      (Category.assoc _ _ _).trans <| congrArg (_ ≫ ·) <| (Category.assoc _ _ _).trans <|
        (congrArg (_ ≫ ·) <| (borelMooreHomologyCoefficientMap_comp _ _ j).symm.trans <|
          (congrArg (borelMooreHomologyCoefficientMap · j)
            ((pullbackCompIso ι.hom iA.hom).inv_hom_id_app L)).trans
            (borelMooreHomologyCoefficientMap_id j)).trans (Category.comp_id _)
  refine eq_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion hB L K_B ?_
  have hAcomp := twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap hA L K' j
  exact (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans <|
    borelMooreHomologyOpenRestrictionOfExhaustion_comp_excision_of_subset
      ι iA hι hiA L K_B K' hBA hXA j)).trans <| (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ _) hAcomp).trans <| (HomologicalComplex.homologyMap_comp _ _ j).symm.trans <|
        (congrArg (HomologicalComplex.homologyMap · j) hRel.symm).trans
          (HomologicalComplex.homologyMap_comp _ _ j)

/-- **Naturality under maps of pairs with proper restriction to complements.** -/
@[reassoc] theorem twistedHomologyMap_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion
    {X' : TopCat.{v}} [T2Space X'] {A' : Set X'} (hA' : IsClosed A')
    (φ : TopPair.ofSubset A' ⟶ TopPair.ofSubset A)
    (fCompl : TopCat.of (A'ᶜ : Set X') ⟶ TopCat.of (Aᶜ : Set X)) (hfCompl : IsProperMap fCompl.hom)
    (hw : fCompl ≫ TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ) =
      TopCat.ofHom (ContinuousMap.subtypeVal A'ᶜ) ≫ TopPair.Hom.fst φ)
    (K' : CompactExhaustion (A'ᶜ : Set X')) (j : ℕ) :
    TopPair.twistedHomologyMap φ L j ≫
        twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j =
      twistedHomologyToBorelMooreHomologyComplOfExhaustion hA'
          ((pullback (TopPair.Hom.fst φ).hom).obj L) K' j ≫
        borelMooreHomologyCoefficientMap
          (((pullbackCompIso (TopCat.ofHom (ContinuousMap.subtypeVal A'ᶜ)).hom
              (TopPair.Hom.fst φ).hom).app L).symm ≪≫
            eqToIso (congrArg (fun k : TopCat.of (A'ᶜ : Set X') ⟶ X ↦
              (pullback k.hom).obj L) hw.symm) ≪≫
            (pullbackCompIso fCompl.hom
              (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)).hom).app L).hom j ≫
        borelMooreHomologyMap fCompl hfCompl
          ((pullback (X := TopCat.of (Aᶜ : Set X)) (ContinuousMap.subtypeVal Aᶜ)).obj L) j := by
  let iA : TopCat.of (Aᶜ : Set X) ⟶ X := TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)
  let iA' : TopCat.of (A'ᶜ : Set X') ⟶ X' := TopCat.ofHom (ContinuousMap.subtypeVal A'ᶜ)
  let f : X' ⟶ X := TopPair.Hom.fst φ; let K'' := K'.supPreimage hfCompl K
  refine Eq.trans ?_ (congrArg (· ≫ _) (twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq
    hA' ((pullback f.hom).obj L) K' K'' j).symm)
  have hfCompl_maps (n : ℕ) : Set.MapsTo fCompl (K'' n)ᶜ (K n)ᶜ :=
    fun _ hx hfx ↦ hx (K'.preimage_subset_supPreimage hfCompl K n hfx)
  have hf_maps (n : ℕ) : Set.MapsTo f (iA' '' K'' n)ᶜ (iA '' K n)ᶜ := by
    rintro x hx ⟨y, hyK, hyx⟩; have hyx' : y.val = f x := hyx
    have hxA' : x ∉ A' := fun hx' ↦ y.property <| by
      have h := congrArg (fun k : TopCat.of (A' : Set X') ⟶ X ↦ k ⟨x, hx'⟩) (TopPair.Hom.w φ)
      exact hyx'.symm ▸ h ▸ (TopPair.Hom.snd φ ⟨x, hx'⟩).property
    have hfy : fCompl ⟨x, hxA'⟩ = y := Subtype.ext <|
      (congrArg (fun k : TopCat.of (A'ᶜ : Set X') ⟶ X ↦ k ⟨x, hxA'⟩) hw).trans hyx'.symm
    exact hx ⟨⟨x, hxA'⟩, K'.preimage_subset_supPreimage hfCompl K n (by simpa [hfy] using hyK), rfl⟩
  have hRel : TopPair.twistedChainComplexMap φ L ≫ relativeToOpenRestrictionLim A L K =
      relativeToOpenRestrictionLim A' ((pullback f.hom).obj L) K'' ≫
        ComplexTower.limComplexMap (complChainComplexTowerPairMap f L _ _ hf_maps) :=
    comp_relativeToOpenRestrictionLim_eq (twistedChainComplexMap f L) _ _
      (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap φ L) fun n ↦
        twistedChainComplexπ_comp_complChainComplexTowerPairMap_app f L _ _ hf_maps n
  symm; refine eq_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K ?_
  have hsq := (congrArg (_ ≫ ·) (HomologicalComplex.homologyMap_comp _ _ j).symm).trans <|
    (HomologicalComplex.homologyMap_comp _ _ j).symm.trans <|
      (congrArg (HomologicalComplex.homologyMap · j) <|
        locallyFiniteChainComplexOpenRestrictionExcision_naturality_square iA
          hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective iA'
          hA'.isOpen_compl.isOpenEmbedding_subtypeVal.injective f fCompl hfCompl hw L K K''
          hfCompl_maps hf_maps).trans (HomologicalComplex.homologyMap_comp _ _ j)
  have hA'comp := twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap
    hA' ((pullback f.hom).obj L) K'' j
  exact (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans hsq)).trans
    <| (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hA'comp).trans <|
      (HomologicalComplex.homologyMap_comp _ _ j).symm.trans <|
        (congrArg (HomologicalComplex.homologyMap · j) hRel.symm).trans
          (HomologicalComplex.homologyMap_comp _ _ j)

/-- **Compatibility with open restriction** on absolute twisted homology of `X`. -/
@[reassoc (attr := simp)]
theorem twistedHomologyπ_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion (j : ℕ) :
    (TopPair.ofSubset A).twistedHomologyπ L j ≫
        twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j =
      twistedHomologyToBorelMooreHomology L j ≫
        borelMooreHomologyOpenRestrictionOfExhaustion
          (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ))
          hA.isOpen_compl.isOpenEmbedding_subtypeVal L K j := by
  refine eq_comp_borelMooreHomologyOpenRestrictionOfExhaustion
    (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) hA.isOpen_compl.isOpenEmbedding_subtypeVal L K ?_
  rw [Category.assoc, twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap,
    ← HomologicalComplex.homologyMap_comp, twistedChainComplexπ_comp_relativeToOpenRestrictionLim]
  exact HomologicalComplex.homologyMap_comp _ _ j
/-- On compact Hausdorff `X`, open restriction to `X \ A` factors through `H_j(X, A; L)`. -/
theorem borelMooreHomologyOpenRestrictionOfExhaustion_subtypeVal_compl_eq [CompactSpace X]
    (j : ℕ) :
    borelMooreHomologyOpenRestrictionOfExhaustion
        (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ))
        hA.isOpen_compl.isOpenEmbedding_subtypeVal L K j =
      (twistedHomologyIsoBorelMooreHomology L j).inv ≫
        (TopPair.ofSubset A).twistedHomologyπ L j ≫
          twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j :=
  (Iso.inv_hom_id_assoc (twistedHomologyIsoBorelMooreHomology L j) _).symm.trans <|
    (congrArg (fun g ↦ (twistedHomologyIsoBorelMooreHomology L j).inv ≫ g ≫ _)
      (twistedHomologyIsoBorelMooreHomology_hom L)).trans (congrArg (_ ≫ ·)
        (twistedHomologyπ_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j).symm)

section Choice
variable [WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)]
/-- **Comparison morphism `H_j(X, A; L) ⟶ H_j^{BM}(X \ A; L|_{X \ A})`** for weakly locally
compact `σ`-compact `X \ A`. -/
def twistedHomologyToBorelMooreHomologyCompl (j : ℕ) :
    (TopPair.ofSubset A).twistedHomology L j ⟶
      borelMooreHomology ((pullback (X := TopCat.of (Aᶜ : Set X))
        (ContinuousMap.subtypeVal Aᶜ)).obj L) j :=
  twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L
    (CompactExhaustion.choice (Aᶜ : Set X)) j
@[simp] theorem
  twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq_twistedHomologyToBorelMooreHomologyCompl
    (j : ℕ) :
    twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j =
      twistedHomologyToBorelMooreHomologyCompl hA L j :=
  twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq hA L K _ j
@[reassoc] theorem twistedHomologyToBorelMooreHomologyCompl_naturality
    {L' : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ L') (j : ℕ) :
    (TopPair.ofSubset A).twistedHomologyCoefficientMap η j ≫
        twistedHomologyToBorelMooreHomologyCompl hA L' j =
      twistedHomologyToBorelMooreHomologyCompl hA L j ≫
        borelMooreHomologyCoefficientMap
          ((pullback (X := TopCat.of (Aᶜ : Set X)) (ContinuousMap.subtypeVal Aᶜ)).map η) j :=
  twistedHomologyToBorelMooreHomologyComplOfExhaustion_naturality hA L _ η j
/-- **Compatibility with closed-subset enlargement** for the compact-pair comparison map. -/
@[reassoc] theorem twistedHomologyTotalToOuter_comp_twistedHomologyToBorelMooreHomologyCompl
    {B : Set X} (hB : IsClosed B) (hAB : A ⊆ B)
    [WeaklyLocallyCompactSpace (Bᶜ : Set X)] [SigmaCompactSpace (Bᶜ : Set X)] (j : ℕ) :
    (TopTriple.ofSubset hAB).twistedHomologyTotalToOuter L j ≫
        twistedHomologyToBorelMooreHomologyCompl hB L j ≫
          borelMooreHomologyCoefficientMap
            ((pullbackCompIso (X := TopCat.of (Bᶜ : Set X)) (Y := TopCat.of (Aᶜ : Set X))
              (ContinuousMap.inclusion (Set.compl_subset_compl.2 hAB))
              (ContinuousMap.subtypeVal Aᶜ)).hom.app L) j =
      twistedHomologyToBorelMooreHomologyCompl hA L j ≫
        borelMooreHomologyOpenRestriction
          (TopCat.ofHom (ContinuousMap.inclusion (Set.compl_subset_compl.2 hAB)))
          (IsOpenEmbedding.of_comp (ContinuousMap.inclusion (Set.compl_subset_compl.2 hAB))
            hA.isOpen_compl.isOpenEmbedding_subtypeVal hB.isOpen_compl.isOpenEmbedding_subtypeVal)
          ((pullback (X := TopCat.of (Aᶜ : Set X)) (ContinuousMap.subtypeVal Aᶜ)).obj L) j := by
  rw [← borelMooreHomologyOpenRestrictionOfExhaustion_eq_borelMooreHomologyOpenRestriction _ _ _
    (CompactExhaustion.choice (Bᶜ : Set X))]
  exact twistedHomologyTotalToOuter_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion
    hA L (CompactExhaustion.choice (Aᶜ : Set X)) hB hAB (CompactExhaustion.choice (Bᶜ : Set X)) j
/-- **Naturality under maps of pairs with proper restriction to complements.** -/
@[reassoc] theorem twistedHomologyMap_comp_twistedHomologyToBorelMooreHomologyCompl
    {X' : TopCat.{v}} [T2Space X'] {A' : Set X'} (hA' : IsClosed A')
    [WeaklyLocallyCompactSpace (A'ᶜ : Set X')] [SigmaCompactSpace (A'ᶜ : Set X')]
    (φ : TopPair.ofSubset A' ⟶ TopPair.ofSubset A)
    (fCompl : TopCat.of (A'ᶜ : Set X') ⟶ TopCat.of (Aᶜ : Set X)) (hfCompl : IsProperMap fCompl.hom)
    (hw : fCompl ≫ TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ) =
      TopCat.ofHom (ContinuousMap.subtypeVal A'ᶜ) ≫ TopPair.Hom.fst φ) (j : ℕ) :
    TopPair.twistedHomologyMap φ L j ≫ twistedHomologyToBorelMooreHomologyCompl hA L j =
      twistedHomologyToBorelMooreHomologyCompl hA' ((pullback (TopPair.Hom.fst φ).hom).obj L) j ≫
        borelMooreHomologyCoefficientMap
          (((pullbackCompIso (TopCat.ofHom (ContinuousMap.subtypeVal A'ᶜ)).hom
              (TopPair.Hom.fst φ).hom).app L).symm ≪≫
            eqToIso (congrArg (fun k : TopCat.of (A'ᶜ : Set X') ⟶ X ↦
              (pullback k.hom).obj L) hw.symm) ≪≫
            (pullbackCompIso fCompl.hom
              (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)).hom).app L).hom j ≫
        borelMooreHomologyMap fCompl hfCompl
          ((pullback (X := TopCat.of (Aᶜ : Set X)) (ContinuousMap.subtypeVal Aᶜ)).obj L) j :=
  twistedHomologyMap_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion
    hA L _ hA' φ fCompl hfCompl hw _ j
@[reassoc (attr := simp)] theorem twistedHomologyπ_comp_twistedHomologyToBorelMooreHomologyCompl
    (j : ℕ) :
    (TopPair.ofSubset A).twistedHomologyπ L j ≫
        twistedHomologyToBorelMooreHomologyCompl hA L j =
      twistedHomologyToBorelMooreHomology L j ≫
        borelMooreHomologyOpenRestriction (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ))
          hA.isOpen_compl.isOpenEmbedding_subtypeVal L j :=
  (twistedHomologyπ_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion
    hA L (CompactExhaustion.choice (Aᶜ : Set X)) j).trans (congrArg (_ ≫ ·)
      (borelMooreHomologyOpenRestrictionOfExhaustion_eq_borelMooreHomologyOpenRestriction
        (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) hA.isOpen_compl.isOpenEmbedding_subtypeVal L
        (CompactExhaustion.choice (Aᶜ : Set X)) j))
/-- Factorization of open restriction from compact Hausdorff `X` to `X \ A`. -/
theorem borelMooreHomologyOpenRestriction_subtypeVal_compl_eq [CompactSpace X] (j : ℕ) :
    borelMooreHomologyOpenRestriction (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ))
        hA.isOpen_compl.isOpenEmbedding_subtypeVal L j =
      (twistedHomologyIsoBorelMooreHomology L j).inv ≫
        (TopPair.ofSubset A).twistedHomologyπ L j ≫
          twistedHomologyToBorelMooreHomologyCompl hA L j :=
  (borelMooreHomologyOpenRestrictionOfExhaustion_eq_borelMooreHomologyOpenRestriction
    (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) hA.isOpen_compl.isOpenEmbedding_subtypeVal L
    (CompactExhaustion.choice (Aᶜ : Set X)) j).symm.trans
    (borelMooreHomologyOpenRestrictionOfExhaustion_subtypeVal_compl_eq hA L
      (CompactExhaustion.choice (Aᶜ : Set X)) j)
end Choice
end T2
end ComparisonMap

section CofinalNeighborhoods
private lemma quasiIso_totalToOuter_of_eq {X : TopCat.{v}}
    {L : LocalCoefficientSystem.{u, v, max v w} R X} {A B B' : Set X} (hAB : A ⊆ B)
    (hAB' : A ⊆ B') (hBB' : B = B')
    [QuasiIso ((TopTriple.ofSubset hAB').twistedChainComplexTotalToOuter L)] :
    QuasiIso ((TopTriple.ofSubset hAB).twistedChainComplexTotalToOuter L) := by
  subst hBB'; infer_instance

variable {X : TopCat.{v}} [hComp : CompactSpace X] [hT2 : T2Space X] {A : Set X} (hA : IsClosed A)
  {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n)) (hAU : ∀ n, A ⊆ U n)
  (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W)

section QuasiIso
variable (L : LocalCoefficientSystem.{u, v, max v w} R X)
  (hU_qi : ∀ n, QuasiIso ((TopTriple.ofSubset (hAU n)).twistedChainComplexTotalToOuter L))
include hComp hT2 hA hU_open hAU hU_cofinal hU_qi
/-- When each `C(X, A; L) ⟶ C(X, U n; L)` is a quasi-iso, `relativeToOpenRestrictionLim` is too. -/
theorem quasiIso_relativeToOpenRestrictionLim_complOfCofinalNhds :
    QuasiIso (relativeToOpenRestrictionLim A L
      (CompactExhaustion.complOfCofinalNhds hA hU_open hAU hU_cofinal)) := by
  let K := CompactExhaustion.complOfCofinalNhds hA hU_open hAU hU_cofinal
  refine ComplexTower.quasiIso_isLimitLimComplexCone_lift
    (complChainComplexTower_shift_surjective L _ _)
    (relativeOpenRestrictionCone A L K) fun j ↦ ⟨0, fun n _ ↦ ?_⟩
  have hKeq :=
    CompactExhaustion.compl_image_subtypeVal_complOfCofinalNhds hA hU_open hAU hU_cofinal n
  have := hU_qi (cofinalNhdsIndex hA hU_open hAU hU_cofinal n)
  exact (quasiIso_iff _).1 (quasiIso_totalToOuter_of_eq
    (Set.subset_compl_comm.2 (Subtype.coe_image_subset Aᶜ (K n))) (hAU _) hKeq) j
/-- **Compact-pair comparison is an isomorphism** under cofinal quasi-isomorphic neighbourhoods. -/
theorem isIso_twistedHomologyToBorelMooreHomologyComplOfExhaustion_of_cofinal_nhds
    (K : CompactExhaustion (Aᶜ : Set X)) (j : ℕ) :
    IsIso (twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j) := by
  let K₀ := CompactExhaustion.complOfCofinalNhds hA hU_open hAU hU_cofinal
  rw [twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq hA L K K₀ j]
  have := quasiIso_relativeToOpenRestrictionLim_complOfCofinalNhds hA hU_open hAU hU_cofinal L hU_qi
  have := isIso_homologyMap_locallyFiniteChainComplexOpenRestrictionExcision
    (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K₀ hA.isOpen_compl.isOpenEmbedding_subtypeVal j
  unfold twistedHomologyToBorelMooreHomologyComplOfExhaustion; infer_instance
/-- **Compact-pair Borel–Moore comparison isomorphism** for an explicit exhaustion `K`. -/
def twistedHomologyIsoBorelMooreHomologyComplOfExhaustion
    (K : CompactExhaustion (Aᶜ : Set X)) (j : ℕ) :
    (TopPair.ofSubset A).twistedHomology L j ≅
      borelMooreHomology ((pullback (X := TopCat.of (Aᶜ : Set X))
        (ContinuousMap.subtypeVal Aᶜ)).obj L) j :=
  have := isIso_twistedHomologyToBorelMooreHomologyComplOfExhaustion_of_cofinal_nhds
    hA hU_open hAU hU_cofinal L hU_qi K j
  asIso (twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j)
@[simp] theorem twistedHomologyIsoBorelMooreHomologyComplOfExhaustion_hom
    (K : CompactExhaustion (Aᶜ : Set X)) (j : ℕ) :
    (twistedHomologyIsoBorelMooreHomologyComplOfExhaustion
        hA hU_open hAU hU_cofinal L hU_qi K j).hom =
      twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j := (rfl)
/-- **Compact-pair comparison isomorphism** `H_j(X, A; L) ≅ H_j^{BM}(X \ A; L|_{X \ A})`. -/
def twistedHomologyIsoBorelMooreHomologyCompl
    [WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)] (j : ℕ) :
    (TopPair.ofSubset A).twistedHomology L j ≅
      borelMooreHomology ((pullback (X := TopCat.of (Aᶜ : Set X))
        (ContinuousMap.subtypeVal Aᶜ)).obj L) j :=
  twistedHomologyIsoBorelMooreHomologyComplOfExhaustion hA hU_open hAU hU_cofinal L hU_qi
    (CompactExhaustion.choice (Aᶜ : Set X)) j
@[simp] theorem twistedHomologyIsoBorelMooreHomologyCompl_hom
    [WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)] (j : ℕ) :
    (twistedHomologyIsoBorelMooreHomologyCompl hA hU_open hAU hU_cofinal L hU_qi j).hom =
      twistedHomologyToBorelMooreHomologyCompl hA L j := (rfl)
end QuasiIso

section DeformationRetraction
variable (hU_ret : ∀ n, ∃ r : C(U n, A),
    (∀ a, r (ContinuousMap.inclusion (hAU n) a) = a) ∧
    ((ContinuousMap.inclusion (hAU n)).comp r).Homotopic (ContinuousMap.id (U n)))
  (L : LocalCoefficientSystem.{u, v, max v w} R X)
include hComp hT2 hA hU_open hAU hU_cofinal hU_ret
/-- **Compact-pair comparison isomorphism under deformation retractions**, for explicit `K`. -/
def twistedHomologyIsoBorelMooreHomologyComplOfExhaustionOfDeformationRetraction
    (K : CompactExhaustion (Aᶜ : Set X)) (j : ℕ) :
    (TopPair.ofSubset A).twistedHomology L j ≅
      borelMooreHomology ((pullback (X := TopCat.of (Aᶜ : Set X))
        (ContinuousMap.subtypeVal Aᶜ)).obj L) j :=
  twistedHomologyIsoBorelMooreHomologyComplOfExhaustion hA hU_open hAU hU_cofinal L
    (fun n ↦ let ⟨r, hr, hH⟩ := hU_ret n
      TopTriple.quasiIso_twistedChainComplexTotalToOuter_ofSubset_of_deformationRetraction
        (hAU n) L r hr hH) K j
@[simp] theorem twistedHomologyIsoBorelMooreHomologyComplOfExhaustionOfDeformationRetraction_hom
    (K : CompactExhaustion (Aᶜ : Set X)) (j : ℕ) :
    (twistedHomologyIsoBorelMooreHomologyComplOfExhaustionOfDeformationRetraction
        hA hU_open hAU hU_cofinal hU_ret L K j).hom =
      twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j := (rfl)
/-- **Compact-pair comparison isomorphism under deformation retractions.** -/
def twistedHomologyIsoBorelMooreHomologyComplOfDeformationRetraction
    [WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)] (j : ℕ) :
    (TopPair.ofSubset A).twistedHomology L j ≅
      borelMooreHomology ((pullback (X := TopCat.of (Aᶜ : Set X))
        (ContinuousMap.subtypeVal Aᶜ)).obj L) j :=
  twistedHomologyIsoBorelMooreHomologyComplOfExhaustionOfDeformationRetraction
    hA hU_open hAU hU_cofinal hU_ret L (CompactExhaustion.choice (Aᶜ : Set X)) j
@[simp] theorem twistedHomologyIsoBorelMooreHomologyComplOfDeformationRetraction_hom
    [WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)] (j : ℕ) :
    (twistedHomologyIsoBorelMooreHomologyComplOfDeformationRetraction
        hA hU_open hAU hU_cofinal hU_ret L j).hom =
      twistedHomologyToBorelMooreHomologyCompl hA L j := (rfl)
end DeformationRetraction
end CofinalNeighborhoods
end TauCeti.LocalCoefficientSystem
