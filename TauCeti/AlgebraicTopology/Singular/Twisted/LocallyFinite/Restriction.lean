/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Excision
public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.ExhaustionComparison
public import TauCeti.Topology.Category.TopCat.Pullback
public import TauCeti.Topology.Compactness.SigmaCompact
import TauCeti.Data.Set.Function

/-!
# Open restriction of Borel–Moore homology with local coefficients

Borel–Moore homology restricts contravariantly along open embeddings `i : V ⟶ U` into Hausdorff
spaces via excision on `openRestrictionTower i L K` (`borelMooreHomologyOpenRestriction`), with
exhaustion independence, coefficient naturality, compatibility with finite chains, functoriality,
and Cartesian base change with proper pushforward.
-/

public section
noncomputable section
open CategoryTheory Limits Opposite SimplexCategory Topology
open scoped Simplicial
namespace TauCeti.LocalCoefficientSystem
section
universe u' v'
private lemma homologyMap_commSq {R : Type u'} [Ring R]
    {C₁ C₂ C₃ C₄ : ChainComplex (ModuleCat.{v'} R) ℕ}
    {f : C₁ ⟶ C₂} {g : C₁ ⟶ C₃} {h : C₂ ⟶ C₄} {i : C₃ ⟶ C₄} (hsq : CommSq f g h i) (j : ℕ) :
    HomologicalComplex.homologyMap f j ≫ HomologicalComplex.homologyMap h j =
      HomologicalComplex.homologyMap g j ≫ HomologicalComplex.homologyMap i j := by
  simpa only [HomologicalComplex.homologyFunctor_map] using
    ((HomologicalComplex.homologyFunctor _ _ j).map_commSq hsq).w
end
universe u v w
variable {R : Type u} [Ring R]

section ExcisionTower
variable {V U : TopCat.{v}} (i : V ⟶ U)
  (L : LocalCoefficientSystem.{u, v, max v w} R U) (K : CompactExhaustion V)

/-- The tower `C(U, (i '' K n)ᶜ; L)` associated to `i : V ⟶ U` and a compact exhaustion `K`. -/
abbrev openRestrictionTower : ComplexTower.{max v w} R (ComplexShape.down ℕ) :=
  complChainComplexTower L (fun n ↦ i '' K n) (fun n ↦ Set.image_mono (K.subset_succ n))
/-- Chain map from locally finite chains on `U` to `(openRestrictionTower i L K).limComplex`. -/
abbrev locallyFiniteChainComplexToOpenRestrictionLim :
    locallyFiniteChainComplex L ⟶ (openRestrictionTower i L K).limComplex :=
  locallyFiniteChainComplexToComplLim L (fun n ↦ i '' K n)
    (fun n ↦ Set.image_mono (K.subset_succ n)) (fun n ↦ (K.isCompact n).image i.hom.continuous)
variable {K} in
/-- Enlarging `K` on `V` induces a quotient morphism of ambient relative towers. -/
abbrev openRestrictionTowerMap {K' : CompactExhaustion V} (h : ∀ n, K n ⊆ K' n) :
    openRestrictionTower i L K' ⟶ openRestrictionTower i L K :=
  complChainComplexTowerMap L (fun n ↦ Set.image_mono (K.subset_succ n))
    (fun n ↦ Set.image_mono (K'.subset_succ n)) (fun n ↦ Set.image_mono (h n))
variable {L} in
/-- Morphism of ambient relative towers induced by a morphism of local coefficient systems. -/
abbrev openRestrictionTowerCoefficientMap {L' : LocalCoefficientSystem.{u, v, max v w} R U}
    (η : L ⟶ L') : openRestrictionTower i L K ⟶ openRestrictionTower i L' K :=
  complChainComplexTowerCoefficientMap (fun n ↦ i '' K n)
    (fun n ↦ Set.image_mono (K.subset_succ n)) η
/-- Tower morphism from `complChainComplexTower` of `V` to `openRestrictionTower i L K`. -/
abbrev openRestrictionExcisionTowerMap (hinj : Function.Injective i) :
    complChainComplexTower ((pullback i.hom).obj L) K K.subset_succ ⟶
      openRestrictionTower i L K :=
  complChainComplexTowerPairMap i L K.subset_succ (fun n ↦ Set.image_mono (K.subset_succ n))
    (fun n ↦ (Set.surjOn_image i (K n)).mapsTo_compl hinj)

/-- **Excision at each stage of an open restriction** when the stage image `i '' K n` is closed. -/
theorem quasiIso_openRestrictionExcisionTowerMap_app_of_isClosed (hi : IsOpenEmbedding i.hom)
    (n : ℕ) (hKc : IsClosed (i '' K n)) :
    QuasiIso ((openRestrictionExcisionTowerMap i L K hi.injective).app (op n)) := by
  erw [complChainComplexTowerPairMap_app]; refine (quasiIso_iff_comp_left (eqToHom _) _).2 <|
    TopPair.quasiIso_twistedChainComplexMap_of_open_cover
      (TopPair.ofSubsetMap i ((Set.surjOn_image i (K n)).mapsTo_compl hi.injective)) L
      (by rw [TopPair.ofSubsetMap_fst]; exact hi.isEmbedding)
      (fun x hx ↦ by
        rw [TopPair.range_ofSubset_map] at hx ⊢; rw [TopPair.ofSubsetMap_fst] at hx
        exact fun hxK ↦ hx ⟨x, hxK, rfl⟩)
      (fun b : Bool ↦ bif b then Set.range i else (i '' K n)ᶜ)
      (Bool.rec hKc.isOpen_compl hi.isOpen_range)
      (Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.2 <|
        Classical.byCases (p := y ∈ i '' K n) (fun ⟨x, _, hxy⟩ ↦ ⟨true, x, hxy⟩) (⟨false, ·⟩))
      (Bool.rec (Or.inl (TopPair.range_ofSubset_map (B := (i '' K n)ᶜ)).ge)
        (Or.inr (by rw [TopPair.ofSubsetMap_fst]; exact le_rfl)))
/-- **Excision at each stage of an open restriction.** -/
theorem quasiIso_openRestrictionExcisionTowerMap_app [T2Space U] (hi : IsOpenEmbedding i.hom)
    (n : ℕ) : QuasiIso ((openRestrictionExcisionTowerMap i L K hi.injective).app (op n)) :=
  quasiIso_openRestrictionExcisionTowerMap_app_of_isClosed i L K hi n
    ((K.isCompact n).image i.hom.continuous).isClosed
/-- **Excision on the limit complex** when every stage image `i '' K n` is closed. -/
theorem quasiIso_limComplexMap_openRestrictionExcisionTowerMap_of_isClosed
    (hi : IsOpenEmbedding i.hom) (hKc : ∀ n, IsClosed (i '' K n)) :
    QuasiIso (ComplexTower.limComplexMap (openRestrictionExcisionTowerMap i L K hi.injective)) :=
  have (n : ℕ) := quasiIso_openRestrictionExcisionTowerMap_app_of_isClosed i L K hi n (hKc n)
  ComplexTower.quasiIso_limComplexMap _
    (complChainComplexTower_shift_surjective ((pullback i.hom).obj L) K K.subset_succ)
    (complChainComplexTower_shift_surjective L _ _)
/-- **Excision on the limit complex** for an open embedding `i : V ⟶ U` into a Hausdorff space. -/
theorem quasiIso_limComplexMap_openRestrictionExcisionTowerMap [T2Space U]
    (hi : IsOpenEmbedding i.hom) :
    QuasiIso (ComplexTower.limComplexMap (openRestrictionExcisionTowerMap i L K hi.injective)) :=
  quasiIso_limComplexMap_openRestrictionExcisionTowerMap_of_isClosed i L K hi fun n ↦
    ((K.isCompact n).image i.hom.continuous).isClosed
/-- Excision map from locally finite chains on `V` to `(openRestrictionTower i L K).limComplex`. -/
def locallyFiniteChainComplexOpenRestrictionExcision (hinj : Function.Injective i) :
    locallyFiniteChainComplex ((pullback i.hom).obj L) ⟶ (openRestrictionTower i L K).limComplex :=
  (locallyFiniteChainComplexIsoLimComplex ((pullback i.hom).obj L) K).hom ≫
    ComplexTower.limComplexMap (openRestrictionExcisionTowerMap i L K hinj)
@[reassoc (attr := simp)] lemma locallyFiniteChainComplexOpenRestrictionExcision_comp_π
    (hinj : Function.Injective i) (n : ℕ) :
    locallyFiniteChainComplexOpenRestrictionExcision i L K hinj ≫
        (openRestrictionTower i L K).limComplexπ n =
      (TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative ((pullback i.hom).obj L)
          (K.isCompact n).compl_range_ofSubset_compl_map ≫
        (openRestrictionExcisionTowerMap i L K hinj).app (op n) := by
  rw [locallyFiniteChainComplexOpenRestrictionExcision, Category.assoc,
    ComplexTower.limComplexMap_comp_π,
    locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexπ_assoc]; rfl
variable {K} in
@[reassoc] lemma locallyFiniteChainComplexOpenRestrictionExcision_comp_limComplexMap
    (hinj : Function.Injective i) {K' : CompactExhaustion V} (h : ∀ n, K n ⊆ K' n) :
    locallyFiniteChainComplexOpenRestrictionExcision i L K' hinj ≫
        ComplexTower.limComplexMap (openRestrictionTowerMap i L h) =
      locallyFiniteChainComplexOpenRestrictionExcision i L K hinj := by
  erw [locallyFiniteChainComplexOpenRestrictionExcision,
    locallyFiniteChainComplexOpenRestrictionExcision, Category.assoc,
    ← ComplexTower.limComplexMap_comp,
    ← complChainComplexTowerMap_comp_complChainComplexTowerPairMap i L K.subset_succ K'.subset_succ
      _ _ _ _ h (fun n ↦ Set.image_mono (h n)),
    ComplexTower.limComplexMap_comp,
    locallyFiniteChainComplexIsoLimComplex_hom_eq_toComplLim _ K',
    locallyFiniteChainComplexToComplLim_comp_limComplexMap_assoc _ K.subset_succ K'.subset_succ
      K.isCompact K'.isCompact h,
    ← locallyFiniteChainComplexIsoLimComplex_hom_eq_toComplLim _ K]
variable {L} in
@[reassoc] lemma locallyFiniteChainComplexCoefficientMap_comp_openRestrictionExcision
    (hinj : Function.Injective i) {L₁ L₂ : LocalCoefficientSystem.{u, v, max v w} R U}
    (η : L₁ ⟶ L₂) :
    locallyFiniteChainComplexCoefficientMap ((pullback i.hom).map η) ≫
        locallyFiniteChainComplexOpenRestrictionExcision i L₂ K hinj =
      locallyFiniteChainComplexOpenRestrictionExcision i L₁ K hinj ≫
        ComplexTower.limComplexMap (openRestrictionTowerCoefficientMap i K η) := by
  erw [locallyFiniteChainComplexOpenRestrictionExcision,
    locallyFiniteChainComplexOpenRestrictionExcision, ← Category.assoc,
    locallyFiniteChainComplexCoefficientMap_comp_isoLimComplex_hom, Category.assoc,
    ← ComplexTower.limComplexMap_comp, ← complChainComplexTowerPairMap_naturality i η K.subset_succ
      _ _, ComplexTower.limComplexMap_comp, Category.assoc]
/-- `locallyFiniteChainComplexOpenRestrictionExcision` is a quasi-isomorphism when every stage
image `i '' K n` is closed. -/
theorem quasiIso_locallyFiniteChainComplexOpenRestrictionExcision_of_isClosed
    (hi : IsOpenEmbedding i.hom) (hKc : ∀ n, IsClosed (i '' K n)) :
    QuasiIso (locallyFiniteChainComplexOpenRestrictionExcision i L K hi.injective) := by
  rw [locallyFiniteChainComplexOpenRestrictionExcision]
  have := quasiIso_limComplexMap_openRestrictionExcisionTowerMap_of_isClosed i L K hi hKc
  infer_instance
/-- In every degree `j`, `locallyFiniteChainComplexOpenRestrictionExcision` induces an iso when
every stage image `i '' K n` is closed. -/
theorem isIso_homologyMap_locallyFiniteChainComplexOpenRestrictionExcision_of_isClosed
    (hi : IsOpenEmbedding i.hom) (hKc : ∀ n, IsClosed (i '' K n)) (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (locallyFiniteChainComplexOpenRestrictionExcision i L K hi.injective) j) :=
  have := quasiIso_locallyFiniteChainComplexOpenRestrictionExcision_of_isClosed i L K hi hKc
  inferInstance
/-- `locallyFiniteChainComplexOpenRestrictionExcision` is a quasi-isomorphism. -/
theorem quasiIso_locallyFiniteChainComplexOpenRestrictionExcision [T2Space U]
    (hi : IsOpenEmbedding i.hom) :
    QuasiIso (locallyFiniteChainComplexOpenRestrictionExcision i L K hi.injective) :=
  quasiIso_locallyFiniteChainComplexOpenRestrictionExcision_of_isClosed i L K hi fun n ↦
    ((K.isCompact n).image i.hom.continuous).isClosed
/-- In every degree `j`, `locallyFiniteChainComplexOpenRestrictionExcision` induces an iso. -/
theorem isIso_homologyMap_locallyFiniteChainComplexOpenRestrictionExcision [T2Space U]
    (hi : IsOpenEmbedding i.hom) (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (locallyFiniteChainComplexOpenRestrictionExcision i L K hi.injective) j) :=
  have := quasiIso_locallyFiniteChainComplexOpenRestrictionExcision i L K hi; inferInstance
end ExcisionTower

section OpenRestriction
variable {V U : TopCat.{v}} [T2Space U] (i : V ⟶ U) (hi : IsOpenEmbedding i.hom)
  (L : LocalCoefficientSystem.{u, v, max v w} R U) (K : CompactExhaustion V)

/-- **Contravariant open restriction of Borel–Moore homology** for an explicit exhaustion `K`. -/
def borelMooreHomologyOpenRestrictionOfExhaustion (j : ℕ) :
    borelMooreHomology L j ⟶ borelMooreHomology ((pullback i.hom).obj L) j :=
  have := isIso_homologyMap_locallyFiniteChainComplexOpenRestrictionExcision i L K hi j
  HomologicalComplex.homologyMap (locallyFiniteChainComplexToOpenRestrictionLim i L K) j ≫
    inv (HomologicalComplex.homologyMap
      (locallyFiniteChainComplexOpenRestrictionExcision i L K hi.injective) j)
@[reassoc (attr := simp)]
theorem borelMooreHomologyOpenRestrictionOfExhaustion_comp_homologyMap_openRestrictionExcision
    (j : ℕ) :
    borelMooreHomologyOpenRestrictionOfExhaustion i hi L K j ≫ HomologicalComplex.homologyMap
        (locallyFiniteChainComplexOpenRestrictionExcision i L K hi.injective) j =
      HomologicalComplex.homologyMap (locallyFiniteChainComplexToOpenRestrictionLim i L K) j := by
  have := isIso_homologyMap_locallyFiniteChainComplexOpenRestrictionExcision i L K hi j
  simp [borelMooreHomologyOpenRestrictionOfExhaustion]
/-- Uniqueness criterion for `borelMooreHomologyOpenRestrictionOfExhaustion`. -/
theorem eq_comp_borelMooreHomologyOpenRestrictionOfExhaustion {M : ModuleCat.{max v w} R} {j : ℕ}
    {g : M ⟶ borelMooreHomology L j} {f : M ⟶ borelMooreHomology ((pullback i.hom).obj L) j}
    (hf : f ≫ HomologicalComplex.homologyMap
        (locallyFiniteChainComplexOpenRestrictionExcision i L K hi.injective) j =
      g ≫ HomologicalComplex.homologyMap
        (locallyFiniteChainComplexToOpenRestrictionLim i L K) j) :
    f = g ≫ borelMooreHomologyOpenRestrictionOfExhaustion i hi L K j := by
  have := isIso_homologyMap_locallyFiniteChainComplexOpenRestrictionExcision i L K hi j
  rw [← cancel_mono (HomologicalComplex.homologyMap
      (locallyFiniteChainComplexOpenRestrictionExcision i L K hi.injective) j),
    Category.assoc,
    borelMooreHomologyOpenRestrictionOfExhaustion_comp_homologyMap_openRestrictionExcision, hf]
/-- At each stage `n`, open restriction intertwines relative classes via excision. -/
@[reassoc (attr := simp)]
theorem borelMooreHomologyOpenRestrictionOfExhaustion_comp_toRelative_comp_excision (j n : ℕ) :
    borelMooreHomologyOpenRestrictionOfExhaustion i hi L K j ≫
        HomologicalComplex.homologyMap
          ((TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative ((pullback i.hom).obj L)
            (K.isCompact n).compl_range_ofSubset_compl_map) j ≫
          HomologicalComplex.homologyMap
            ((openRestrictionExcisionTowerMap i L K hi.injective).app (op n)) j =
      HomologicalComplex.homologyMap
        ((TopPair.ofSubset (i '' K n)ᶜ).locallyFiniteChainComplexToRelative L
          ((K.isCompact n).image i.hom.continuous).compl_range_ofSubset_compl_map) j := by
  have hsq1 : CommSq
      ((TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative ((pullback i.hom).obj L)
        (K.isCompact n).compl_range_ofSubset_compl_map)
      (locallyFiniteChainComplexOpenRestrictionExcision i L K hi.injective)
      ((openRestrictionExcisionTowerMap i L K hi.injective).app (op n))
      ((openRestrictionTower i L K).limComplexπ n) :=
    ⟨(locallyFiniteChainComplexOpenRestrictionExcision_comp_π i L K hi.injective n).symm⟩
  refine (congrArg (borelMooreHomologyOpenRestrictionOfExhaustion i hi L K j ≫ ·)
    (homologyMap_commSq hsq1 j)).trans ?_
  erw [borelMooreHomologyOpenRestrictionOfExhaustion_comp_homologyMap_openRestrictionExcision_assoc,
    ← HomologicalComplex.homologyMap_comp, locallyFiniteChainComplexToComplLim_comp_π]; rfl

private lemma borelMooreHomologyOpenRestrictionOfExhaustion_eq_of_subset
    {K' : CompactExhaustion V} (h : ∀ n, K n ⊆ K' n) (j : ℕ) :
    borelMooreHomologyOpenRestrictionOfExhaustion i hi L K' j =
      borelMooreHomologyOpenRestrictionOfExhaustion i hi L K j := by
  refine (eq_comp_borelMooreHomologyOpenRestrictionOfExhaustion i hi L K (g := 𝟙 _) ?_).trans
    (Category.id_comp _)
  have hsq1 : CommSq (𝟙 _)
      (locallyFiniteChainComplexOpenRestrictionExcision i L K' hi.injective)
      (locallyFiniteChainComplexOpenRestrictionExcision i L K hi.injective)
      (ComplexTower.limComplexMap (openRestrictionTowerMap i L h)) :=
    ⟨(Category.id_comp _).trans
      (locallyFiniteChainComplexOpenRestrictionExcision_comp_limComplexMap i L hi.injective h).symm⟩
  have hsq2 : CommSq (𝟙 _)
      (locallyFiniteChainComplexToOpenRestrictionLim i L K')
      (locallyFiniteChainComplexToOpenRestrictionLim i L K)
      (ComplexTower.limComplexMap (openRestrictionTowerMap i L h)) :=
    ⟨(Category.id_comp _).trans (locallyFiniteChainComplexToComplLim_comp_limComplexMap L
      (fun n ↦ Set.image_mono (K.subset_succ n)) (fun n ↦ Set.image_mono (K'.subset_succ n))
      (fun n ↦ (K.isCompact n).image i.hom.continuous)
      (fun n ↦ (K'.isCompact n).image i.hom.continuous)
      (fun n ↦ Set.image_mono (h n))).symm⟩
  have h1 := homologyMap_commSq hsq1 j
  have h2 := homologyMap_commSq hsq2 j
  rw [HomologicalComplex.homologyMap_id, Category.id_comp] at h1 h2
  rw [Category.id_comp, h1,
    borelMooreHomologyOpenRestrictionOfExhaustion_comp_homologyMap_openRestrictionExcision_assoc,
    ← h2]
/-- **Exhaustion independence of open restriction.** -/
theorem borelMooreHomologyOpenRestrictionOfExhaustion_eq (K' : CompactExhaustion V) (j : ℕ) :
    borelMooreHomologyOpenRestrictionOfExhaustion i hi L K j =
      borelMooreHomologyOpenRestrictionOfExhaustion i hi L K' j :=
  (borelMooreHomologyOpenRestrictionOfExhaustion_eq_of_subset i hi L K
    (CompactExhaustion.subset_sup_left K K') j).symm.trans
    (borelMooreHomologyOpenRestrictionOfExhaustion_eq_of_subset i hi L K'
      (CompactExhaustion.subset_sup_right K K') j)
/-- **Open restriction is natural in the local coefficient system.** -/
@[reassoc] theorem borelMooreHomologyOpenRestrictionOfExhaustion_naturality
    {L' : LocalCoefficientSystem.{u, v, max v w} R U} (η : L ⟶ L') (j : ℕ) :
    borelMooreHomologyCoefficientMap η j ≫
        borelMooreHomologyOpenRestrictionOfExhaustion i hi L' K j =
      borelMooreHomologyOpenRestrictionOfExhaustion i hi L K j ≫
        borelMooreHomologyCoefficientMap ((pullback i.hom).map η) j := by
  symm; refine eq_comp_borelMooreHomologyOpenRestrictionOfExhaustion i hi L' K ?_
  have hsq1 : CommSq (locallyFiniteChainComplexCoefficientMap ((pullback i.hom).map η))
      (locallyFiniteChainComplexOpenRestrictionExcision i L K hi.injective)
      (locallyFiniteChainComplexOpenRestrictionExcision i L' K hi.injective)
      (ComplexTower.limComplexMap (openRestrictionTowerCoefficientMap i K η)) :=
    ⟨locallyFiniteChainComplexCoefficientMap_comp_openRestrictionExcision i K hi.injective η⟩
  have hsq2 : CommSq (locallyFiniteChainComplexCoefficientMap η)
      (locallyFiniteChainComplexToOpenRestrictionLim i L K)
      (locallyFiniteChainComplexToOpenRestrictionLim i L' K)
      (ComplexTower.limComplexMap (openRestrictionTowerCoefficientMap i K η)) :=
    ⟨locallyFiniteChainComplexCoefficientMap_comp_toComplLim _ _ η _⟩
  rw [Category.assoc, homologyMap_commSq hsq1 j,
    borelMooreHomologyOpenRestrictionOfExhaustion_comp_homologyMap_openRestrictionExcision_assoc,
    ← homologyMap_commSq hsq2 j]
/-- **Compatibility of open restriction with finite chains pushed forward from `V`.** -/
@[reassoc (attr := simp)]
theorem
  twistedHomologyMap_comp_twistedHomologyToBorelMooreHomology_comp_openRestrictionOfExhaustion
    (j : ℕ) :
    twistedHomologyMap i L j ≫ twistedHomologyToBorelMooreHomology L j ≫
        borelMooreHomologyOpenRestrictionOfExhaustion i hi L K j =
      twistedHomologyToBorelMooreHomology ((pullback i.hom).obj L) j := by
  symm; refine (eq_comp_borelMooreHomologyOpenRestrictionOfExhaustion i hi L K
    (g := twistedHomologyMap i L j ≫ twistedHomologyToBorelMooreHomology L j) ?_).trans
      (Category.assoc _ _ _).symm
  have hchain : toLocallyFiniteChainComplex ((pullback i.hom).obj L) ≫
        locallyFiniteChainComplexOpenRestrictionExcision i L K hi.injective =
      (twistedChainComplexMap i L ≫ toLocallyFiniteChainComplex L) ≫
        locallyFiniteChainComplexToOpenRestrictionLim i L K :=
    (openRestrictionTower i L K).limComplex_hom_ext fun n ↦ by
      erw [Category.assoc, locallyFiniteChainComplexOpenRestrictionExcision_comp_π,
        TopPair.toLocallyFiniteChainComplex_comp_locallyFiniteChainComplexToRelative_assoc,
        twistedChainComplexπ_comp_complChainComplexTowerPairMap_app, Category.assoc, Category.assoc,
        locallyFiniteChainComplexToComplLim_comp_π,
        TopPair.toLocallyFiniteChainComplex_comp_locallyFiniteChainComplexToRelative]; rfl
  have hsq : CommSq (toLocallyFiniteChainComplex ((pullback i.hom).obj L))
      (twistedChainComplexMap i L ≫ toLocallyFiniteChainComplex L)
      (locallyFiniteChainComplexOpenRestrictionExcision i L K hi.injective)
      (locallyFiniteChainComplexToOpenRestrictionLim i L K) := ⟨hchain⟩
  have h := homologyMap_commSq hsq j
  rwa [HomologicalComplex.homologyMap_comp] at h

section Choice
variable [WeaklyLocallyCompactSpace V] [SigmaCompactSpace V]
/-- **Contravariant open restriction of Borel–Moore homology** along `i : V ⟶ U`. -/
def borelMooreHomologyOpenRestriction (j : ℕ) :
    borelMooreHomology L j ⟶ borelMooreHomology ((pullback i.hom).obj L) j :=
  borelMooreHomologyOpenRestrictionOfExhaustion i hi L (CompactExhaustion.choice V) j
@[simp] theorem borelMooreHomologyOpenRestrictionOfExhaustion_eq_borelMooreHomologyOpenRestriction
    (j : ℕ) :
    borelMooreHomologyOpenRestrictionOfExhaustion i hi L K j =
      borelMooreHomologyOpenRestriction i hi L j :=
  borelMooreHomologyOpenRestrictionOfExhaustion_eq i hi L K (CompactExhaustion.choice V) j
/-- At each stage `n` of any exhaustion `K`, `borelMooreHomologyOpenRestriction` intertwines
relative classes via excision. -/
@[reassoc (attr := simp)]
theorem borelMooreHomologyOpenRestriction_comp_toRelative_comp_excision (j n : ℕ) :
    borelMooreHomologyOpenRestriction i hi L j ≫
        HomologicalComplex.homologyMap
          ((TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative ((pullback i.hom).obj L)
            (K.isCompact n).compl_range_ofSubset_compl_map) j ≫
          HomologicalComplex.homologyMap
            ((openRestrictionExcisionTowerMap i L K hi.injective).app (op n)) j =
      HomologicalComplex.homologyMap
        ((TopPair.ofSubset (i '' K n)ᶜ).locallyFiniteChainComplexToRelative L
          ((K.isCompact n).image i.hom.continuous).compl_range_ofSubset_compl_map) j := by
  rw [← borelMooreHomologyOpenRestrictionOfExhaustion_eq_borelMooreHomologyOpenRestriction
    i hi L K j]
  exact borelMooreHomologyOpenRestrictionOfExhaustion_comp_toRelative_comp_excision i hi L K j n
/-- `borelMooreHomologyOpenRestriction` is natural in the local coefficient system. -/
@[reassoc] theorem borelMooreHomologyOpenRestriction_naturality
    {L' : LocalCoefficientSystem.{u, v, max v w} R U} (η : L ⟶ L') (j : ℕ) :
    borelMooreHomologyCoefficientMap η j ≫ borelMooreHomologyOpenRestriction i hi L' j =
      borelMooreHomologyOpenRestriction i hi L j ≫
        borelMooreHomologyCoefficientMap ((pullback i.hom).map η) j :=
  borelMooreHomologyOpenRestrictionOfExhaustion_naturality i hi L (CompactExhaustion.choice V) η j
/-- Open restriction of a finite chain pushed forward from `V` recovers its locally finite class. -/
@[reassoc (attr := simp)]
theorem
  twistedHomologyMap_comp_twistedHomologyToBorelMooreHomology_comp_borelMooreHomologyOpenRestriction
    (j : ℕ) :
    twistedHomologyMap i L j ≫ twistedHomologyToBorelMooreHomology L j ≫
        borelMooreHomologyOpenRestriction i hi L j =
      twistedHomologyToBorelMooreHomology ((pullback i.hom).obj L) j := by
  rw [← borelMooreHomologyOpenRestrictionOfExhaustion_eq_borelMooreHomologyOpenRestriction
    i hi L (CompactExhaustion.choice V) j]
  exact
    twistedHomologyMap_comp_twistedHomologyToBorelMooreHomology_comp_openRestrictionOfExhaustion
      i hi L _ j
end Choice
end OpenRestriction

section Functoriality
/-- **Identity law for open restriction of Borel–Moore homology.** -/
@[simp] theorem borelMooreHomologyOpenRestrictionOfExhaustion_id {U : TopCat.{v}} [T2Space U]
    (L : LocalCoefficientSystem.{u, v, max v w} R U) (K : CompactExhaustion U) (j : ℕ) :
    borelMooreHomologyOpenRestrictionOfExhaustion (𝟙 U) IsOpenEmbedding.id L K j =
      borelMooreHomologyCoefficientMap ((pullbackIdIso U).inv.app L) j := by
  symm; refine (eq_comp_borelMooreHomologyOpenRestrictionOfExhaustion (𝟙 U) IsOpenEmbedding.id L K
    (g := 𝟙 _) ?_).trans (Category.id_comp _)
  have hchain : locallyFiniteChainComplexCoefficientMap ((pullbackIdIso U).inv.app L) ≫
        locallyFiniteChainComplexOpenRestrictionExcision (𝟙 U) L K IsOpenEmbedding.id.injective =
      𝟙 (locallyFiniteChainComplex L) ≫ locallyFiniteChainComplexToOpenRestrictionLim (𝟙 U) L K :=
    (openRestrictionTower (𝟙 U) L K).limComplex_hom_ext fun n ↦ by
      have hsub : (K n)ᶜ ⊆ ((𝟙 U : U ⟶ U) '' K n)ᶜ := by simp
      have hrel : (TopPair.ofSubset (K n)ᶜ).twistedChainComplexCoefficientMap
            ((pullbackIdIso U).inv.app L) ≫ (openRestrictionExcisionTowerMap (𝟙 U) L K
            IsOpenEmbedding.id.injective).app (op n) =
          (TopTriple.ofSubset hsub).twistedChainComplexTotalToOuter L :=
        (TopPair.ofSubset (K n)ᶜ).twistedChainComplex_hom_ext L <| by
          erw [TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc,
            twistedChainComplexπ_comp_complChainComplexTowerPairMap_app, ← Category.assoc,
            twistedChainComplexMap_id, ← twistedChainComplexCoefficientMap_comp,
            (pullbackIdIso U).inv_hom_id_app, twistedChainComplexCoefficientMap_id,
            Category.id_comp, TopTriple.twistedChainComplexπ_comp_totalToOuter]; rfl
      erw [Category.assoc, locallyFiniteChainComplexOpenRestrictionExcision_comp_π,
        ← Category.assoc,
        ← (TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative_naturality, Category.assoc,
        hrel, TopTriple.locallyFiniteChainComplexToRelative_comp_twistedChainComplexTotalToOuter,
        Category.id_comp, locallyFiniteChainComplexToComplLim_comp_π]; rfl
  have hsq : CommSq (locallyFiniteChainComplexCoefficientMap ((pullbackIdIso U).inv.app L))
      (𝟙 (locallyFiniteChainComplex L))
      (locallyFiniteChainComplexOpenRestrictionExcision (𝟙 U) L K IsOpenEmbedding.id.injective)
      (locallyFiniteChainComplexToOpenRestrictionLim (𝟙 U) L K) := ⟨hchain⟩
  have h := homologyMap_commSq hsq j
  erw [HomologicalComplex.homologyMap_id, Category.id_comp] at h
  exact h
/-- Identity law for `borelMooreHomologyOpenRestriction`. -/
@[simp] theorem borelMooreHomologyOpenRestriction_id {U : TopCat.{v}} [T2Space U]
    [WeaklyLocallyCompactSpace U] [SigmaCompactSpace U]
    (L : LocalCoefficientSystem.{u, v, max v w} R U) (j : ℕ) :
    borelMooreHomologyOpenRestriction (𝟙 U) IsOpenEmbedding.id L j =
      borelMooreHomologyCoefficientMap ((pullbackIdIso U).inv.app L) j :=
  borelMooreHomologyOpenRestrictionOfExhaustion_id L _ j

section Comp
variable {W V U : TopCat.{v}} [T2Space U]
  (i₁ : W ⟶ V) (i₂ : V ⟶ U) (hi₁ : IsOpenEmbedding i₁.hom) (hi₂ : IsOpenEmbedding i₂.hom)
  (L : LocalCoefficientSystem.{u, v, max v w} R U)

/-- Excision compatibility for nested open embeddings `W ↪ V ↪ U` with `i₁ '' K_W n ⊆ K_V n`. -/
theorem
  borelMooreHomologyOpenRestrictionOfExhaustion_comp_coefficientMap_comp_excision_of_subset
    (K_W : CompactExhaustion W) (K_V : CompactExhaustion V) (hWV : ∀ n, i₁ '' K_W n ⊆ K_V n)
    (j : ℕ) :
    letI := hi₂.isEmbedding.t2Space
    borelMooreHomologyOpenRestrictionOfExhaustion i₁ hi₁ ((pullback i₂.hom).obj L) K_W j ≫
        borelMooreHomologyCoefficientMap ((pullbackCompIso i₁.hom i₂.hom).inv.app L) j ≫
        HomologicalComplex.homologyMap (locallyFiniteChainComplexOpenRestrictionExcision
          (i₁ ≫ i₂) L K_W (hi₂.comp hi₁).injective) j =
      HomologicalComplex.homologyMap
          (locallyFiniteChainComplexOpenRestrictionExcision i₂ L K_V hi₂.injective) j ≫
        HomologicalComplex.homologyMap (ComplexTower.limComplexMap
          (complChainComplexTowerMap L (fun n ↦ Set.image_mono (K_W.subset_succ n))
            (fun n ↦ Set.image_mono (K_V.subset_succ n))
            (fun n ↦ (Set.image_comp i₂ i₁ (K_W n)).symm ▸ Set.image_mono (hWV n)))) j := by
  have : T2Space V := hi₂.isEmbedding.t2Space
  have hUW (n : ℕ) : (i₁ ≫ i₂) '' K_W n ⊆ i₂ '' K_V n := by
    rw [TopCat.coe_comp, Set.image_comp]; exact Set.image_mono (hWV n)
  have hMaps (n : ℕ) : Set.MapsTo i₂ (i₁ '' K_W n)ᶜ ((i₁ ≫ i₂) '' K_W n)ᶜ := by
    rw [TopCat.coe_comp, Set.image_comp]
    exact (Set.surjOn_image i₂ (i₁ '' K_W n)).mapsTo_compl hi₂.injective
  let qV : complChainComplexTower ((pullback i₂.hom).obj L) K_V K_V.subset_succ ⟶
      openRestrictionTower i₁ ((pullback i₂.hom).obj L) K_W :=
    complChainComplexTowerMap _ _ K_V.subset_succ hWV
  let eUW : openRestrictionTower i₁ ((pullback i₂.hom).obj L) K_W ⟶
      openRestrictionTower (i₁ ≫ i₂) L K_W := complChainComplexTowerPairMap i₂ L _ _ hMaps
  have htower : openRestrictionExcisionTowerMap (i₁ ≫ i₂) L K_W (hi₂.comp hi₁).injective =
      complChainComplexTowerCoefficientMap K_W K_W.subset_succ
          ((pullbackCompIso i₁.hom i₂.hom).hom.app L) ≫
        openRestrictionExcisionTowerMap i₁ ((pullback i₂.hom).obj L) K_W hi₁.injective ≫ eUW :=
    complChainComplexTowerPairMap_comp i₁ i₂ L K_W.subset_succ _ _ _ hMaps
  have hlim2 : locallyFiniteChainComplexOpenRestrictionExcision (i₁ ≫ i₂) L K_W
        (hi₂.comp hi₁).injective =
      locallyFiniteChainComplexCoefficientMap ((pullbackCompIso i₁.hom i₂.hom).hom.app L) ≫
        locallyFiniteChainComplexOpenRestrictionExcision i₁ ((pullback i₂.hom).obj L) K_W
          hi₁.injective ≫ ComplexTower.limComplexMap eUW := by
    rw [locallyFiniteChainComplexOpenRestrictionExcision,
      locallyFiniteChainComplexOpenRestrictionExcision, htower, ComplexTower.limComplexMap_comp,
      ComplexTower.limComplexMap_comp, ← Category.assoc,
      ← locallyFiniteChainComplexCoefficientMap_comp_isoLimComplex_hom, Category.assoc,
      Category.assoc]; rfl
  have hpushV : locallyFiniteChainComplexToOpenRestrictionLim i₁ ((pullback i₂.hom).obj L) K_W =
      (locallyFiniteChainComplexIsoLimComplex ((pullback i₂.hom).obj L) K_V).hom ≫
        ComplexTower.limComplexMap qV :=
    (locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexMap_compl _ K_V _ _ hWV).symm
  have hsq : qV ≫ eUW = openRestrictionExcisionTowerMap i₂ L K_V hi₂.injective ≫
      complChainComplexTowerMap L (fun n ↦ Set.image_mono (K_W.subset_succ n))
        (fun n ↦ Set.image_mono (K_V.subset_succ n)) hUW :=
    complChainComplexTowerMap_comp_complChainComplexTowerPairMap i₂ L _ K_V.subset_succ _ _
      hMaps _ hWV hUW
  have hsqLim : CommSq
      (locallyFiniteChainComplexToOpenRestrictionLim i₁ ((pullback i₂.hom).obj L) K_W)
      (locallyFiniteChainComplexOpenRestrictionExcision i₂ L K_V hi₂.injective)
      (ComplexTower.limComplexMap eUW)
      (ComplexTower.limComplexMap (complChainComplexTowerMap L
        (fun n ↦ Set.image_mono (K_W.subset_succ n))
        (fun n ↦ Set.image_mono (K_V.subset_succ n)) hUW)) :=
    ⟨by rw [hpushV, Category.assoc, ← ComplexTower.limComplexMap_comp, hsq,
      ComplexTower.limComplexMap_comp, locallyFiniteChainComplexOpenRestrictionExcision,
      Category.assoc]⟩
  rw [hlim2, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp,
    ← Category.assoc (borelMooreHomologyCoefficientMap _ j),
    ← borelMooreHomologyCoefficientMap_comp, (pullbackCompIso i₁.hom i₂.hom).inv_hom_id_app,
    borelMooreHomologyCoefficientMap_id, Category.id_comp,
    borelMooreHomologyOpenRestrictionOfExhaustion_comp_homologyMap_openRestrictionExcision_assoc]
  exact homologyMap_commSq hsqLim j
/-- **Contravariant composition law for open restriction**, for explicit compact exhaustions. -/
@[reassoc] theorem borelMooreHomologyOpenRestrictionOfExhaustion_comp
    (K_W : CompactExhaustion W) (K_V : CompactExhaustion V) (j : ℕ) :
    borelMooreHomologyOpenRestrictionOfExhaustion (i₁ ≫ i₂) (hi₂.comp hi₁) L K_W j ≫
        borelMooreHomologyCoefficientMap ((pullbackCompIso i₁.hom i₂.hom).hom.app L) j =
      borelMooreHomologyOpenRestrictionOfExhaustion i₂ hi₂ L K_V j ≫
        (letI := hi₂.isEmbedding.t2Space
        borelMooreHomologyOpenRestrictionOfExhaustion i₁ hi₁ ((pullback i₂.hom).obj L) K_W j) := by
  have : T2Space V := hi₂.isEmbedding.t2Space
  let K_V' := K_V.supImage i₁.hom.continuous hi₁.isOpenMap K_W
  rw [borelMooreHomologyOpenRestrictionOfExhaustion_eq i₂ hi₂ L K_V K_V' j]
  suffices hmain : borelMooreHomologyOpenRestrictionOfExhaustion i₂ hi₂ L K_V' j ≫
        borelMooreHomologyOpenRestrictionOfExhaustion i₁ hi₁ ((pullback i₂.hom).obj L) K_W j ≫
        borelMooreHomologyCoefficientMap ((pullbackCompIso i₁.hom i₂.hom).inv.app L) j =
      borelMooreHomologyOpenRestrictionOfExhaustion (i₁ ≫ i₂) (hi₂.comp hi₁) L K_W j by
    rw [← hmain, Category.assoc, Category.assoc, ← borelMooreHomologyCoefficientMap_comp,
      (pullbackCompIso i₁.hom i₂.hom).inv_hom_id_app, borelMooreHomologyCoefficientMap_id]
    erw [Category.comp_id]
  refine (eq_comp_borelMooreHomologyOpenRestrictionOfExhaustion (i₁ ≫ i₂) (hi₂.comp hi₁) L K_W
    (g := 𝟙 _) ?_).trans (Category.id_comp _)
  have hsqLim : CommSq (𝟙 (locallyFiniteChainComplex L))
      (locallyFiniteChainComplexToOpenRestrictionLim i₂ L K_V')
      (locallyFiniteChainComplexToOpenRestrictionLim (i₁ ≫ i₂) L K_W)
      (ComplexTower.limComplexMap (complChainComplexTowerMap L
        (fun n ↦ Set.image_mono (K_W.subset_succ n))
        (fun n ↦ Set.image_mono (K_V'.subset_succ n))
        (fun n ↦ (Set.image_comp i₂ i₁ (K_W n)).symm ▸
          Set.image_mono (K_V.image_subset_supImage i₁.hom.continuous hi₁.isOpenMap K_W n)))) :=
    ⟨(Category.id_comp _).trans (locallyFiniteChainComplexToComplLim_comp_limComplexMap L
      (fun n ↦ Set.image_mono (K_W.subset_succ n)) (fun n ↦ Set.image_mono (K_V'.subset_succ n))
      (fun n ↦ (K_W.isCompact n).image (i₁ ≫ i₂).hom.continuous)
      (fun n ↦ (K_V'.isCompact n).image i₂.hom.continuous) _).symm⟩
  have hLim := homologyMap_commSq hsqLim j
  rw [HomologicalComplex.homologyMap_id, Category.id_comp] at hLim
  rw [Category.id_comp, Category.assoc, Category.assoc,
    borelMooreHomologyOpenRestrictionOfExhaustion_comp_coefficientMap_comp_excision_of_subset
      i₁ i₂ hi₁ hi₂ L K_W K_V'
      (K_V.image_subset_supImage i₁.hom.continuous hi₁.isOpenMap K_W),
    borelMooreHomologyOpenRestrictionOfExhaustion_comp_homologyMap_openRestrictionExcision_assoc,
    ← hLim]
/-- **Contravariant composition law for open restriction of Borel–Moore homology.** -/
@[reassoc] theorem borelMooreHomologyOpenRestriction_comp
    [WeaklyLocallyCompactSpace W] [SigmaCompactSpace W]
    [WeaklyLocallyCompactSpace V] [SigmaCompactSpace V] (j : ℕ) :
    borelMooreHomologyOpenRestriction (i₁ ≫ i₂) (hi₂.comp hi₁) L j ≫
        borelMooreHomologyCoefficientMap ((pullbackCompIso i₁.hom i₂.hom).hom.app L) j =
      borelMooreHomologyOpenRestriction i₂ hi₂ L j ≫
        (letI := hi₂.isEmbedding.t2Space
        borelMooreHomologyOpenRestriction i₁ hi₁ ((pullback i₂.hom).obj L) j) :=
  borelMooreHomologyOpenRestrictionOfExhaustion_comp i₁ i₂ hi₁ hi₂ L _ _ j
end Comp

/-- Chain-level naturality square for `locallyFiniteChainComplexOpenRestrictionExcision` under a
commutative square with proper map `f' : V' ⟶ V`. -/
theorem locallyFiniteChainComplexOpenRestrictionExcision_naturality_square
    {V' V U' U : TopCat.{v}} (i : V ⟶ U) (hi : Function.Injective i) (i' : V' ⟶ U')
    (hi' : Function.Injective i') (f : U' ⟶ U) (f' : V' ⟶ V) (hf' : IsProperMap f'.hom)
    (hw : f' ≫ i = i' ≫ f) (L : LocalCoefficientSystem.{u, v, max v w} R U)
    (K_V : CompactExhaustion V) (K_V' : CompactExhaustion V')
    (hf_maps : ∀ n, Set.MapsTo f (i' '' K_V' n)ᶜ (i '' K_V n)ᶜ) :
    locallyFiniteChainComplexCoefficientMap
          (((pullbackCompIso i'.hom f.hom).app L).symm ≪≫
            eqToIso (congrArg (fun k : V' ⟶ U ↦ (pullback k.hom).obj L) hw.symm) ≪≫
            (pullbackCompIso f'.hom i.hom).app L).hom ≫
        locallyFiniteChainComplexMap f' hf' ((pullback i.hom).obj L) ≫
        locallyFiniteChainComplexOpenRestrictionExcision i L K_V hi =
      locallyFiniteChainComplexOpenRestrictionExcision i' ((pullback f.hom).obj L) K_V' hi' ≫
        ComplexTower.limComplexMap (complChainComplexTowerPairMap f L
          (fun n ↦ Set.image_mono (K_V'.subset_succ n))
          (fun n ↦ Set.image_mono (K_V.subset_succ n)) hf_maps) := by
  have hf'_maps (n : ℕ) : Set.MapsTo f' (K_V' n)ᶜ (K_V n)ᶜ :=
    (hf_maps n).of_compl_image hi' (funext fun v' ↦ congrArg (fun g : V' ⟶ U ↦ g v') hw)
  set α : (pullback i'.hom).obj ((pullback f.hom).obj L) ⟶
      (pullback f'.hom).obj ((pullback i.hom).obj L) :=
    (((pullbackCompIso i'.hom f.hom).app L).symm ≪≫
      eqToIso (congrArg (fun k : V' ⟶ U ↦ (pullback k.hom).obj L) hw.symm) ≪≫
      (pullbackCompIso f'.hom i.hom).app L).hom
  erw [locallyFiniteChainComplexOpenRestrictionExcision,
    locallyFiniteChainComplexOpenRestrictionExcision,
    ← Category.assoc (locallyFiniteChainComplexMap f' hf' _),
    locallyFiniteChainComplexMap_comp_isoLimComplex_hom f' hf' _ K_V' K_V hf'_maps, Category.assoc,
    Category.assoc, ← Category.assoc (locallyFiniteChainComplexCoefficientMap α),
    locallyFiniteChainComplexCoefficientMap_comp_isoLimComplex_hom K_V' α, Category.assoc,
    ← ComplexTower.limComplexMap_comp, ← ComplexTower.limComplexMap_comp,
    ← complChainComplexTowerPairMap_naturality_square i' f f' i L hw.symm K_V'.subset_succ
      (fun n ↦ Set.image_mono (K_V'.subset_succ n)) K_V.subset_succ
      (fun n ↦ Set.image_mono (K_V.subset_succ n))
      (fun n ↦ (Set.surjOn_image i' (K_V' n)).mapsTo_compl hi')
      hf_maps hf'_maps (fun n ↦ (Set.surjOn_image i (K_V n)).mapsTo_compl hi),
    ComplexTower.limComplexMap_comp, ← Category.assoc]

/-- Homology-level naturality square for `locallyFiniteChainComplexOpenRestrictionExcision` under a
commutative square with proper map `f' : V' ⟶ V`. -/
@[reassoc] theorem homologyMap_locallyFiniteChainComplexOpenRestrictionExcision_naturality_square
    {V' V U' U : TopCat.{v}} (i : V ⟶ U) (hi : Function.Injective i) (i' : V' ⟶ U')
    (hi' : Function.Injective i') (f : U' ⟶ U) (f' : V' ⟶ V) (hf' : IsProperMap f'.hom)
    (hw : f' ≫ i = i' ≫ f) (L : LocalCoefficientSystem.{u, v, max v w} R U)
    (K_V : CompactExhaustion V) (K_V' : CompactExhaustion V')
    (hf_maps : ∀ n, Set.MapsTo f (i' '' K_V' n)ᶜ (i '' K_V n)ᶜ) (j : ℕ) :
    borelMooreHomologyCoefficientMap
          (((pullbackCompIso i'.hom f.hom).app L).symm ≪≫
            eqToIso (congrArg (fun k : V' ⟶ U ↦ (pullback k.hom).obj L) hw.symm) ≪≫
            (pullbackCompIso f'.hom i.hom).app L).hom j ≫
        borelMooreHomologyMap f' hf' ((pullback i.hom).obj L) j ≫
        HomologicalComplex.homologyMap
          (locallyFiniteChainComplexOpenRestrictionExcision i L K_V hi) j =
      HomologicalComplex.homologyMap
          (locallyFiniteChainComplexOpenRestrictionExcision i' ((pullback f.hom).obj L) K_V' hi')
          j ≫
        HomologicalComplex.homologyMap (ComplexTower.limComplexMap
          (complChainComplexTowerPairMap f L (fun n ↦ Set.image_mono (K_V'.subset_succ n))
            (fun n ↦ Set.image_mono (K_V.subset_succ n)) hf_maps)) j := by
  have hsq : CommSq
      (locallyFiniteChainComplexCoefficientMap
        (((pullbackCompIso i'.hom f.hom).app L).symm ≪≫
          eqToIso (congrArg (fun k : V' ⟶ U ↦ (pullback k.hom).obj L) hw.symm) ≪≫
          (pullbackCompIso f'.hom i.hom).app L).hom ≫
        locallyFiniteChainComplexMap f' hf' ((pullback i.hom).obj L))
      (locallyFiniteChainComplexOpenRestrictionExcision i' ((pullback f.hom).obj L) K_V' hi')
      (locallyFiniteChainComplexOpenRestrictionExcision i L K_V hi)
      (ComplexTower.limComplexMap (complChainComplexTowerPairMap f L
        (fun n ↦ Set.image_mono (K_V'.subset_succ n))
        (fun n ↦ Set.image_mono (K_V.subset_succ n)) hf_maps)) :=
    ⟨(Category.assoc _ _ _).trans
      (locallyFiniteChainComplexOpenRestrictionExcision_naturality_square
        i hi i' hi' f f' hf' hw L K_V K_V' hf_maps)⟩
  have h := homologyMap_commSq hsq j
  rwa [HomologicalComplex.homologyMap_comp, Category.assoc] at h

section BaseChange
variable {V' V U' U : TopCat.{v}} [T2Space U'] [T2Space U] (i : V ⟶ U) (hi : IsOpenEmbedding i.hom)
  (i' : V' ⟶ U') (hi' : IsOpenEmbedding i'.hom) (f : U' ⟶ U) (hf : IsProperMap f.hom) (f' : V' ⟶ V)
  (hw : f' ≫ i = i' ≫ f) (hcart : f ⁻¹' Set.range i ⊆ Set.range i')
  (L : LocalCoefficientSystem.{u, v, max v w} R U)
include hcart
/-- **Base change between proper pushforward and open restriction**, for explicit exhaustions. -/
@[reassoc] theorem borelMooreHomologyMap_comp_borelMooreHomologyOpenRestrictionOfExhaustion
    (K_V : CompactExhaustion V) (K_V' : CompactExhaustion V') (j : ℕ) :
    borelMooreHomologyMap f hf L j ≫ borelMooreHomologyOpenRestrictionOfExhaustion i hi L K_V j =
      borelMooreHomologyOpenRestrictionOfExhaustion i' hi' ((pullback f.hom).obj L) K_V' j ≫
        borelMooreHomologyCoefficientMap
          (((pullbackCompIso i'.hom f.hom).app L).symm ≪≫
            eqToIso (congrArg (fun k : V' ⟶ U ↦ (pullback k.hom).obj L) hw.symm) ≪≫
            (pullbackCompIso f'.hom i.hom).app L).hom j ≫
        borelMooreHomologyMap f'
          (hf.of_cartesian_isEmbeddings hi.isEmbedding hi'.isEmbedding hw hcart)
          ((pullback i.hom).obj L) j := by
  have hf' := hf.of_cartesian_isEmbeddings hi.isEmbedding hi'.isEmbedding hw hcart
  let K_V'' := K_V'.supPreimage hf' K_V
  rw [borelMooreHomologyOpenRestrictionOfExhaustion_eq i' hi' ((pullback f.hom).obj L) K_V' K_V'' j]
  have hf_maps (n : ℕ) : Set.MapsTo f (i' '' K_V'' n)ᶜ (i '' K_V n)ᶜ :=
    (K_V'.mapsTo_compl_supPreimage hf' K_V n).compl_image hi.injective
      (funext fun v' ↦ congrArg (fun g : V' ⟶ U ↦ g v') hw) hcart
  have hsqLim : CommSq (locallyFiniteChainComplexMap f hf L)
      (locallyFiniteChainComplexToOpenRestrictionLim i' ((pullback f.hom).obj L) K_V'')
      (locallyFiniteChainComplexToOpenRestrictionLim i L K_V)
      (ComplexTower.limComplexMap (complChainComplexTowerPairMap f L
        (fun n ↦ Set.image_mono (K_V''.subset_succ n))
        (fun n ↦ Set.image_mono (K_V.subset_succ n)) hf_maps)) :=
    ⟨locallyFiniteChainComplexMap_comp_toComplLim f hf L _ _ _ _ hf_maps⟩
  symm; refine eq_comp_borelMooreHomologyOpenRestrictionOfExhaustion i hi L K_V ?_
  rw [Category.assoc, Category.assoc,
    homologyMap_locallyFiniteChainComplexOpenRestrictionExcision_naturality_square
      i hi.injective i' hi'.injective f f' hf' hw L K_V K_V'' hf_maps,
    borelMooreHomologyOpenRestrictionOfExhaustion_comp_homologyMap_openRestrictionExcision_assoc,
    homologyMap_commSq hsqLim j]
/-- **Base change between proper pushforward and open restriction.** -/
@[reassoc] theorem borelMooreHomologyMap_comp_borelMooreHomologyOpenRestriction
    [WeaklyLocallyCompactSpace V] [SigmaCompactSpace V]
    [WeaklyLocallyCompactSpace V'] [SigmaCompactSpace V'] (j : ℕ) :
    borelMooreHomologyMap f hf L j ≫ borelMooreHomologyOpenRestriction i hi L j =
      borelMooreHomologyOpenRestriction i' hi' ((pullback f.hom).obj L) j ≫
        borelMooreHomologyCoefficientMap
          (((pullbackCompIso i'.hom f.hom).app L).symm ≪≫
            eqToIso (congrArg (fun k : V' ⟶ U ↦ (pullback k.hom).obj L) hw.symm) ≪≫
            (pullbackCompIso f'.hom i.hom).app L).hom j ≫
        borelMooreHomologyMap f'
          (hf.of_cartesian_isEmbeddings hi.isEmbedding hi'.isEmbedding hw hcart)
          ((pullback i.hom).obj L) j :=
  borelMooreHomologyMap_comp_borelMooreHomologyOpenRestrictionOfExhaustion
    i hi i' hi' f hf f' hw hcart L _ _ j
end BaseChange
end Functoriality
end TauCeti.LocalCoefficientSystem
