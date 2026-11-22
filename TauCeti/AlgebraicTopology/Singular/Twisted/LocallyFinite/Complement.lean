/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Acyclic
public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Restriction

/-!
# Borel–Moore homology of the complement of a closed set

For a closed subset `A` of a space `X`, a local coefficient system `L` on `X`, and a compact
exhaustion `K` of `X \ A`, the canonical cone of triple quotients `C(X, A; L) ⟶ C(X, X \ Kₙ; L)`
lifts to a chain map `relativeToOpenRestrictionLim A L K` into the limit complex of
`openRestrictionTower (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K`. When each stage image
`Kₙ` is closed in `X` (automatic when `X` is Hausdorff), inverse excision on open restriction
defines the comparison morphism
`H_j(X, A; L) ⟶ H_j^{BM}(X \ A; L|_{X \ A})`
(`twistedHomologyToBorelMooreHomologyComplOfIsClosed`,
`twistedHomologyToBorelMooreHomologyComplOfExhaustion`, and
`twistedHomologyToBorelMooreHomologyCompl`),
which is independent of `K` and natural in `L`, closed-subset enlargement, proper complement pair
maps, and open restriction.

This yields a unified comparison theorem: whenever each triple quotient
`C(X, A; L) ⟶ C(X, X \ Kₙ; L)` is a quasi-isomorphism and each `Kₙ` is closed in `X`,
`relativeToOpenRestrictionLim A L K` is a quasi-isomorphism and the comparison morphism is an
isomorphism (`isIso_twistedHomologyToBorelMooreHomologyComplOfIsClosed`). Two corollaries follow:

* `borelMooreHomologyComplEquiv`: for any closed compact sets `Kₙ ⊆ X \ A` covering `X \ A` with
  `Kₙ ⊆ interior Kₙ₊₁` and `H_*(X \ Kₙ, A; L) = 0` (without assuming `X` compact or Hausdorff),
  `H^{BM}_j(X \ A; L) ≃ H_j(X, A; L)`, characterized on relative classes via
  `twistedHomologyTotalToOuter_borelMooreHomologyComplEquiv`.
* `twistedHomologyIsoBorelMooreHomologyCompl` and
  `twistedHomologyIsoBorelMooreHomologyComplOfDeformationRetraction`: on a compact Hausdorff space
  `X`, when `A` has a countable cofinal family of open neighbourhoods whose triple quotients are
  quasi-isomorphisms (for instance deformation retractions onto `A`),
  `H_j(X, A; L) ≅ H_j^{BM}(X \ A; L|_{X \ A})`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, proof of Proposition 2.22.
* J. Milnor, *On axiomatic homology theory*, Pacific J. Math. 12 (1962), 337–341.
* G. E. Bredon, *Sheaf Theory*, 2nd ed., Graduate Texts in Mathematics 170, Chapter V.
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

/-- Composing `relativeToOpenRestrictionLim` with the `n`-th tower projection gives the triple
quotient `C(X, A; L) ⟶ C(X, X \ Kₙ; L)`. -/
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
        (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K := by
  refine (openRestrictionTower (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K).limComplex_hom_ext
    fun n ↦ ?_
  have h1 := relativeToOpenRestrictionLim_comp_π A L K n
  have h2 := locallyFiniteChainComplexToComplLim_comp_π L
    (fun n ↦ TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ) '' K n)
    (fun n ↦ Set.image_mono (K.subset_succ n))
    (fun n ↦ (K.isCompact n).image (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)).hom.continuous) n
  have h3 := (TopTriple.ofSubset (Set.subset_compl_comm.2
    (Subtype.coe_image_subset Aᶜ (K n)))).twistedChainComplexπ_comp_totalToOuter L
  have h4 := (TopPair.ofSubset (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ) ''
    K n)ᶜ).toLocallyFiniteChainComplex_comp_locallyFiniteChainComplexToRelative L
      ((K.isCompact n).image
        (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)).hom.continuous).compl_range_ofSubset_compl_map
  erw [Category.assoc, h1, h3, ← h4, Category.assoc, ← h2]; rfl

/-- When every stage triple quotient `C(X, A; L) ⟶ C(X, X \ Kₙ; L)` is a quasi-isomorphism,
`relativeToOpenRestrictionLim A L K` is a quasi-isomorphism. -/
theorem quasiIso_relativeToOpenRestrictionLim
    (hKqi : ∀ n, QuasiIso ((TopTriple.ofSubset (Set.subset_compl_comm.2
      (Subtype.coe_image_subset Aᶜ (K n)))).twistedChainComplexTotalToOuter L)) :
    QuasiIso (relativeToOpenRestrictionLim A L K) :=
  ComplexTower.quasiIso_isLimitLimComplexCone_lift
    (complChainComplexTower_shift_surjective L _ _) (relativeOpenRestrictionCone A L K)
    fun j ↦ ⟨0, fun n _ ↦ (quasiIso_iff _).1 (hKqi n) j⟩

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
      relativeToOpenRestrictionLim A₁ L₁ K₁ ≫ ComplexTower.limComplexMap q := by
  refine (openRestrictionTower
    (TopCat.ofHom (ContinuousMap.subtypeVal A₂ᶜ)) L₂ K₂).limComplex_hom_ext
    fun n ↦ (TopPair.ofSubset A₁).twistedChainComplex_hom_ext L₁ ?_
  have h₁ := (TopTriple.ofSubset (Set.subset_compl_comm.2
    (Subtype.coe_image_subset A₁ᶜ (K₁ n)))).twistedChainComplexπ_comp_totalToOuter L₁
  have h₂ := (TopTriple.ofSubset (Set.subset_compl_comm.2
    (Subtype.coe_image_subset A₂ᶜ (K₂ n)))).twistedChainComplexπ_comp_totalToOuter L₂
  simp only [Category.assoc, relativeToOpenRestrictionLim_comp_π,
    ComplexTower.limComplexMap_comp_π]
  erw [← Category.assoc _ p, hp, Category.assoc, h₂, relativeToOpenRestrictionLim_comp_π_assoc,
    ← Category.assoc _ _ (q.app (op n)), h₁, hq n]; rfl

/-- Enlarging the compact exhaustion `K` commutes with `relativeToOpenRestrictionLim`. -/
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

/-- Changing local coefficients commutes with `relativeToOpenRestrictionLim`. -/
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

section IsClosed

variable {A : Set X} (hA : IsClosed A) (L : LocalCoefficientSystem.{u, v, max v w} R X)
  (K : CompactExhaustion (Aᶜ : Set X))
  (hKc : ∀ n, IsClosed ((TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) '' K n))

/-- **Comparison morphism `H_j(X, A; L) ⟶ H_j^{BM}(X \ A; L|_{X \ A})`** when every stage
`K n` has closed image in `X`. -/
def twistedHomologyToBorelMooreHomologyComplOfIsClosed (j : ℕ) :
    (TopPair.ofSubset A).twistedHomology L j ⟶
      borelMooreHomology ((pullback (X := TopCat.of (Aᶜ : Set X))
        (ContinuousMap.subtypeVal Aᶜ)).obj L) j :=
  have := isIso_homologyMap_locallyFiniteChainComplexOpenRestrictionExcision_of_isClosed
    (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K hA.isOpen_compl.isOpenEmbedding_subtypeVal hKc
    j
  HomologicalComplex.homologyMap (relativeToOpenRestrictionLim A L K) j ≫
    inv (HomologicalComplex.homologyMap (locallyFiniteChainComplexOpenRestrictionExcision
      (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K
      hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective) j)

/-- Precomposing the excision homology map with `twistedHomologyToBorelMooreHomologyComplOfIsClosed`
recovers `relativeToOpenRestrictionLim`. -/
@[reassoc (attr := simp)]
theorem twistedHomologyToBorelMooreHomologyComplOfIsClosed_comp_homologyMap_openRestrictionExcision
    (j : ℕ) :
    twistedHomologyToBorelMooreHomologyComplOfIsClosed hA L K hKc j ≫
        HomologicalComplex.homologyMap (locallyFiniteChainComplexOpenRestrictionExcision
          (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K
          hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective) j =
      HomologicalComplex.homologyMap (relativeToOpenRestrictionLim A L K) j := by
  have := isIso_homologyMap_locallyFiniteChainComplexOpenRestrictionExcision_of_isClosed
    (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K hA.isOpen_compl.isOpenEmbedding_subtypeVal hKc
    j
  simp [twistedHomologyToBorelMooreHomologyComplOfIsClosed]

/-- At each stage `n`, `twistedHomologyToBorelMooreHomologyComplOfIsClosed` followed by the
relative class of a locally finite chain and excision equals the triple quotient
`H_j(X, A; L) ⟶ H_j(X, X \ Kₙ; L)`. -/
theorem twistedHomologyToBorelMooreHomologyComplOfIsClosed_comp_toRelative_comp_excision
    (j n : ℕ) :
    twistedHomologyToBorelMooreHomologyComplOfIsClosed hA L K hKc j ≫
        HomologicalComplex.homologyMap
          ((TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative
            ((pullback (X := TopCat.of (Aᶜ : Set X)) (ContinuousMap.subtypeVal Aᶜ)).obj L)
            (K.isCompact n).compl_range_ofSubset_compl_map) j ≫
          HomologicalComplex.homologyMap
            ((openRestrictionExcisionTowerMap (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K
              hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective).app (op n)) j =
      (TopTriple.ofSubset (Set.subset_compl_comm.2
        (Subtype.coe_image_subset Aᶜ (K n)))).twistedHomologyTotalToOuter L j := by
  erw [← HomologicalComplex.homologyMap_comp,
    ← locallyFiniteChainComplexOpenRestrictionExcision_comp_π,
    HomologicalComplex.homologyMap_comp, ← Category.assoc,
    twistedHomologyToBorelMooreHomologyComplOfIsClosed_comp_homologyMap_openRestrictionExcision
      hA,
    ← HomologicalComplex.homologyMap_comp, relativeToOpenRestrictionLim_comp_π]; rfl

/-- When every stage triple quotient is a quasi-isomorphism and every stage image is closed in `X`,
`twistedHomologyToBorelMooreHomologyComplOfIsClosed` is an isomorphism. -/
theorem isIso_twistedHomologyToBorelMooreHomologyComplOfIsClosed
    (hKqi : ∀ n, QuasiIso ((TopTriple.ofSubset (Set.subset_compl_comm.2
      (Subtype.coe_image_subset Aᶜ (K n)))).twistedChainComplexTotalToOuter L)) (j : ℕ) :
    IsIso (twistedHomologyToBorelMooreHomologyComplOfIsClosed hA L K hKc j) := by
  have := quasiIso_relativeToOpenRestrictionLim A L K hKqi
  have := isIso_homologyMap_locallyFiniteChainComplexOpenRestrictionExcision_of_isClosed
    (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K hA.isOpen_compl.isOpenEmbedding_subtypeVal hKc
    j
  unfold twistedHomologyToBorelMooreHomologyComplOfIsClosed; infer_instance

end IsClosed

section T2

variable [T2Space X] {A : Set X} (hA : IsClosed A)
  (L : LocalCoefficientSystem.{u, v, max v w} R X) (K : CompactExhaustion (Aᶜ : Set X))

/-- **Comparison morphism `H_j(X, A; L) ⟶ H_j^{BM}(X \ A; L|_{X \ A})`** for exhaustion `K`. -/
def twistedHomologyToBorelMooreHomologyComplOfExhaustion (j : ℕ) :
    (TopPair.ofSubset A).twistedHomology L j ⟶
      borelMooreHomology ((pullback (X := TopCat.of (Aᶜ : Set X))
        (ContinuousMap.subtypeVal Aᶜ)).obj L) j :=
  twistedHomologyToBorelMooreHomologyComplOfIsClosed hA L K
    (fun n ↦ ((K.isCompact n).image continuous_subtypeVal).isClosed) j

/-- Precomposing the excision homology map with
`twistedHomologyToBorelMooreHomologyComplOfExhaustion` recovers `relativeToOpenRestrictionLim`. -/
@[reassoc (attr := simp)]
theorem
  twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap_openRestrictionExcision
    (j : ℕ) :
    twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j ≫
        HomologicalComplex.homologyMap (locallyFiniteChainComplexOpenRestrictionExcision
          (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K
          hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective) j =
      HomologicalComplex.homologyMap (relativeToOpenRestrictionLim A L K) j :=
  twistedHomologyToBorelMooreHomologyComplOfIsClosed_comp_homologyMap_openRestrictionExcision
    hA L K (fun n ↦ ((K.isCompact n).image continuous_subtypeVal).isClosed) j

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
    Category.assoc,
    twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap_openRestrictionExcision,
    hf]

private lemma twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq_of_subset
    {K' : CompactExhaustion (Aᶜ : Set X)} (h : ∀ n, K n ⊆ K' n) (j : ℕ) :
    twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K' j =
      twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j := by
  refine (eq_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K (g := 𝟙 _) ?_).trans
    (Category.id_comp _)
  rw [Category.id_comp, ← locallyFiniteChainComplexOpenRestrictionExcision_comp_limComplexMap
      (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L
      hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective h, HomologicalComplex.homologyMap_comp,
    ← Category.assoc,
    twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap_openRestrictionExcision
      hA,
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
  have h1 :
      borelMooreHomologyCoefficientMap
          ((pullback (X := TopCat.of (Aᶜ : Set X)) (ContinuousMap.subtypeVal Aᶜ)).map η) j ≫
        HomologicalComplex.homologyMap (locallyFiniteChainComplexOpenRestrictionExcision
          (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L' K
          hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective) j =
      HomologicalComplex.homologyMap (locallyFiniteChainComplexOpenRestrictionExcision
          (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K
          hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective) j ≫
        HomologicalComplex.homologyMap (ComplexTower.limComplexMap
          (openRestrictionTowerCoefficientMap
            (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) K η)) j := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    exact congrArg (fun φ ↦ HomologicalComplex.homologyMap φ j)
      (locallyFiniteChainComplexCoefficientMap_comp_openRestrictionExcision
        (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) K
        hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective η)
  rw [Category.assoc, h1, ← Category.assoc,
    twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap_openRestrictionExcision
      hA,
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
  let q := complChainComplexTowerMap L (fun n ↦ Set.image_mono (K_B.subset_succ n))
    (fun n ↦ Set.image_mono (K'.subset_succ n)) hXA
  have hRel : (TopTriple.ofSubset hAB).twistedChainComplexTotalToOuter L ≫
        relativeToOpenRestrictionLim B L K_B =
      relativeToOpenRestrictionLim A L K' ≫ ComplexTower.limComplexMap q :=
    comp_relativeToOpenRestrictionLim_eq (𝟙 _) _ _
      (((TopTriple.ofSubset hAB).twistedChainComplexπ_comp_totalToOuter L).trans
        (Category.id_comp _).symm)
      fun n ↦ (twistedChainComplexπ_comp_complChainComplexTowerMap_app L _ _ hXA n).trans
        (Category.id_comp _).symm
  have hmain : twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K' j ≫
        borelMooreHomologyOpenRestrictionOfExhaustion ι hι ((pullback iA.hom).obj L) K_B j ≫
          borelMooreHomologyCoefficientMap ((pullbackCompIso ι.hom iA.hom).inv.app L) j =
      (TopTriple.ofSubset hAB).twistedHomologyTotalToOuter L j ≫
        twistedHomologyToBorelMooreHomologyComplOfExhaustion hB L K_B j := by
    refine eq_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion hB L K_B ?_
    have h1 := borelMooreHomologyOpenRestrictionOfExhaustion_comp_excision_of_subset
      ι iA hι hiA L K_B K' hBA hXA j
    have h2 :
        HomologicalComplex.homologyMap
            (relativeToOpenRestrictionLim A L K' ≫ ComplexTower.limComplexMap q) j =
          (TopTriple.ofSubset hAB).twistedHomologyTotalToOuter L j ≫
            HomologicalComplex.homologyMap (relativeToOpenRestrictionLim B L K_B) j :=
      (congrArg (fun φ ↦ HomologicalComplex.homologyMap φ j) hRel.symm).trans
        (HomologicalComplex.homologyMap_comp _ _ j)
    refine ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
      ((Category.assoc _ _ _).trans h1))).trans ?_
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) <|
      twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap_openRestrictionExcision
        hA L K' j)).trans ?_
    exact (HomologicalComplex.homologyMap_comp _ _ j).symm.trans h2
  have hcancel :
      (borelMooreHomologyOpenRestrictionOfExhaustion ι hι ((pullback iA.hom).obj L) K_B j ≫
          borelMooreHomologyCoefficientMap ((pullbackCompIso ι.hom iA.hom).inv.app L) j) ≫
        borelMooreHomologyCoefficientMap ((pullbackCompIso ι.hom iA.hom).hom.app L) j =
      borelMooreHomologyOpenRestrictionOfExhaustion ι hι ((pullback iA.hom).obj L) K_B j := by
    simp only [Category.assoc, ← borelMooreHomologyCoefficientMap_comp,
      (pullbackCompIso ι.hom iA.hom).inv_hom_id_app, borelMooreHomologyCoefficientMap_id]
    exact Category.comp_id _
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hmain.symm)).trans <|
    (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hcancel)

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
  erw [twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq
    hA' ((pullback f.hom).obj L) K' K'' j]
  have hcart : f ⁻¹' Set.range iA ⊆ Set.range iA' := by
    rintro x ⟨y, hy⟩
    have hxA' : x ∉ A' := fun hx' ↦ y.property <| by
      have h : (TopPair.Hom.snd φ ⟨x, hx'⟩).val = f x :=
        congrArg (fun k : TopCat.of (A' : Set X') ⟶ X ↦ k ⟨x, hx'⟩) (TopPair.Hom.w φ)
      have hy' : y.val = f x := hy
      rw [hy', ← h]; exact (TopPair.Hom.snd φ ⟨x, hx'⟩).property
    exact ⟨⟨x, hxA'⟩, rfl⟩
  have hfCompl_maps := mapsTo_compl_supPreimage hfCompl K K'
  have hf_maps := mapsTo_compl_image_supPreimage
    hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective hfCompl hw hcart K K'
  have hRel : TopPair.twistedChainComplexMap φ L ≫ relativeToOpenRestrictionLim A L K =
      relativeToOpenRestrictionLim A' ((pullback f.hom).obj L) K'' ≫
        ComplexTower.limComplexMap (complChainComplexTowerPairMap f L _ _ hf_maps) :=
    comp_relativeToOpenRestrictionLim_eq (twistedChainComplexMap f L) _ _
      (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap φ L) fun n ↦
        twistedChainComplexπ_comp_complChainComplexTowerPairMap_app f L _ _ hf_maps n
  have h1 := homologyMap_locallyFiniteChainComplexOpenRestrictionExcision_naturality_square
    iA hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective
    iA' hA'.isOpen_compl.isOpenEmbedding_subtypeVal.injective f fCompl hfCompl hw L K K''
    hfCompl_maps hf_maps j
  symm; refine eq_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K ?_
  refine ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
    ((Category.assoc _ _ _).trans h1))).trans ?_
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) <|
    twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap_openRestrictionExcision
      hA' ((pullback f.hom).obj L) K'' j)).trans ?_
  exact (HomologicalComplex.homologyMap_comp _ _ j).symm.trans <|
    (congrArg (fun ψ ↦ HomologicalComplex.homologyMap ψ j) hRel.symm).trans
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
  rw [Category.assoc,
    twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap_openRestrictionExcision,
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

/-- The exhaustion-specific comparison morphism equals
`twistedHomologyToBorelMooreHomologyCompl`. -/
@[simp] theorem
  twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq_twistedHomologyToBorelMooreHomologyCompl
    (j : ℕ) :
    twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j =
      twistedHomologyToBorelMooreHomologyCompl hA L j :=
  twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq hA L K _ j

/-- `twistedHomologyToBorelMooreHomologyCompl` is natural in local coefficients. -/
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

/-- Compatibility of `twistedHomologyToBorelMooreHomologyCompl` with open restriction on absolute
twisted homology. -/
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

end Choice

/-- Factorization of open restriction from compact Hausdorff `X` to `σ`-compact `X \ A`. -/
theorem borelMooreHomologyOpenRestriction_subtypeVal_compl_eq [CompactSpace X]
    [SigmaCompactSpace (Aᶜ : Set X)] (j : ℕ) :
    letI := hA.isOpen_compl.locallyCompactSpace
    borelMooreHomologyOpenRestriction (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ))
        hA.isOpen_compl.isOpenEmbedding_subtypeVal L j =
      (twistedHomologyIsoBorelMooreHomology L j).inv ≫
        (TopPair.ofSubset A).twistedHomologyπ L j ≫
          twistedHomologyToBorelMooreHomologyCompl hA L j := by
  have := hA.isOpen_compl.locallyCompactSpace
  exact (borelMooreHomologyOpenRestrictionOfExhaustion_eq_borelMooreHomologyOpenRestriction
    (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) hA.isOpen_compl.isOpenEmbedding_subtypeVal L
    (CompactExhaustion.choice (Aᶜ : Set X)) j).symm.trans
    (borelMooreHomologyOpenRestrictionOfExhaustion_subtypeVal_compl_eq hA L
      (CompactExhaustion.choice (Aᶜ : Set X)) j)

end T2

end ComparisonMap

section ClosedExhaustion

variable {X : TopCat.{v}} (L : LocalCoefficientSystem.{u, v, max v w} R X)
  {A : Set X} {K : ℕ → Set X} (hK : ∀ n, IsCompact (K n)) (hKc : ∀ n, IsClosed (K n))
  (hKA : ∀ n, A ⊆ (K n)ᶜ) (hsub : ∀ n, K n ⊆ interior (K (n + 1)))
  (hcover : ∀ x ∉ A, ∃ n, x ∈ K n)
  (hzero : ∀ n k, IsZero ((TopPair.ofInclusion (hKA n)).twistedHomology
    ((TopPair.ofSubset (K n)ᶜ).subspaceSystem L) k))

include hKA hsub hcover in
private lemma isClosed_of_closedExhaustion : IsClosed A := by
  simpa using (isOpen_of_subset_interior_succ (fun n ↦ Set.subset_compl_comm.1 (hKA n)) hsub
    fun x hx ↦ Set.mem_iUnion.2 (hcover x hx)).isClosed_compl

private abbrev subtypeExhaustionOfClosed : CompactExhaustion (Aᶜ : Set X) :=
  CompactExhaustion.subtype Aᶜ K hK (fun n ↦ Set.subset_compl_comm.1 (hKA n)) hsub
    fun x hx ↦ Set.mem_iUnion.2 (hcover x hx)

private lemma image_subtypeVal_subtypeExhaustionOfClosed (n : ℕ) :
    TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ) ''
        subtypeExhaustionOfClosed hK hKA hsub hcover n = K n :=
  Set.image_preimage_eq_iff.2 (Subtype.range_coe.symm ▸ Set.subset_compl_comm.1 (hKA n))

private lemma quasiIso_totalToOuter_of_eq {B B' : Set X} (hAB : A ⊆ B) (hAB' : A ⊆ B')
    (hBB' : B = B') [QuasiIso ((TopTriple.ofSubset hAB').twistedChainComplexTotalToOuter L)] :
    QuasiIso ((TopTriple.ofSubset hAB).twistedChainComplexTotalToOuter L) := by
  subst hBB'; infer_instance

include hzero in
private lemma isIso_comparison_of_closedExhaustion (j : ℕ) :
    IsIso (twistedHomologyToBorelMooreHomologyComplOfIsClosed
      (isClosed_of_closedExhaustion hKA hsub hcover) L
      (subtypeExhaustionOfClosed hK hKA hsub hcover)
      (fun n ↦ (image_subtypeVal_subtypeExhaustionOfClosed hK hKA hsub hcover n).symm ▸ hKc n)
      j) := by
  refine isIso_twistedHomologyToBorelMooreHomologyComplOfIsClosed _ L _ _ (fun n ↦ ?_) j
  have hqi : QuasiIso ((TopTriple.ofSubset (hKA n)).twistedChainComplexTotalToOuter L) :=
    (quasiIso_iff _).2 fun k ↦ (quasiIsoAt_iff_isIso_homologyMap _ k).2 <|
      TopTriple.isIso_twistedHomologyTotalToOuter_of_isZero (TopTriple.ofSubset (hKA n)) L k
        (hzero n k) fun m _ ↦ hzero n m
  have heq : (K n)ᶜ = (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ) ''
      subtypeExhaustionOfClosed hK hKA hsub hcover n)ᶜ :=
    congrArg compl (image_subtypeVal_subtypeExhaustionOfClosed hK hKA hsub hcover n).symm
  exact quasiIso_totalToOuter_of_eq L _ (hKA n) heq.symm

include hK hKc hKA hsub hcover hzero in
/-- **Borel–Moore homology of a complement.** Let `A ⊆ X`, and let `Kₙ` be closed compact subsets
of `X` covering `X \ A`, disjoint from `A`, with `Kₙ ⊆ interior Kₙ₊₁`. If the relative homology
`H_*(X \ Kₙ, A; L)` of each open neighbourhood `X \ Kₙ` of `A` vanishes, then the Borel–Moore
homology of `X \ A`, with coefficients in the restriction of `L`, is the relative homology of
`(X, A)`: `H^{BM}_j(X \ A; L) ≃ H_j(X, A; L)`. -/
def borelMooreHomologyComplEquiv (j : ℕ) :
    borelMooreHomology
        ((pullback (X := TopCat.of ↥Aᶜ) ⟨Subtype.val, continuous_subtypeVal⟩).obj L) j ≃ₗ[R]
      (TopPair.ofSubset A).twistedHomology L j :=
  have := isIso_comparison_of_closedExhaustion L hK hKc hKA hsub hcover hzero j
  (asIso (twistedHomologyToBorelMooreHomologyComplOfIsClosed
    (isClosed_of_closedExhaustion hKA hsub hcover) L
    (subtypeExhaustionOfClosed hK hKA hsub hcover)
    (fun n ↦ (image_subtypeVal_subtypeExhaustionOfClosed hK hKA hsub hcover n).symm ▸ hKc n)
    j)).symm.toLinearEquiv

private lemma totalToOuter_comp_eq_of_eq {A : Set X}
    (L : LocalCoefficientSystem.{u, v, max v w} R X) (j : ℕ)
    {B B' : Set X} (hAB : A ⊆ B) (hAB' : A ⊆ B') (hBB' : B = B')
    (f : (TopPair.ofSubset (Subtype.val ⁻¹' B')).twistedChainComplex
        ((pullback (X := TopCat.of ↥Aᶜ) ⟨Subtype.val, continuous_subtypeVal⟩).obj L) ⟶
      (TopPair.ofSubset B).twistedChainComplex L)
    (hf : (TopPair.ofSubset (Subtype.val ⁻¹' B')).twistedChainComplexπ _ ≫ f =
      twistedChainComplexMap (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L ≫
        (TopPair.ofSubset B).twistedChainComplexπ L)
    (y : (TopPair.ofSubset A).twistedHomology L j)
    (w : (TopPair.ofSubset (Subtype.val ⁻¹' B')).twistedHomology
      ((pullback (X := TopCat.of ↥Aᶜ) ⟨Subtype.val, continuous_subtypeVal⟩).obj L) j)
    (hw : (HomologicalComplex.homologyMap f j).hom w =
      ((TopTriple.ofSubset hAB).twistedHomologyTotalToOuter L j).hom y) :
    ((TopTriple.ofSubset hAB').twistedHomologyTotalToOuter L j).hom y =
      (TopPair.twistedHomologyMap (TopPair.excisionMap Aᶜ B') L j).hom w := by
  subst hBB'
  rw [← hw]
  have hmaps : f = TopPair.twistedChainComplexMap (TopPair.excisionMap Aᶜ B) L := by
    refine TopPair.twistedChainComplex_hom_ext _ _ ?_
    erw [hf, TopPair.twistedChainComplexπ_comp_twistedChainComplexMap]; rfl
  rw [hmaps]; rfl

include hK hKc hKA hsub hcover hzero in
/-- The isomorphism `H^{BM}_j(X \ A; L) ≃ H_j(X, A; L)` followed by the quotient to
`H_j(X, X \ Kₙ; L)` sends a class to the relative class of its locally finite representatives in
`H_j(X \ A, X \ (A ∪ Kₙ); L)`, followed by excision. -/
theorem twistedHomologyTotalToOuter_borelMooreHomologyComplEquiv (j n : ℕ)
    (x : borelMooreHomology
      ((pullback (X := TopCat.of ↥Aᶜ) ⟨Subtype.val, continuous_subtypeVal⟩).obj L) j) :
    ((TopTriple.ofSubset (hKA n)).twistedHomologyTotalToOuter L j).hom
        (borelMooreHomologyComplEquiv L hK hKc hKA hsub hcover hzero j x) =
      (TopPair.twistedHomologyMap (TopPair.excisionMap Aᶜ (K n)ᶜ) L j).hom
        ((HomologicalComplex.homologyMap (TopPair.locallyFiniteChainComplexToRelative
          (TopPair.ofSubset (X := TopCat.of ↥Aᶜ) (Subtype.val ⁻¹' K n)ᶜ) _
          (IsCompact.compl_range_ofSubset_compl_map (CompactExhaustion.isCompact
            (CompactExhaustion.subtype Aᶜ K hK (fun n ↦ Set.subset_compl_comm.1 (hKA n)) hsub
              fun x hx ↦ Set.mem_iUnion.2 (hcover x hx)) n))) j).hom x) := by
  have := isIso_comparison_of_closedExhaustion L hK hKc hKA hsub hcover hzero j
  let f := twistedHomologyToBorelMooreHomologyComplOfIsClosed
    (isClosed_of_closedExhaustion hKA hsub hcover) L
    (subtypeExhaustionOfClosed hK hKA hsub hcover)
    (fun m ↦ (image_subtypeVal_subtypeExhaustionOfClosed hK hKA hsub hcover m).symm ▸ hKc m) j
  set y := borelMooreHomologyComplEquiv L hK hKc hKA hsub hcover hzero j x
  have hfy : f.hom y = x := congrArg (fun g ↦ g.hom x) (IsIso.inv_hom_id f)
  have hrel := congrArg (fun g ↦ g.hom y)
    (twistedHomologyToBorelMooreHomologyComplOfIsClosed_comp_toRelative_comp_excision
      (isClosed_of_closedExhaustion hKA hsub hcover) L
      (subtypeExhaustionOfClosed hK hKA hsub hcover)
      (fun m ↦ (image_subtypeVal_subtypeExhaustionOfClosed hK hKA hsub hcover m).symm ▸ hKc m)
      j n)
  have hrel' :
      (HomologicalComplex.homologyMap
        ((openRestrictionExcisionTowerMap (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L
          (subtypeExhaustionOfClosed hK hKA hsub hcover)
          (isClosed_of_closedExhaustion hKA hsub
            hcover).isOpen_compl.isOpenEmbedding_subtypeVal.injective).app (op n)) j).hom
        ((HomologicalComplex.homologyMap (TopPair.locallyFiniteChainComplexToRelative
          (TopPair.ofSubset (X := TopCat.of ↥Aᶜ) (Subtype.val ⁻¹' K n)ᶜ) _
          (IsCompact.compl_range_ofSubset_compl_map (CompactExhaustion.isCompact
            (CompactExhaustion.subtype Aᶜ K hK (fun n ↦ Set.subset_compl_comm.1 (hKA n)) hsub
              fun x hx ↦ Set.mem_iUnion.2 (hcover x hx)) n))) j).hom x) =
      ((TopTriple.ofSubset (Set.subset_compl_comm.2
        (Subtype.coe_image_subset Aᶜ _))).twistedHomologyTotalToOuter L j).hom y := by
    erw [← hfy]; exact hrel
  exact totalToOuter_comp_eq_of_eq L j
    (Set.subset_compl_comm.2 (Subtype.coe_image_subset Aᶜ _)) (hKA n)
    (congrArg compl (image_subtypeVal_subtypeExhaustionOfClosed hK hKA hsub hcover n))
    ((openRestrictionExcisionTowerMap (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L
      (subtypeExhaustionOfClosed hK hKA hsub hcover)
      (isClosed_of_closedExhaustion hKA hsub
        hcover).isOpen_compl.isOpenEmbedding_subtypeVal.injective).app (op n))
    (twistedChainComplexπ_comp_complChainComplexTowerPairMap_app _ L _ _ _ n) y _ hrel'

end ClosedExhaustion

section CofinalNeighborhoods

variable {X : TopCat.{v}} [hComp : CompactSpace X] [hT2 : T2Space X] {A : Set X} (hA : IsClosed A)
  {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n)) (hAU : ∀ n, A ⊆ U n)
  (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W)

section QuasiIso

variable (L : LocalCoefficientSystem.{u, v, max v w} R X)
  (hU_qi : ∀ n, QuasiIso ((TopTriple.ofSubset (hAU n)).twistedChainComplexTotalToOuter L))
include hComp hT2 hA hU_open hAU hU_cofinal hU_qi

/-- When each `C(X, A; L) ⟶ C(X, U n; L)` is a quasi-iso, `relativeToOpenRestrictionLim` is too. -/
theorem quasiIso_relativeToOpenRestrictionLim_complOfCofinalNhdsSet :
    QuasiIso (relativeToOpenRestrictionLim A L
      (CompactExhaustion.complOfCofinalNhdsSet hA hU_open hAU hU_cofinal)) := by
  refine quasiIso_relativeToOpenRestrictionLim A L _ fun n ↦ ?_
  have hKeq :=
    CompactExhaustion.compl_image_subtypeVal_complOfCofinalNhdsSet hA hU_open hAU hU_cofinal n
  have := hU_qi (TauCeti.shrinkingNhdsSetIndex hA hU_open hAU hU_cofinal n)
  exact quasiIso_totalToOuter_of_eq L _ (hAU _) hKeq

/-- **Compact-pair comparison is an isomorphism** under cofinal quasi-isomorphic neighbourhoods. -/
theorem isIso_twistedHomologyToBorelMooreHomologyComplOfExhaustion_of_cofinal_nhds_set
    (K : CompactExhaustion (Aᶜ : Set X)) (j : ℕ) :
    IsIso (twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j) := by
  let K₀ := CompactExhaustion.complOfCofinalNhdsSet hA hU_open hAU hU_cofinal
  rw [twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq hA L K K₀ j]
  have := quasiIso_relativeToOpenRestrictionLim_complOfCofinalNhdsSet
    hA hU_open hAU hU_cofinal L hU_qi
  have := isIso_homologyMap_locallyFiniteChainComplexOpenRestrictionExcision
    (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K₀ hA.isOpen_compl.isOpenEmbedding_subtypeVal j
  unfold twistedHomologyToBorelMooreHomologyComplOfExhaustion
    twistedHomologyToBorelMooreHomologyComplOfIsClosed
  infer_instance

/-- **Compact-pair Borel–Moore comparison isomorphism** for an explicit exhaustion `K`. -/
def twistedHomologyIsoBorelMooreHomologyComplOfExhaustion
    (K : CompactExhaustion (Aᶜ : Set X)) (j : ℕ) :
    (TopPair.ofSubset A).twistedHomology L j ≅
      borelMooreHomology ((pullback (X := TopCat.of (Aᶜ : Set X))
        (ContinuousMap.subtypeVal Aᶜ)).obj L) j :=
  have := isIso_twistedHomologyToBorelMooreHomologyComplOfExhaustion_of_cofinal_nhds_set
    hA hU_open hAU hU_cofinal L hU_qi K j
  asIso (twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j)

/-- The forward map of `twistedHomologyIsoBorelMooreHomologyComplOfExhaustion` is
`twistedHomologyToBorelMooreHomologyComplOfExhaustion`. -/
@[simp] theorem twistedHomologyIsoBorelMooreHomologyComplOfExhaustion_hom
    (K : CompactExhaustion (Aᶜ : Set X)) (j : ℕ) :
    (twistedHomologyIsoBorelMooreHomologyComplOfExhaustion
        hA hU_open hAU hU_cofinal L hU_qi K j).hom =
      twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j := (rfl)

/-- **Compact-pair comparison isomorphism** `H_j(X, A; L) ≅ H_j^{BM}(X \ A; L|_{X \ A})`. -/
def twistedHomologyIsoBorelMooreHomologyCompl (j : ℕ) :
    (TopPair.ofSubset A).twistedHomology L j ≅
      borelMooreHomology ((pullback (X := TopCat.of (Aᶜ : Set X))
        (ContinuousMap.subtypeVal Aᶜ)).obj L) j :=
  twistedHomologyIsoBorelMooreHomologyComplOfExhaustion hA hU_open hAU hU_cofinal L hU_qi
    (CompactExhaustion.complOfCofinalNhdsSet hA hU_open hAU hU_cofinal) j

/-- The forward map of `twistedHomologyIsoBorelMooreHomologyCompl` is
`twistedHomologyToBorelMooreHomologyCompl`. -/
@[simp] theorem twistedHomologyIsoBorelMooreHomologyCompl_hom
    [WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)] (j : ℕ) :
    (twistedHomologyIsoBorelMooreHomologyCompl hA hU_open hAU hU_cofinal L hU_qi j).hom =
      twistedHomologyToBorelMooreHomologyCompl hA L j :=
  twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq_twistedHomologyToBorelMooreHomologyCompl
    hA L (CompactExhaustion.complOfCofinalNhdsSet hA hU_open hAU hU_cofinal) j

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

/-- The forward map of
`twistedHomologyIsoBorelMooreHomologyComplOfExhaustionOfDeformationRetraction` is
`twistedHomologyToBorelMooreHomologyComplOfExhaustion`. -/
@[simp] theorem twistedHomologyIsoBorelMooreHomologyComplOfExhaustionOfDeformationRetraction_hom
    (K : CompactExhaustion (Aᶜ : Set X)) (j : ℕ) :
    (twistedHomologyIsoBorelMooreHomologyComplOfExhaustionOfDeformationRetraction
        hA hU_open hAU hU_cofinal hU_ret L K j).hom =
      twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j := (rfl)

/-- **Compact-pair comparison isomorphism under deformation retractions.** -/
def twistedHomologyIsoBorelMooreHomologyComplOfDeformationRetraction (j : ℕ) :
    (TopPair.ofSubset A).twistedHomology L j ≅
      borelMooreHomology ((pullback (X := TopCat.of (Aᶜ : Set X))
        (ContinuousMap.subtypeVal Aᶜ)).obj L) j :=
  twistedHomologyIsoBorelMooreHomologyComplOfExhaustionOfDeformationRetraction
    hA hU_open hAU hU_cofinal hU_ret L
    (CompactExhaustion.complOfCofinalNhdsSet hA hU_open hAU hU_cofinal) j

/-- The forward map of `twistedHomologyIsoBorelMooreHomologyComplOfDeformationRetraction` is
`twistedHomologyToBorelMooreHomologyCompl`. -/
@[simp] theorem twistedHomologyIsoBorelMooreHomologyComplOfDeformationRetraction_hom
    [WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)] (j : ℕ) :
    (twistedHomologyIsoBorelMooreHomologyComplOfDeformationRetraction
        hA hU_open hAU hU_cofinal hU_ret L j).hom =
      twistedHomologyToBorelMooreHomologyCompl hA L j :=
  twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq_twistedHomologyToBorelMooreHomologyCompl
    hA L (CompactExhaustion.complOfCofinalNhdsSet hA hU_open hAU hU_cofinal) j

end DeformationRetraction

end CofinalNeighborhoods

end TauCeti.LocalCoefficientSystem
