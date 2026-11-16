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

For a closed subset `A` of a Hausdorff space `X` and a compact exhaustion `K` of `X \ A`, each
ambient image `TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ) '' K n` is compact (hence closed) with
`A ⊆ (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ) '' K n)ᶜ`. The triple quotient maps
`C(X, A; L) ⟶ C(X, (Subtype.val '' K n)ᶜ; L)` induce a chain map
`relativeToOpenRestrictionLim : C(X, A; L) ⟶ (openRestrictionTower _ L K).limComplex`. Composing on
homology with the inverse of the open-restriction excision isomorphism yields the comparison map
`twistedHomologyToBorelMooreHomologyCompl : H_j(X, A; L) ⟶ H_j^{BM}(X \ A; L|_{X \ A})`, proved
exhaustion-independent, natural in `L`, compatible with closed-subset enlargement `A ⊆ B`, natural
under maps of pairs whose restriction to complements is proper, and compatible with
`borelMooreHomologyOpenRestriction`.

When `X` is compact Hausdorff and `A` admits a countable cofinal family `U : ℕ → Set X` of open
neighbourhoods with quasi-isomorphic triple quotient maps `C(X, A; L) ⟶ C(X, U n; L)` — in
particular, when each `U n` deformation retracts onto `A` — `CompactExhaustion.complOfCofinalNhds`
and `ComplexTower.quasiIso_isLimitLimComplexCone_lift` make this comparison map an isomorphism
`twistedHomologyIsoBorelMooreHomologyCompl` (and
`twistedHomologyIsoBorelMooreHomologyComplOfDeformationRetraction`).

## References

* A. Borel and J. C. Moore, *Homology theory for locally compact spaces*, Michigan Math. J. 7
  (1960), 137–159.
* G. E. Bredon, *Sheaf Theory*, 2nd ed., Graduate Texts in Mathematics 170, Chapter V.
* B. Iversen, *Cohomology of Sheaves*, Universitext, Springer, 1986, Chapter IX.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Topology

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R]

section ComparisonMap

variable {X : TopCat.{v}}

/-- The cone from `C(X, A; L)` to
`openRestrictionTower (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K` whose stage-`n` leg is the
triple quotient map `C(X, A; L) ⟶ C(X, (Subtype.val '' K n)ᶜ; L)`. -/
private def relativeOpenRestrictionCone (A : Set X)
    (L : LocalCoefficientSystem.{u, v, max v w} R X) (K : CompactExhaustion (Aᶜ : Set X)) :
    Cone (openRestrictionTower (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K) where
  pt := (TopPair.ofSubset A).twistedChainComplex L
  π := NatTrans.ofOpSequence
    (fun n ↦ (TopTriple.ofSubset
      (Set.subset_compl_comm.2 (Subtype.coe_image_subset Aᶜ (K n)))).twistedChainComplexTotalToOuter
        L)
    fun n ↦ (TopPair.ofSubset A).twistedChainComplex_hom_ext L <|
      (congrArg (_ ≫ ·) (Category.id_comp _)).trans <|
        ((TopTriple.ofSubset (Set.subset_compl_comm.2
          (Subtype.coe_image_subset Aᶜ (K n)))).twistedChainComplexπ_comp_totalToOuter L).trans
          (((TopTriple.ofSubset (Set.subset_compl_comm.2
            (Subtype.coe_image_subset Aᶜ (K (n + 1))))).twistedChainComplexπ_comp_totalToOuter_assoc
              L _).trans
            (twistedChainComplexπ_comp_openRestrictionTower_map
              (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K
              (homOfLE (Nat.le_succ n)).op)).symm

private lemma relativeOpenRestrictionCone_pt (A : Set X)
    (L : LocalCoefficientSystem.{u, v, max v w} R X) (K : CompactExhaustion (Aᶜ : Set X)) :
    (relativeOpenRestrictionCone A L K).pt = (TopPair.ofSubset A).twistedChainComplex L :=
  rfl

private lemma relativeOpenRestrictionCone_π_app (A : Set X)
    (L : LocalCoefficientSystem.{u, v, max v w} R X) (K : CompactExhaustion (Aᶜ : Set X))
    (n : ℕ) :
    (relativeOpenRestrictionCone A L K).π.app (op n) =
      (TopTriple.ofSubset
        (Set.subset_compl_comm.2
          (Subtype.coe_image_subset Aᶜ (K n)))).twistedChainComplexTotalToOuter L :=
  rfl

/-- The canonical chain map from `C(X, A; L)` to the limit complex of
`openRestrictionTower (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K`. -/
def relativeToOpenRestrictionLim (A : Set X) (L : LocalCoefficientSystem.{u, v, max v w} R X)
    (K : CompactExhaustion (Aᶜ : Set X)) :
    (TopPair.ofSubset A).twistedChainComplex L ⟶
      (openRestrictionTower (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K).limComplex :=
  (openRestrictionTower (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K).isLimitLimComplexCone.lift
    (relativeOpenRestrictionCone A L K)

@[reassoc (attr := simp)]
lemma relativeToOpenRestrictionLim_comp_π (A : Set X)
    (L : LocalCoefficientSystem.{u, v, max v w} R X) (K : CompactExhaustion (Aᶜ : Set X))
    (n : ℕ) :
    relativeToOpenRestrictionLim A L K ≫
        (openRestrictionTower (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K).limComplexπ n =
      (TopTriple.ofSubset
        (Set.subset_compl_comm.2
          (Subtype.coe_image_subset Aᶜ (K n)))).twistedChainComplexTotalToOuter L := by
  rw [← relativeOpenRestrictionCone_π_app A L K n]
  exact (openRestrictionTower (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L
    K).isLimitLimComplexCone.fac (relativeOpenRestrictionCone A L K) (op n)

/-- On absolute twisted chains on `X`, projecting to `C(X, A; L)` and mapping to the ambient
relative tower agrees with viewing finite chains as locally finite chains and restricting. -/
@[reassoc (attr := simp)]
theorem twistedChainComplexπ_comp_relativeToOpenRestrictionLim (A : Set X)
    (L : LocalCoefficientSystem.{u, v, max v w} R X) (K : CompactExhaustion (Aᶜ : Set X)) :
    (TopPair.ofSubset A).twistedChainComplexπ L ≫ relativeToOpenRestrictionLim A L K =
      toLocallyFiniteChainComplex L ≫
        locallyFiniteChainComplexToOpenRestrictionLim
          (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K :=
  (openRestrictionTower (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K).limComplex_hom_ext
    fun n ↦
    (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (relativeToOpenRestrictionLim_comp_π A L K n)).trans <|
        ((TopTriple.ofSubset (Set.subset_compl_comm.2
          (Subtype.coe_image_subset Aᶜ (K n)))).twistedChainComplexπ_comp_totalToOuter L).trans <|
          (TopPair.toLocallyFiniteChainComplex_comp_locallyFiniteChainComplexToRelative
            (TopPair.ofSubset (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ) '' K n)ᶜ) L _).symm.trans
            <| (congrArg (_ ≫ ·) (locallyFiniteChainComplexToOpenRestrictionLim_comp_π
              (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K n).symm).trans
              (Category.assoc _ _ _).symm

@[reassoc (attr := simp)]
lemma relativeToOpenRestrictionLim_comp_limComplexMap {A : Set X}
    (L : LocalCoefficientSystem.{u, v, max v w} R X) {K K' : CompactExhaustion (Aᶜ : Set X)}
    (h : ∀ n, K n ⊆ K' n) :
    relativeToOpenRestrictionLim A L K' ≫
        ComplexTower.limComplexMap
          (openRestrictionTowerMap (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L h) =
      relativeToOpenRestrictionLim A L K := by
  refine (openRestrictionTower (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L
    K).limComplex_hom_ext fun n ↦
    (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (ComplexTower.limComplexMap_comp_π _ n)).trans <|
        (relativeToOpenRestrictionLim_comp_π_assoc A L K' n _).trans <|
          (?_ : _ = _).trans (relativeToOpenRestrictionLim_comp_π A L K n).symm
  refine (TopPair.ofSubset A).twistedChainComplex_hom_ext L <|
    ((TopTriple.ofSubset (Set.subset_compl_comm.2
      (Subtype.coe_image_subset Aᶜ (K' n)))).twistedChainComplexπ_comp_totalToOuter_assoc L _).trans
      <| (twistedChainComplexπ_comp_openRestrictionTowerMap_app
        (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L h n).trans
        ((TopTriple.ofSubset (Set.subset_compl_comm.2
          (Subtype.coe_image_subset Aᶜ (K n)))).twistedChainComplexπ_comp_totalToOuter L).symm

@[reassoc]
lemma twistedChainComplexCoefficientMap_comp_relativeToOpenRestrictionLim (A : Set X)
    {L L' : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ L')
    (K : CompactExhaustion (Aᶜ : Set X)) :
    (TopPair.ofSubset A).twistedChainComplexCoefficientMap η ≫
        relativeToOpenRestrictionLim A L' K =
      relativeToOpenRestrictionLim A L K ≫
        ComplexTower.limComplexMap
          (openRestrictionTowerCoefficientMap (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) K η) :=
  (openRestrictionTower (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L' K).limComplex_hom_ext
    fun n ↦ (TopPair.ofSubset A).twistedChainComplex_hom_ext L <|
      ((Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ _)
          ((TopPair.ofSubset A).twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc
            η _)).trans <|
          (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans <|
            (congrArg (_ ≫ ·)
              (congrArg (_ ≫ ·) (relativeToOpenRestrictionLim_comp_π A L' K n))).trans
              (congrArg (_ ≫ ·) ((TopTriple.ofSubset (Set.subset_compl_comm.2
                (Subtype.coe_image_subset Aᶜ (K n)))).twistedChainComplexπ_comp_totalToOuter
                  L'))).trans
        ((congrArg (_ ≫ ·) <| (Category.assoc _ _ _).trans <|
          (congrArg (_ ≫ ·) (ComplexTower.limComplexMap_comp_π
            (openRestrictionTowerCoefficientMap
              (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) K η) n)).trans
            (relativeToOpenRestrictionLim_comp_π_assoc A L K n _)).trans <|
          ((TopTriple.ofSubset (Set.subset_compl_comm.2
            (Subtype.coe_image_subset Aᶜ (K n)))).twistedChainComplexπ_comp_totalToOuter_assoc
              L _).trans <|
            (congrArg (_ ≫ ·)
              (openRestrictionTowerCoefficientMap_app
                (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) K η n)).trans
              (TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap
                (TopPair.ofSubset (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ) '' K n)ᶜ) η)).symm

section T2

variable [T2Space X] {A : Set X} (hA : IsClosed A)
  (L : LocalCoefficientSystem.{u, v, max v w} R X) (K : CompactExhaustion (Aᶜ : Set X))

/-- **Comparison morphism from relative twisted homology to Borel–Moore homology of the
complement**, defined with respect to an explicit compact exhaustion `K` of `Aᶜ` (and independent of
`K` by `twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq`). -/
def twistedHomologyToBorelMooreHomologyComplOfExhaustion (j : ℕ) :
    (TopPair.ofSubset A).twistedHomology L j ⟶
      borelMooreHomology ((pullback (X := TopCat.of (Aᶜ : Set X))
        (ContinuousMap.subtypeVal Aᶜ)).obj L) j :=
  have := isIso_homologyMap_locallyFiniteChainComplexOpenRestrictionExcision
    (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) hA.isOpen_compl.isOpenEmbedding_subtypeVal L K j
  HomologicalComplex.homologyMap (relativeToOpenRestrictionLim A L K) j ≫
    inv (HomologicalComplex.homologyMap
      (locallyFiniteChainComplexOpenRestrictionExcision
        (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ))
        hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective L K) j)

/-- Characterizing equation of `twistedHomologyToBorelMooreHomologyComplOfExhaustion`: followed by
the excision isomorphism into the homology of `(openRestrictionTower _ L K).limComplex`, it is the
map induced by `relativeToOpenRestrictionLim`. -/
@[reassoc (attr := simp)]
theorem twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap (j : ℕ) :
    twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j ≫
        HomologicalComplex.homologyMap
          (locallyFiniteChainComplexOpenRestrictionExcision
            (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ))
            hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective L K) j =
      HomologicalComplex.homologyMap (relativeToOpenRestrictionLim A L K) j := by
  have := isIso_homologyMap_locallyFiniteChainComplexOpenRestrictionExcision
    (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) hA.isOpen_compl.isOpenEmbedding_subtypeVal L K j
  simp [twistedHomologyToBorelMooreHomologyComplOfExhaustion]

/-- Uniqueness criterion for `twistedHomologyToBorelMooreHomologyComplOfExhaustion`. -/
theorem eq_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion
    {M : ModuleCat.{max v w} R} {j : ℕ}
    {g : M ⟶ (TopPair.ofSubset A).twistedHomology L j}
    {f : M ⟶ borelMooreHomology ((pullback (X := TopCat.of (Aᶜ : Set X))
      (ContinuousMap.subtypeVal Aᶜ)).obj L) j}
    (hf : f ≫ HomologicalComplex.homologyMap
        (locallyFiniteChainComplexOpenRestrictionExcision
          (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ))
          hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective L K) j =
      g ≫ HomologicalComplex.homologyMap (relativeToOpenRestrictionLim A L K) j) :
    f = g ≫ twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j := by
  have := isIso_homologyMap_locallyFiniteChainComplexOpenRestrictionExcision
    (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) hA.isOpen_compl.isOpenEmbedding_subtypeVal L K j
  apply (cancel_mono (HomologicalComplex.homologyMap
    (locallyFiniteChainComplexOpenRestrictionExcision
      (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ))
      hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective L K) j)).1
  rw [Category.assoc, twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap, hf]

private lemma twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq_of_subset
    {K' : CompactExhaustion (Aᶜ : Set X)} (h : ∀ n, K n ⊆ K' n) (j : ℕ) :
    twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K' j =
      twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j := by
  refine (eq_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K (g := 𝟙 _) ?_).trans
    (Category.id_comp _)
  rw [Category.id_comp, ← locallyFiniteChainComplexOpenRestrictionExcision_comp_limComplexMap
      (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ))
      hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective L h,
    HomologicalComplex.homologyMap_comp,
    twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap_assoc,
    ← HomologicalComplex.homologyMap_comp, relativeToOpenRestrictionLim_comp_limComplexMap]

/-- **Exhaustion independence** of the comparison morphism
`H_j(X, A; L) ⟶ H_j^{BM}(X \ A; L|_{X \ A})`. -/
theorem twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq
    (K' : CompactExhaustion (Aᶜ : Set X)) (j : ℕ) :
    twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j =
      twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K' j :=
  (twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq_of_subset hA L K
    (CompactExhaustion.subset_sup_left K K') j).symm.trans
    (twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq_of_subset hA L K'
      (CompactExhaustion.subset_sup_right K K') j)

/-- **Naturality in the local coefficient system** of the comparison morphism
`H_j(X, A; L) ⟶ H_j^{BM}(X \ A; L|_{X \ A})`. -/
@[reassoc]
theorem twistedHomologyToBorelMooreHomologyComplOfExhaustion_naturality
    {L' : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ L') (j : ℕ) :
    (TopPair.ofSubset A).twistedHomologyCoefficientMap η j ≫
        twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L' K j =
      twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j ≫
        borelMooreHomologyCoefficientMap
          ((pullback (X := TopCat.of (Aᶜ : Set X)) (ContinuousMap.subtypeVal Aᶜ)).map η) j := by
  symm
  refine eq_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L' K ?_
  have hchain :
      locallyFiniteChainComplexCoefficientMap
          ((pullback (X := TopCat.of (Aᶜ : Set X)) (ContinuousMap.subtypeVal Aᶜ)).map η) ≫
        locallyFiniteChainComplexOpenRestrictionExcision
          (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ))
          hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective L' K =
        locallyFiniteChainComplexOpenRestrictionExcision
          (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ))
          hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective L K ≫
          ComplexTower.limComplexMap
            (openRestrictionTowerCoefficientMap
              (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) K η) :=
    locallyFiniteChainComplexCoefficientMap_comp_openRestrictionExcision
      (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ))
      hA.isOpen_compl.isOpenEmbedding_subtypeVal.injective η K
  rw [Category.assoc, ← HomologicalComplex.homologyMap_comp, hchain,
    HomologicalComplex.homologyMap_comp,
    twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap_assoc,
    ← HomologicalComplex.homologyMap_comp,
    ← twistedChainComplexCoefficientMap_comp_relativeToOpenRestrictionLim,
    HomologicalComplex.homologyMap_comp]

/-- **Compatibility with closed-subset enlargement:** for nested closed subsets `A ⊆ B`, the
comparison morphism intertwines the triple quotient `H_j(X, A; L) ⟶ H_j(X, B; L)` with open
restriction along `Bᶜ ↪ Aᶜ`. -/
@[reassoc]
theorem twistedHomologyTotalToOuter_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion
    {B : Set X} (hB : IsClosed B) (hAB : A ⊆ B)
    (K_B : CompactExhaustion (Bᶜ : Set X)) (j : ℕ) :
    (TopTriple.ofSubset hAB).twistedHomologyTotalToOuter L j ≫
        twistedHomologyToBorelMooreHomologyComplOfExhaustion hB L K_B j ≫
          borelMooreHomologyCoefficientMap
            ((pullbackCompIso
              (X := TopCat.of (Bᶜ : Set X)) (Y := TopCat.of (Aᶜ : Set X))
              (ContinuousMap.inclusion (Set.compl_subset_compl.2 hAB))
              (ContinuousMap.subtypeVal Aᶜ)).hom.app L) j =
      twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j ≫
        borelMooreHomologyOpenRestrictionOfExhaustion
          (TopCat.ofHom (ContinuousMap.inclusion (Set.compl_subset_compl.2 hAB)))
          (IsOpenEmbedding.of_comp (ContinuousMap.inclusion (Set.compl_subset_compl.2 hAB))
            hA.isOpen_compl.isOpenEmbedding_subtypeVal
            hB.isOpen_compl.isOpenEmbedding_subtypeVal)
          ((pullback (X := TopCat.of (Aᶜ : Set X)) (ContinuousMap.subtypeVal Aᶜ)).obj L) K_B j := by
  let iA : TopCat.of (Aᶜ : Set X) ⟶ X := TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)
  let ι : TopCat.of (Bᶜ : Set X) ⟶ TopCat.of (Aᶜ : Set X) :=
    TopCat.ofHom (ContinuousMap.inclusion (Set.compl_subset_compl.2 hAB))
  have hiA : IsOpenEmbedding iA.hom := hA.isOpen_compl.isOpenEmbedding_subtypeVal
  have hiB : IsOpenEmbedding (ι ≫ iA).hom := hB.isOpen_compl.isOpenEmbedding_subtypeVal
  have hι : IsOpenEmbedding ι.hom := IsOpenEmbedding.of_comp ι.hom hiA hiB
  let K' : CompactExhaustion (Aᶜ : Set X) := K.supImage ι.hom.continuous hι.isOpenMap K_B
  rw [twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq hA L K K' j]
  have hBA (n : ℕ) : ι '' K_B n ⊆ K' n :=
    K.image_subset_supImage ι.hom.continuous hι.isOpenMap K_B n
  have hXA (n : ℕ) : (ι ≫ iA) '' K_B n ⊆ iA '' K' n := by
    rw [TopCat.coe_comp, Set.image_comp]
    exact Set.image_mono (hBA n)
  have hMaps (n : ℕ) : Set.MapsTo iA (ι '' K_B n)ᶜ ((ι ≫ iA) '' K_B n)ᶜ :=
    fun x hx ⟨w, hw, hwx⟩ ↦ hx ⟨w, hw, hiA.injective hwx⟩
  let qA : relativeChainComplexTower ((pullback iA.hom).obj L) K' ⟶
      openRestrictionTower ι ((pullback iA.hom).obj L) K_B :=
    complChainComplexTowerMap ((pullback iA.hom).obj L)
      (fun n ↦ Set.image_mono (K_B.subset_succ n)) K'.subset_succ hBA
  let qX : openRestrictionTower iA L K' ⟶ openRestrictionTower (ι ≫ iA) L K_B :=
    complChainComplexTowerMap L (fun n ↦ Set.image_mono (K_B.subset_succ n))
      (fun n ↦ Set.image_mono (K'.subset_succ n)) hXA
  let eBX : openRestrictionTower ι ((pullback iA.hom).obj L) K_B ⟶
      openRestrictionTower (ι ≫ iA) L K_B :=
    complChainComplexTowerPairMap iA L (fun n ↦ Set.image_mono (K_B.subset_succ n))
      (fun n ↦ Set.image_mono (K_B.subset_succ n)) hMaps
  have hSq1 : openRestrictionExcisionTowerMap iA hiA.injective L K' ≫ qX = qA ≫ eBX := by
    rw [openRestrictionExcisionTowerMap_eq_complChainComplexTowerPairMap]
    exact (complChainComplexTowerMap_comp_complChainComplexTowerPairMap iA L
      (fun n ↦ Set.image_mono (K_B.subset_succ n)) K'.subset_succ
      (fun n ↦ Set.image_mono (K_B.subset_succ n)) (fun n ↦ Set.image_mono (K'.subset_succ n))
      hMaps _ hBA hXA).symm
  let eα : (pullback (ι ≫ iA).hom).obj L ≅ (pullback ι.hom).obj ((pullback iA.hom).obj L) :=
    (pullbackCompIso ι.hom iA.hom).app L
  have hα_inv_hom :
      borelMooreHomologyCoefficientMap eα.inv j ≫ borelMooreHomologyCoefficientMap eα.hom j =
        𝟙 _ := by
    rw [← borelMooreHomologyCoefficientMap_comp, eα.inv_hom_id, borelMooreHomologyCoefficientMap_id]
  have hSq2 :
      openRestrictionExcisionTowerMap (ι ≫ iA) hiB.injective L K_B =
        relativeChainComplexTowerCoefficientMap K_B eα.hom ≫
          openRestrictionExcisionTowerMap ι hι.injective ((pullback iA.hom).obj L) K_B ≫ eBX := by
    have hc : relativeChainComplexTowerCoefficientMap K_B eα.hom =
        complChainComplexTowerCoefficientMap K_B K_B.subset_succ eα.hom :=
      NatTrans.ext <| funext fun n ↦
        (relativeChainComplexTowerCoefficientMap_app K_B eα.hom n.unop).trans
          (complChainComplexTowerCoefficientMap_app K_B K_B.subset_succ eα.hom n.unop).symm
    rw [hc, openRestrictionExcisionTowerMap_eq_complChainComplexTowerPairMap,
      openRestrictionExcisionTowerMap_eq_complChainComplexTowerPairMap]
    exact complChainComplexTowerPairMap_comp ι iA L K_B.subset_succ
      (fun n ↦ Set.image_mono (K_B.subset_succ n)) (fun n ↦ Set.image_mono (K_B.subset_succ n))
      _ hMaps _
  have hlim2 :
      locallyFiniteChainComplexOpenRestrictionExcision (ι ≫ iA) hiB.injective L K_B =
        locallyFiniteChainComplexCoefficientMap eα.hom ≫
          locallyFiniteChainComplexOpenRestrictionExcision ι hι.injective
            ((pullback iA.hom).obj L) K_B ≫ ComplexTower.limComplexMap eBX := by
    rw [locallyFiniteChainComplexOpenRestrictionExcision_def,
      locallyFiniteChainComplexOpenRestrictionExcision_def, hSq2,
      ComplexTower.limComplexMap_comp, ComplexTower.limComplexMap_comp,
      ← Category.assoc, ← locallyFiniteChainComplexCoefficientMap_comp_isoLimComplex_hom,
      Category.assoc, Category.assoc]
  have hqA :
      (locallyFiniteChainComplexIsoLimComplex ((pullback iA.hom).obj L) K').hom ≫
          ComplexTower.limComplexMap qA =
        locallyFiniteChainComplexToOpenRestrictionLim ι ((pullback iA.hom).obj L) K_B := by
    rw [locallyFiniteChainComplexToOpenRestrictionLim_eq_toComplLim]
    exact locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexMap_compl
      ((pullback iA.hom).obj L) K' (fun n ↦ Set.image_mono (K_B.subset_succ n))
      (fun n ↦ (K_B.isCompact n).image ι.hom.continuous) hBA
  have hRel :
      (TopTriple.ofSubset hAB).twistedChainComplexTotalToOuter L ≫
          relativeToOpenRestrictionLim B L K_B =
        relativeToOpenRestrictionLim A L K' ≫ ComplexTower.limComplexMap qX := by
    refine (openRestrictionTower (ι ≫ iA) L K_B).limComplex_hom_ext fun n ↦
      (TopPair.ofSubset A).twistedChainComplex_hom_ext L ?_
    exact ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans (Category.assoc _ _ _).symm).trans <|
      (congrArg₂ (· ≫ ·) ((TopTriple.ofSubset hAB).twistedChainComplexπ_comp_totalToOuter L)
        (relativeToOpenRestrictionLim_comp_π B L K_B n)).trans <|
      ((TopTriple.ofSubset (Set.subset_compl_comm.2
        (Subtype.coe_image_subset Bᶜ (K_B n)))).twistedChainComplexπ_comp_totalToOuter L).trans <|
      (twistedChainComplexπ_comp_complChainComplexTowerMap_app L
        (fun n ↦ Set.image_mono (K_B.subset_succ n))
        (fun n ↦ Set.image_mono (K'.subset_succ n)) hXA n).symm.trans <|
      (congrArg (· ≫ qX.app (op n))
        (((TopTriple.ofSubset (Set.subset_compl_comm.2
          (Subtype.coe_image_subset Aᶜ (K' n)))).twistedChainComplexπ_comp_totalToOuter
            L).symm.trans
          (congrArg (_ ≫ ·) (relativeToOpenRestrictionLim_comp_π A L K' n).symm))).trans <|
      (Category.assoc _ _ _).trans <| congrArg (_ ≫ ·) <|
        (Category.assoc _ _ _).trans <|
          (congrArg (_ ≫ ·) (ComplexTower.limComplexMap_comp_π qX n).symm).trans
            (Category.assoc _ _ _).symm
  suffices hmain :
      twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K' j ≫
          borelMooreHomologyOpenRestrictionOfExhaustion ι hι ((pullback iA.hom).obj L) K_B j ≫
            borelMooreHomologyCoefficientMap eα.inv j =
        (TopTriple.ofSubset hAB).twistedHomologyTotalToOuter L j ≫
          twistedHomologyToBorelMooreHomologyComplOfExhaustion hB L K_B j by
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hmain.symm)).trans <|
      (Category.assoc _ _ _).trans <| congrArg (_ ≫ ·) <|
        (Category.assoc _ _ _).trans <|
          (congrArg (_ ≫ ·) hα_inv_hom).trans (Category.comp_id _)
  refine eq_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion hB L K_B ?_
  have hHlim2 :
      HomologicalComplex.homologyMap
          (locallyFiniteChainComplexOpenRestrictionExcision (ι ≫ iA) hiB.injective L K_B) j =
        borelMooreHomologyCoefficientMap eα.hom j ≫
          HomologicalComplex.homologyMap
            (locallyFiniteChainComplexOpenRestrictionExcision ι hι.injective
              ((pullback iA.hom).obj L) K_B) j ≫
          HomologicalComplex.homologyMap (ComplexTower.limComplexMap eBX) j :=
    (congrArg (HomologicalComplex.homologyMap · j) hlim2).trans <|
      (HomologicalComplex.homologyMap_comp _ _ j).trans <|
        congrArg (_ ≫ ·) (HomologicalComplex.homologyMap_comp _ _ j)
  have hH :
      borelMooreHomologyOpenRestrictionOfExhaustion ι hι ((pullback iA.hom).obj L) K_B j ≫
          borelMooreHomologyCoefficientMap eα.inv j ≫
          HomologicalComplex.homologyMap
            (locallyFiniteChainComplexOpenRestrictionExcision (ι ≫ iA) hiB.injective L K_B) j =
        HomologicalComplex.homologyMap
          (locallyFiniteChainComplexOpenRestrictionExcision iA hiA.injective L K') j ≫
          HomologicalComplex.homologyMap (ComplexTower.limComplexMap qX) j := by
    rw [hHlim2, ← Category.assoc (borelMooreHomologyCoefficientMap eα.inv j), hα_inv_hom,
      Category.id_comp, ← Category.assoc,
      borelMooreHomologyOpenRestrictionOfExhaustion_comp_homologyMap,
      ← HomologicalComplex.homologyMap_comp, ← hqA, Category.assoc,
      ← ComplexTower.limComplexMap_comp, ← hSq1, ComplexTower.limComplexMap_comp,
      ← Category.assoc, HomologicalComplex.homologyMap_comp,
      ← locallyFiniteChainComplexOpenRestrictionExcision_def]
  exact (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans hH)).trans <|
      (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ _)
          (twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap
            hA L K' j)).trans <|
          (HomologicalComplex.homologyMap_comp _ _ j).symm.trans <|
            (congrArg (HomologicalComplex.homologyMap · j) hRel.symm).trans
              (HomologicalComplex.homologyMap_comp _ _ j)

/-- **Naturality under maps of pairs with proper restriction to complements.** Given a map of pairs
`φ : (X', A') ⟶ (X, A)` whose restriction `fCompl : A'ᶜ ⟶ Aᶜ` is proper (which holds automatically
whenever `TopPair.Hom.fst φ` is proper and satisfies `(TopPair.Hom.fst φ) ⁻¹' A = A'`, by
`IsProperMap.of_isEmbedding_of_range_eq`), the comparison morphism intertwines
`TopPair.twistedHomologyMap` with `borelMooreHomologyMap fCompl`. -/
@[reassoc]
theorem twistedHomologyMap_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion
    {X' : TopCat.{v}} [T2Space X'] {A' : Set X'} (hA' : IsClosed A')
    (φ : TopPair.ofSubset A' ⟶ TopPair.ofSubset A)
    (fCompl : TopCat.of (A'ᶜ : Set X') ⟶ TopCat.of (Aᶜ : Set X))
    (hfCompl : IsProperMap fCompl.hom)
    (hw : fCompl ≫ TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ) =
      TopCat.ofHom (ContinuousMap.subtypeVal A'ᶜ) ≫ TopPair.Hom.fst φ)
    (K' : CompactExhaustion (A'ᶜ : Set X')) (j : ℕ) :
    TopPair.twistedHomologyMap φ L j ≫
        twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j =
      twistedHomologyToBorelMooreHomologyComplOfExhaustion hA'
          ((pullback (TopPair.Hom.fst φ).hom).obj L) K' j ≫
        borelMooreHomologyCoefficientMap
          (((pullbackCompIso
              (TopCat.ofHom (ContinuousMap.subtypeVal A'ᶜ)).hom
              (TopPair.Hom.fst φ).hom).app L).symm ≪≫
            eqToIso (congrArg (fun k : TopCat.of (A'ᶜ : Set X') ⟶ X ↦
              (pullback k.hom).obj L) hw.symm) ≪≫
            (pullbackCompIso fCompl.hom
              (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)).hom).app L).hom j ≫
        borelMooreHomologyMap fCompl hfCompl
          ((pullback (X := TopCat.of (Aᶜ : Set X)) (ContinuousMap.subtypeVal Aᶜ)).obj L) j := by
  let iA : TopCat.of (Aᶜ : Set X) ⟶ X := TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)
  let iA' : TopCat.of (A'ᶜ : Set X') ⟶ X' := TopCat.ofHom (ContinuousMap.subtypeVal A'ᶜ)
  let f : X' ⟶ X := TopPair.Hom.fst φ
  have hiA : IsOpenEmbedding iA.hom := hA.isOpen_compl.isOpenEmbedding_subtypeVal
  have hiA' : IsOpenEmbedding iA'.hom := hA'.isOpen_compl.isOpenEmbedding_subtypeVal
  let α : (pullback iA'.hom).obj ((pullback f.hom).obj L) ⟶
      (pullback fCompl.hom).obj ((pullback iA.hom).obj L) :=
    (((pullbackCompIso iA'.hom f.hom).app L).symm ≪≫
      eqToIso (congrArg (fun k : TopCat.of (A'ᶜ : Set X') ⟶ X ↦ (pullback k.hom).obj L) hw.symm) ≪≫
      (pullbackCompIso fCompl.hom iA.hom).app L).hom
  let K'' : CompactExhaustion (A'ᶜ : Set X') := K'.supPreimage hfCompl K
  rw [twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq hA'
    ((pullback (TopPair.Hom.fst φ).hom).obj L) K' K'' j]
  have hfCompl_maps (n : ℕ) : Set.MapsTo fCompl (K'' n)ᶜ (K n)ᶜ := fun x hx hfx ↦
    hx (K'.preimage_subset_supPreimage hfCompl K n hfx)
  have hf_maps (n : ℕ) : Set.MapsTo f (iA' '' K'' n)ᶜ (iA '' K n)ᶜ := by
    rintro x hx ⟨y, hyK, hyx⟩
    have hyx' : y.1 = f x := hyx
    have hxA' : x ∉ A' := fun hx' ↦ by
      have hfxA : f x ∈ A := by
        have h := congrArg (fun k : TopCat.of (A' : Set X') ⟶ X ↦ k ⟨x, hx'⟩) (TopPair.Hom.w φ)
        exact h ▸ (TopPair.Hom.snd φ ⟨x, hx'⟩).2
      exact y.2 (hyx'.symm ▸ hfxA)
    have hfy : fCompl ⟨x, hxA'⟩ = y := Subtype.ext <| by
      have h := congrArg (fun k : TopCat.of (A'ᶜ : Set X') ⟶ X ↦ k ⟨x, hxA'⟩) hw
      exact h.trans hyx'.symm
    exact hx ⟨⟨x, hxA'⟩, K'.preimage_subset_supPreimage hfCompl K n (by simpa [hfy] using hyK), rfl⟩
  let pV : relativeChainComplexTower ((pullback fCompl.hom).obj ((pullback iA.hom).obj L)) K'' ⟶
      relativeChainComplexTower ((pullback iA.hom).obj L) K :=
    complChainComplexTowerPairMap fCompl ((pullback iA.hom).obj L)
      K''.subset_succ K.subset_succ hfCompl_maps
  let pU : openRestrictionTower iA' ((pullback f.hom).obj L) K'' ⟶
      openRestrictionTower iA L K :=
    complChainComplexTowerPairMap f L (fun n ↦ Set.image_mono (K''.subset_succ n))
      (fun n ↦ Set.image_mono (K.subset_succ n)) hf_maps
  have hpushV :
      locallyFiniteChainComplexMap fCompl hfCompl ((pullback iA.hom).obj L) ≫
          (locallyFiniteChainComplexIsoLimComplex ((pullback iA.hom).obj L) K).hom =
        (locallyFiniteChainComplexIsoLimComplex
            ((pullback fCompl.hom).obj ((pullback iA.hom).obj L)) K'').hom ≫
          ComplexTower.limComplexMap pV :=
    locallyFiniteChainComplexMap_comp_isoLimComplex_hom fCompl hfCompl ((pullback iA.hom).obj L)
      K'' K hfCompl_maps
  have hRel :
      TopPair.twistedChainComplexMap φ L ≫ relativeToOpenRestrictionLim A L K =
        relativeToOpenRestrictionLim A' ((pullback f.hom).obj L) K'' ≫
          ComplexTower.limComplexMap pU := by
    refine (openRestrictionTower iA L K).limComplex_hom_ext fun n ↦
      (TopPair.ofSubset A').twistedChainComplex_hom_ext ((pullback f.hom).obj L) ?_
    exact ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans (Category.assoc _ _ _).symm).trans <|
      (congrArg₂ (· ≫ ·) (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap φ L)
        (relativeToOpenRestrictionLim_comp_π A L K n)).trans <|
      (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) ((TopTriple.ofSubset (Set.subset_compl_comm.2
        (Subtype.coe_image_subset Aᶜ (K n)))).twistedChainComplexπ_comp_totalToOuter L)).trans <|
      (twistedChainComplexπ_comp_complChainComplexTowerPairMap_app f L
        (fun n ↦ Set.image_mono (K''.subset_succ n))
        (fun n ↦ Set.image_mono (K.subset_succ n)) hf_maps n).symm.trans <|
      (congrArg (· ≫ pU.app (op n))
        (((TopTriple.ofSubset (Set.subset_compl_comm.2
          (Subtype.coe_image_subset A'ᶜ (K'' n)))).twistedChainComplexπ_comp_totalToOuter
            ((pullback f.hom).obj L)).symm.trans
          (congrArg (_ ≫ ·)
            (relativeToOpenRestrictionLim_comp_π A' ((pullback f.hom).obj L) K'' n).symm))).trans <|
      (Category.assoc _ _ _).trans <| congrArg (_ ≫ ·) <|
        (Category.assoc _ _ _).trans <|
          (congrArg (_ ≫ ·) (ComplexTower.limComplexMap_comp_π pU n).symm).trans
            (Category.assoc _ _ _).symm
  have hsq :
      relativeChainComplexTowerCoefficientMap K'' α ≫ pV ≫
          openRestrictionExcisionTowerMap iA hiA.injective L K =
        openRestrictionExcisionTowerMap iA' hiA'.injective ((pullback f.hom).obj L) K'' ≫ pU := by
    have hc : relativeChainComplexTowerCoefficientMap K'' α =
        complChainComplexTowerCoefficientMap K'' K''.subset_succ α :=
      NatTrans.ext <| funext fun n ↦
        (relativeChainComplexTowerCoefficientMap_app K'' α n.unop).trans
          (complChainComplexTowerCoefficientMap_app K'' K''.subset_succ α n.unop).symm
    rw [hc, openRestrictionExcisionTowerMap_eq_complChainComplexTowerPairMap,
      openRestrictionExcisionTowerMap_eq_complChainComplexTowerPairMap]
    exact (complChainComplexTowerPairMap_naturality_square iA' f fCompl iA L hw.symm
      K''.subset_succ (fun n ↦ Set.image_mono (K''.subset_succ n))
      K.subset_succ (fun n ↦ Set.image_mono (K.subset_succ n))
      _ hf_maps hfCompl_maps _).symm
  symm
  refine eq_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K ?_
  have hchain :
      locallyFiniteChainComplexCoefficientMap α ≫
          locallyFiniteChainComplexMap fCompl hfCompl ((pullback iA.hom).obj L) ≫
          locallyFiniteChainComplexOpenRestrictionExcision iA hiA.injective L K =
        locallyFiniteChainComplexOpenRestrictionExcision iA' hiA'.injective
            ((pullback f.hom).obj L) K'' ≫
          ComplexTower.limComplexMap pU := by
    rw [locallyFiniteChainComplexOpenRestrictionExcision_def,
      locallyFiniteChainComplexOpenRestrictionExcision_def,
      ← Category.assoc (locallyFiniteChainComplexMap fCompl hfCompl _), hpushV,
      Category.assoc, Category.assoc,
      ← Category.assoc (locallyFiniteChainComplexCoefficientMap α),
      locallyFiniteChainComplexCoefficientMap_comp_isoLimComplex_hom,
      Category.assoc, ← ComplexTower.limComplexMap_comp,
      ← ComplexTower.limComplexMap_comp, hsq, ComplexTower.limComplexMap_comp,
      ← Category.assoc]
  have hHchain :
      borelMooreHomologyCoefficientMap α j ≫
          borelMooreHomologyMap fCompl hfCompl ((pullback iA.hom).obj L) j ≫
          HomologicalComplex.homologyMap
            (locallyFiniteChainComplexOpenRestrictionExcision iA hiA.injective L K) j =
        HomologicalComplex.homologyMap
            (locallyFiniteChainComplexOpenRestrictionExcision iA' hiA'.injective
              ((pullback f.hom).obj L) K'') j ≫
          HomologicalComplex.homologyMap (ComplexTower.limComplexMap pU) j := by
    calc
      _ = HomologicalComplex.homologyMap
            (locallyFiniteChainComplexCoefficientMap α ≫
              locallyFiniteChainComplexMap fCompl hfCompl ((pullback iA.hom).obj L) ≫
              locallyFiniteChainComplexOpenRestrictionExcision iA hiA.injective L K) j := by
          rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
      _ = _ := (congrArg (HomologicalComplex.homologyMap · j) hchain).trans
          (HomologicalComplex.homologyMap_comp _ _ j)
  exact (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans hHchain)).trans <|
      (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ _)
          (twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap
            hA' ((pullback f.hom).obj L) K'' j)).trans <|
          (HomologicalComplex.homologyMap_comp _ _ j).symm.trans <|
            (congrArg (HomologicalComplex.homologyMap · j) hRel.symm).trans
              (HomologicalComplex.homologyMap_comp _ _ j)

/-- **Compatibility with open restriction:** on absolute twisted homology of `X`, passing to
relative homology `H_j(X, A; L)` and applying the comparison map agrees with viewing finite chains
as Borel–Moore classes on `X` and restricting to `X \ A`. -/
@[reassoc (attr := simp)]
theorem twistedHomologyπ_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion (j : ℕ) :
    (TopPair.ofSubset A).twistedHomologyπ L j ≫
        twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j =
      twistedHomologyToBorelMooreHomology L j ≫
        borelMooreHomologyOpenRestrictionOfExhaustion
          (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ))
          hA.isOpen_compl.isOpenEmbedding_subtypeVal L K j := by
  refine eq_comp_borelMooreHomologyOpenRestrictionOfExhaustion
    (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ))
    hA.isOpen_compl.isOpenEmbedding_subtypeVal L K ?_
  rw [Category.assoc, twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap,
    ← HomologicalComplex.homologyMap_comp,
    twistedChainComplexπ_comp_relativeToOpenRestrictionLim]
  exact HomologicalComplex.homologyMap_comp _ _ j

/-- **Comparison morphism from relative twisted homology to Borel–Moore homology of the
complement** when `X \ A` is weakly locally compact and `σ`-compact. -/
def twistedHomologyToBorelMooreHomologyCompl
    [WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)] (j : ℕ) :
    (TopPair.ofSubset A).twistedHomology L j ⟶
      borelMooreHomology ((pullback (X := TopCat.of (Aᶜ : Set X))
        (ContinuousMap.subtypeVal Aᶜ)).obj L) j :=
  twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L
    (CompactExhaustion.choice (Aᶜ : Set X)) j

/-- Any compact exhaustion of `Aᶜ` computes `twistedHomologyToBorelMooreHomologyCompl`. -/
@[simp]
theorem
  twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq_twistedHomologyToBorelMooreHomologyCompl
    [WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)] (j : ℕ) :
    twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j =
      twistedHomologyToBorelMooreHomologyCompl hA L j :=
  twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq hA L K
    (CompactExhaustion.choice (Aᶜ : Set X)) j

/-- Naturality in the local coefficient system for `twistedHomologyToBorelMooreHomologyCompl`. -/
@[reassoc]
theorem twistedHomologyToBorelMooreHomologyCompl_naturality
    [WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)]
    {L' : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ L') (j : ℕ) :
    (TopPair.ofSubset A).twistedHomologyCoefficientMap η j ≫
        twistedHomologyToBorelMooreHomologyCompl hA L' j =
      twistedHomologyToBorelMooreHomologyCompl hA L j ≫
        borelMooreHomologyCoefficientMap
          ((pullback (X := TopCat.of (Aᶜ : Set X)) (ContinuousMap.subtypeVal Aᶜ)).map η) j :=
  twistedHomologyToBorelMooreHomologyComplOfExhaustion_naturality hA L
    (CompactExhaustion.choice (Aᶜ : Set X)) η j

/-- **Compatibility with closed-subset enlargement** for
`twistedHomologyToBorelMooreHomologyCompl`. -/
@[reassoc]
theorem twistedHomologyTotalToOuter_comp_twistedHomologyToBorelMooreHomologyCompl
    {B : Set X} (hB : IsClosed B) (hAB : A ⊆ B)
    [WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)]
    [WeaklyLocallyCompactSpace (Bᶜ : Set X)] [SigmaCompactSpace (Bᶜ : Set X)] (j : ℕ) :
    (TopTriple.ofSubset hAB).twistedHomologyTotalToOuter L j ≫
        twistedHomologyToBorelMooreHomologyCompl hB L j ≫
          borelMooreHomologyCoefficientMap
            ((pullbackCompIso
              (X := TopCat.of (Bᶜ : Set X)) (Y := TopCat.of (Aᶜ : Set X))
              (ContinuousMap.inclusion (Set.compl_subset_compl.2 hAB))
              (ContinuousMap.subtypeVal Aᶜ)).hom.app L) j =
      twistedHomologyToBorelMooreHomologyCompl hA L j ≫
        borelMooreHomologyOpenRestriction
          (TopCat.ofHom (ContinuousMap.inclusion (Set.compl_subset_compl.2 hAB)))
          (IsOpenEmbedding.of_comp (ContinuousMap.inclusion (Set.compl_subset_compl.2 hAB))
            hA.isOpen_compl.isOpenEmbedding_subtypeVal
            hB.isOpen_compl.isOpenEmbedding_subtypeVal)
          ((pullback (X := TopCat.of (Aᶜ : Set X)) (ContinuousMap.subtypeVal Aᶜ)).obj L) j := by
  rw [← borelMooreHomologyOpenRestrictionOfExhaustion_eq_borelMooreHomologyOpenRestriction _ _ _
    (CompactExhaustion.choice (Bᶜ : Set X))]
  exact twistedHomologyTotalToOuter_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion
    hA L (CompactExhaustion.choice (Aᶜ : Set X)) hB hAB (CompactExhaustion.choice (Bᶜ : Set X)) j

/-- **Naturality under maps of pairs with proper restriction to complements** for
`twistedHomologyToBorelMooreHomologyCompl`. -/
@[reassoc]
theorem twistedHomologyMap_comp_twistedHomologyToBorelMooreHomologyCompl
    {X' : TopCat.{v}} [T2Space X'] {A' : Set X'} (hA' : IsClosed A')
    [WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)]
    [WeaklyLocallyCompactSpace (A'ᶜ : Set X')] [SigmaCompactSpace (A'ᶜ : Set X')]
    (φ : TopPair.ofSubset A' ⟶ TopPair.ofSubset A)
    (fCompl : TopCat.of (A'ᶜ : Set X') ⟶ TopCat.of (Aᶜ : Set X))
    (hfCompl : IsProperMap fCompl.hom)
    (hw : fCompl ≫ TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ) =
      TopCat.ofHom (ContinuousMap.subtypeVal A'ᶜ) ≫ TopPair.Hom.fst φ) (j : ℕ) :
    TopPair.twistedHomologyMap φ L j ≫
        twistedHomologyToBorelMooreHomologyCompl hA L j =
      twistedHomologyToBorelMooreHomologyCompl hA' ((pullback (TopPair.Hom.fst φ).hom).obj L) j ≫
        borelMooreHomologyCoefficientMap
          (((pullbackCompIso
              (TopCat.ofHom (ContinuousMap.subtypeVal A'ᶜ)).hom
              (TopPair.Hom.fst φ).hom).app L).symm ≪≫
            eqToIso (congrArg (fun k : TopCat.of (A'ᶜ : Set X') ⟶ X ↦
              (pullback k.hom).obj L) hw.symm) ≪≫
            (pullbackCompIso fCompl.hom
              (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)).hom).app L).hom j ≫
        borelMooreHomologyMap fCompl hfCompl
          ((pullback (X := TopCat.of (Aᶜ : Set X)) (ContinuousMap.subtypeVal Aᶜ)).obj L) j :=
  twistedHomologyMap_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L
    (CompactExhaustion.choice (Aᶜ : Set X)) hA' φ fCompl hfCompl hw
    (CompactExhaustion.choice (A'ᶜ : Set X')) j

/-- Compatibility of `twistedHomologyToBorelMooreHomologyCompl` with open restriction from `X` to
`X \ A`. -/
@[reassoc (attr := simp)]
theorem twistedHomologyπ_comp_twistedHomologyToBorelMooreHomologyCompl
    [WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)] (j : ℕ) :
    (TopPair.ofSubset A).twistedHomologyπ L j ≫
        twistedHomologyToBorelMooreHomologyCompl hA L j =
      twistedHomologyToBorelMooreHomology L j ≫
        borelMooreHomologyOpenRestriction (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ))
          hA.isOpen_compl.isOpenEmbedding_subtypeVal L j :=
  (twistedHomologyπ_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L
    (CompactExhaustion.choice (Aᶜ : Set X)) j).trans
    (congrArg (_ ≫ ·)
      (borelMooreHomologyOpenRestrictionOfExhaustion_eq_borelMooreHomologyOpenRestriction
        (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) hA.isOpen_compl.isOpenEmbedding_subtypeVal L
        (CompactExhaustion.choice (Aᶜ : Set X)) j))

/-- On a compact Hausdorff space `X`, open restriction of Borel–Moore homology from `X` to `X \ A`
factors through `(twistedHomologyIsoBorelMooreHomology L j).inv`, the relative quotient map
`H_j(X; L) ⟶ H_j(X, A; L)`, and the compact-pair comparison map. -/
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
      (twistedHomologyIsoBorelMooreHomology_hom L)).trans
      (congrArg (_ ≫ ·)
        (twistedHomologyπ_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion
          hA L K j).symm)

/-- Exhaustion-free factorization of open restriction from a compact Hausdorff space `X` to `X \ A`
through relative twisted homology `H_j(X, A; L)`. -/
theorem borelMooreHomologyOpenRestriction_subtypeVal_compl_eq [CompactSpace X]
    [WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)] (j : ℕ) :
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

end T2

end ComparisonMap

section CofinalNeighborhoods

private lemma quasiIso_twistedChainComplexTotalToOuter_of_eq {X : TopCat.{v}}
    {L : LocalCoefficientSystem.{u, v, max v w} R X} {A B B' : Set X}
    (hAB : A ⊆ B) (hAB' : A ⊆ B') (hBB' : B = B')
    [QuasiIso ((TopTriple.ofSubset hAB').twistedChainComplexTotalToOuter L)] :
    QuasiIso ((TopTriple.ofSubset hAB).twistedChainComplexTotalToOuter L) := by
  subst hBB'; infer_instance

variable {X : TopCat.{v}} [CompactSpace X] [T2Space X] {A : Set X}

/-- When each triple quotient map `C(X, A; L) ⟶ C(X, U n; L)` is a quasi-isomorphism, the cone lift
`relativeToOpenRestrictionLim` for `CompactExhaustion.complOfCofinalNhds` is a quasi-isomorphism. -/
theorem quasiIso_relativeToOpenRestrictionLim_complOfCofinalNhds
    (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n)) (hAU : ∀ n, A ⊆ U n)
    (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W)
    (L : LocalCoefficientSystem.{u, v, max v w} R X)
    (hU_qi : ∀ n, QuasiIso ((TopTriple.ofSubset (hAU n)).twistedChainComplexTotalToOuter L)) :
    QuasiIso (relativeToOpenRestrictionLim A L
      (CompactExhaustion.complOfCofinalNhds hA hU_open hAU hU_cofinal)) := by
  let K := CompactExhaustion.complOfCofinalNhds hA hU_open hAU hU_cofinal
  refine ComplexTower.quasiIso_isLimitLimComplexCone_lift
    (openRestrictionTower_shift_surjective (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) L K)
    (relativeOpenRestrictionCone A L K) fun j ↦ ⟨0, fun n _ ↦ ?_⟩
  rw [relativeOpenRestrictionCone_π_app]
  have hKeq : (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ) '' K n)ᶜ =
      U (cofinalNhdsIndex hA hU_open hAU hU_cofinal n) :=
    (congrArg compl (Set.image_congr fun _ _ ↦ rfl)).trans
      (CompactExhaustion.compl_image_subtypeVal_complOfCofinalNhds hA hU_open hAU hU_cofinal n)
  have := hU_qi (cofinalNhdsIndex hA hU_open hAU hU_cofinal n)
  exact (quasiIso_iff _).1 (quasiIso_twistedChainComplexTotalToOuter_of_eq
    (Set.subset_compl_comm.2 (Subtype.coe_image_subset Aᶜ (K n)))
    (hAU (cofinalNhdsIndex hA hU_open hAU hU_cofinal n)) hKeq) j

/-- **Compact-pair comparison is an isomorphism** for every compact exhaustion of `Aᶜ` whenever `A`
admits a countable cofinal open neighbourhood family `U` with quasi-isomorphic triple quotient maps
`C(X, A; L) ⟶ C(X, U n; L)`. -/
theorem isIso_twistedHomologyToBorelMooreHomologyComplOfExhaustion_of_cofinal_nhds
    (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n)) (hAU : ∀ n, A ⊆ U n)
    (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W)
    (L : LocalCoefficientSystem.{u, v, max v w} R X)
    (hU_qi : ∀ n, QuasiIso ((TopTriple.ofSubset (hAU n)).twistedChainComplexTotalToOuter L))
    (K : CompactExhaustion (Aᶜ : Set X)) (j : ℕ) :
    IsIso (twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j) := by
  let K₀ := CompactExhaustion.complOfCofinalNhds hA hU_open hAU hU_cofinal
  rw [twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq hA L K K₀ j]
  have := quasiIso_relativeToOpenRestrictionLim_complOfCofinalNhds hA hU_open hAU hU_cofinal L hU_qi
  have := isIso_homologyMap_locallyFiniteChainComplexOpenRestrictionExcision
    (TopCat.ofHom (ContinuousMap.subtypeVal Aᶜ)) hA.isOpen_compl.isOpenEmbedding_subtypeVal L K₀ j
  unfold twistedHomologyToBorelMooreHomologyComplOfExhaustion; infer_instance

/-- **Compact-pair Borel–Moore comparison isomorphism** `H_j(X, A; L) ≅ H_j^{BM}(X \ A; L|_{X \ A})`
with respect to an explicit compact exhaustion `K` of `X \ A`. -/
def twistedHomologyIsoBorelMooreHomologyComplOfExhaustion
    (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n)) (hAU : ∀ n, A ⊆ U n)
    (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W)
    (L : LocalCoefficientSystem.{u, v, max v w} R X)
    (hU_qi : ∀ n, QuasiIso ((TopTriple.ofSubset (hAU n)).twistedChainComplexTotalToOuter L))
    (K : CompactExhaustion (Aᶜ : Set X)) (j : ℕ) :
    (TopPair.ofSubset A).twistedHomology L j ≅
      borelMooreHomology ((pullback (X := TopCat.of (Aᶜ : Set X))
        (ContinuousMap.subtypeVal Aᶜ)).obj L) j :=
  have := isIso_twistedHomologyToBorelMooreHomologyComplOfExhaustion_of_cofinal_nhds
    hA hU_open hAU hU_cofinal L hU_qi K j
  asIso (twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j)

@[simp]
theorem twistedHomologyIsoBorelMooreHomologyComplOfExhaustion_hom
    (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n)) (hAU : ∀ n, A ⊆ U n)
    (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W)
    (L : LocalCoefficientSystem.{u, v, max v w} R X)
    (hU_qi : ∀ n, QuasiIso ((TopTriple.ofSubset (hAU n)).twistedChainComplexTotalToOuter L))
    (K : CompactExhaustion (Aᶜ : Set X)) (j : ℕ) :
    (twistedHomologyIsoBorelMooreHomologyComplOfExhaustion
        hA hU_open hAU hU_cofinal L hU_qi K j).hom =
      twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j := (rfl)

/-- **Compact-pair Borel–Moore comparison isomorphism** `H_j(X, A; L) ≅ H_j^{BM}(X \ A; L|_{X \ A})`
for `[WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)]`. -/
def twistedHomologyIsoBorelMooreHomologyCompl
    [WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)]
    (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n)) (hAU : ∀ n, A ⊆ U n)
    (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W)
    (L : LocalCoefficientSystem.{u, v, max v w} R X)
    (hU_qi : ∀ n, QuasiIso ((TopTriple.ofSubset (hAU n)).twistedChainComplexTotalToOuter L))
    (j : ℕ) :
    (TopPair.ofSubset A).twistedHomology L j ≅
      borelMooreHomology ((pullback (X := TopCat.of (Aᶜ : Set X))
        (ContinuousMap.subtypeVal Aᶜ)).obj L) j :=
  have : IsIso (twistedHomologyToBorelMooreHomologyCompl hA L j) :=
    isIso_twistedHomologyToBorelMooreHomologyComplOfExhaustion_of_cofinal_nhds
      hA hU_open hAU hU_cofinal L hU_qi (CompactExhaustion.choice (Aᶜ : Set X)) j
  asIso (twistedHomologyToBorelMooreHomologyCompl hA L j)

@[simp]
theorem twistedHomologyIsoBorelMooreHomologyCompl_hom
    [WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)]
    (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n)) (hAU : ∀ n, A ⊆ U n)
    (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W)
    (L : LocalCoefficientSystem.{u, v, max v w} R X)
    (hU_qi : ∀ n, QuasiIso ((TopTriple.ofSubset (hAU n)).twistedChainComplexTotalToOuter L))
    (j : ℕ) :
    (twistedHomologyIsoBorelMooreHomologyCompl hA hU_open hAU hU_cofinal L hU_qi j).hom =
      twistedHomologyToBorelMooreHomologyCompl hA L j := (rfl)

/-- **Compact-pair Borel–Moore comparison isomorphism under deformation retractions** with respect
to an explicit compact exhaustion `K` of `X \ A`. -/
def twistedHomologyIsoBorelMooreHomologyComplOfExhaustionOfDeformationRetraction
    (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n)) (hAU : ∀ n, A ⊆ U n)
    (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W)
    (hU_ret : ∀ n, ∃ r : C(U n, A),
      (∀ a, r (ContinuousMap.inclusion (hAU n) a) = a) ∧
      ((ContinuousMap.inclusion (hAU n)).comp r).Homotopic (ContinuousMap.id (U n)))
    (L : LocalCoefficientSystem.{u, v, max v w} R X)
    (K : CompactExhaustion (Aᶜ : Set X)) (j : ℕ) :
    (TopPair.ofSubset A).twistedHomology L j ≅
      borelMooreHomology ((pullback (X := TopCat.of (Aᶜ : Set X))
        (ContinuousMap.subtypeVal Aᶜ)).obj L) j :=
  twistedHomologyIsoBorelMooreHomologyComplOfExhaustion hA hU_open hAU hU_cofinal L
    (fun n ↦ let ⟨r, hr, hH⟩ := hU_ret n
      TopTriple.quasiIso_twistedChainComplexTotalToOuter_ofSubset_of_deformationRetraction
        (hAU n) L r hr hH) K j

@[simp]
theorem twistedHomologyIsoBorelMooreHomologyComplOfExhaustionOfDeformationRetraction_hom
    (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n)) (hAU : ∀ n, A ⊆ U n)
    (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W)
    (hU_ret : ∀ n, ∃ r : C(U n, A),
      (∀ a, r (ContinuousMap.inclusion (hAU n) a) = a) ∧
      ((ContinuousMap.inclusion (hAU n)).comp r).Homotopic (ContinuousMap.id (U n)))
    (L : LocalCoefficientSystem.{u, v, max v w} R X)
    (K : CompactExhaustion (Aᶜ : Set X)) (j : ℕ) :
    (twistedHomologyIsoBorelMooreHomologyComplOfExhaustionOfDeformationRetraction
        hA hU_open hAU hU_cofinal hU_ret L K j).hom =
      twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j := (rfl)

/-- **Compact-pair Borel–Moore comparison isomorphism under deformation retractions**, without
explicit exhaustion parameter. -/
def twistedHomologyIsoBorelMooreHomologyComplOfDeformationRetraction
    [WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)]
    (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n)) (hAU : ∀ n, A ⊆ U n)
    (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W)
    (hU_ret : ∀ n, ∃ r : C(U n, A),
      (∀ a, r (ContinuousMap.inclusion (hAU n) a) = a) ∧
      ((ContinuousMap.inclusion (hAU n)).comp r).Homotopic (ContinuousMap.id (U n)))
    (L : LocalCoefficientSystem.{u, v, max v w} R X) (j : ℕ) :
    (TopPair.ofSubset A).twistedHomology L j ≅
      borelMooreHomology ((pullback (X := TopCat.of (Aᶜ : Set X))
        (ContinuousMap.subtypeVal Aᶜ)).obj L) j :=
  twistedHomologyIsoBorelMooreHomologyCompl hA hU_open hAU hU_cofinal L
    (fun n ↦ let ⟨r, hr, hH⟩ := hU_ret n
      TopTriple.quasiIso_twistedChainComplexTotalToOuter_ofSubset_of_deformationRetraction
        (hAU n) L r hr hH) j

@[simp]
theorem twistedHomologyIsoBorelMooreHomologyComplOfDeformationRetraction_hom
    [WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)]
    (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n)) (hAU : ∀ n, A ⊆ U n)
    (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W)
    (hU_ret : ∀ n, ∃ r : C(U n, A),
      (∀ a, r (ContinuousMap.inclusion (hAU n) a) = a) ∧
      ((ContinuousMap.inclusion (hAU n)).comp r).Homotopic (ContinuousMap.id (U n)))
    (L : LocalCoefficientSystem.{u, v, max v w} R X) (j : ℕ) :
    (twistedHomologyIsoBorelMooreHomologyComplOfDeformationRetraction
        hA hU_open hAU hU_cofinal hU_ret L j).hom =
      twistedHomologyToBorelMooreHomologyCompl hA L j := (rfl)

end CofinalNeighborhoods

end TauCeti.LocalCoefficientSystem
