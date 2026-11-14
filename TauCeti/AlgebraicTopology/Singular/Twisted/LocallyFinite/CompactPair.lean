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

For a closed subset `A` of a Hausdorff space `X`, the complement `X \ A` is open in `X`. Given a
compact exhaustion `K` of `X \ A` and a local coefficient system `L` on `X`, each subset `K n` is
compact, so its ambient image `i '' K n` is closed and `A ⊆ (i '' K n)ᶜ`. The triple quotient maps
`C(X, A; L) ⟶ C(X, (i '' K n)ᶜ; L)` assemble into a chain map
`relativeToOpenRestrictionLim : C(X, A; L) ⟶ (openRestrictionTower i L K).limComplex`. Composing its
induced map on homology with the inverse of the excision isomorphism from
`TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Restriction` yields a canonical comparison
morphism
`twistedHomologyToBorelMooreHomologyCompl : H_j(X, A; L) ⟶ H_j^{BM}(X \ A; L|_{X \ A})`,
independent of the compact exhaustion, natural in `L`, and compatible with open restriction along
`X \ A ↪ X`. When `X` is compact, open restriction `H_j^{BM}(X; L) ⟶ H_j^{BM}(X \ A; L|_{X \ A})`
factors through the relative quotient map `H_j(X; L) ⟶ H_j(X, A; L)` and this comparison map.

When `X` is compact Hausdorff and `A` admits a countable cofinal family of open neighbourhoods
`U : ℕ → Set X` for which the triple quotient maps `C(X, A; L) ⟶ C(X, U n; L)` are
quasi-isomorphisms — in particular, when each `U n` deformation retracts onto `A`, as for compact
Euclidean/polyhedral NDR pairs — `CompactExhaustion.complOfCofinalNhds` extracts a shrinking
subsequence `U (φ n)` with `closure (U (φ (n + 1))) ⊆ U (φ n)` whose complements `K n = (U (φ n))ᶜ`
form a compact exhaustion of `X \ A`. By Milnor's limit criterion
(`ComplexTower.quasiIso_isLimitLimComplexCone_lift`), `relativeToOpenRestrictionLim` is then a
quasi-isomorphism, so the comparison map is an isomorphism
`H_j(X, A; L) ≅ H_j^{BM}(X \ A; L|_{X \ A})` in every degree `j`.

## Main definitions and results

* `TauCeti.LocalCoefficientSystem.complInclusion`: the open inclusion `Aᶜ ⟶ X` in `TopCat`.
* `TauCeti.LocalCoefficientSystem.twistedHomologyToBorelMooreHomologyComplOfExhaustion` and
  `TauCeti.LocalCoefficientSystem.twistedHomologyToBorelMooreHomologyCompl`: the canonical
  comparison map `H_j(X, A; L) ⟶ H_j^{BM}(X \ A; L|_{X \ A})`, proved independent of the exhaustion,
  natural in `L`, and compatible with `borelMooreHomologyOpenRestriction`.
* `TauCeti.LocalCoefficientSystem.twistedHomologyIsoBorelMooreHomologyComplOfExhaustion` and
  `TauCeti.LocalCoefficientSystem.twistedHomologyIsoBorelMooreHomologyCompl`: the compact-pair
  isomorphism `H_j(X, A; L) ≅ H_j^{BM}(X \ A; L|_{X \ A})`, specialized to neighbourhood families
  that deformation retract onto `A` in
  `twistedHomologyIsoBorelMooreHomologyComplOfDeformationRetraction`.

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

/-! ### Comparison morphism from relative homology to Borel–Moore homology of the complement -/

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R]

section ComparisonMap

variable {X : TopCat.{v}}

/-- The inclusion `Aᶜ ↪ X` of the complement of `A ⊆ X` as a morphism in `TopCat`. -/
@[expose]
def complInclusion (A : Set X) : TopCat.of (Aᶜ : Set X) ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- When `A` is closed in `X`, `complInclusion A` is an open embedding. -/
theorem isOpenEmbedding_complInclusion {A : Set X} (hA : IsClosed A) :
    IsOpenEmbedding (complInclusion A).hom :=
  hA.isOpen_compl.isOpenEmbedding_subtypeVal

lemma subset_compl_image_complInclusion (A : Set X) (S : Set (TopCat.of (Aᶜ : Set X))) :
    A ⊆ (complInclusion A '' S)ᶜ := by
  rintro x hx ⟨y, -, rfl⟩
  exact y.2 hx

/-- The cone from `C(X, A; L)` to `openRestrictionTower (complInclusion A) L K` whose stage-`n` leg
is the triple quotient map `C(X, A; L) ⟶ C(X, (complInclusion A '' K n)ᶜ; L)`. -/
@[expose]
def relativeOpenRestrictionCone (A : Set X) (L : LocalCoefficientSystem.{u, v, max v w} R X)
    (K : CompactExhaustion (Aᶜ : Set X)) :
    Cone (openRestrictionTower (complInclusion A) L K) where
  pt := (TopPair.ofSubset A).twistedChainComplex L
  π := NatTrans.ofOpSequence
    (fun n ↦ (TopTriple.ofSubset
      (subset_compl_image_complInclusion A (K n))).twistedChainComplexTotalToOuter L)
    fun n ↦ by
      apply (TopPair.ofSubset A).twistedChainComplex_hom_ext L
      exact (congrArg (_ ≫ ·) (Category.id_comp _)).trans <|
        ((TopTriple.ofSubset
          (subset_compl_image_complInclusion A (K n))).twistedChainComplexπ_comp_totalToOuter
            L).trans
          (((TopTriple.ofSubset
            (subset_compl_image_complInclusion A
              (K (n + 1)))).twistedChainComplexπ_comp_totalToOuter_assoc L _).trans
            (twistedChainComplexπ_comp_openRestrictionTower_map (complInclusion A) L K
              (homOfLE (Nat.le_succ n)).op)).symm

/-- The canonical chain map from `C(X, A; L)` to the limit complex of
`openRestrictionTower (complInclusion A) L K`. -/
def relativeToOpenRestrictionLim (A : Set X) (L : LocalCoefficientSystem.{u, v, max v w} R X)
    (K : CompactExhaustion (Aᶜ : Set X)) :
    (TopPair.ofSubset A).twistedChainComplex L ⟶
      (openRestrictionTower (complInclusion A) L K).limComplex :=
  (openRestrictionTower (complInclusion A) L K).isLimitLimComplexCone.lift
    (relativeOpenRestrictionCone A L K)

@[reassoc (attr := simp)]
lemma relativeToOpenRestrictionLim_comp_π (A : Set X)
    (L : LocalCoefficientSystem.{u, v, max v w} R X) (K : CompactExhaustion (Aᶜ : Set X))
    (n : ℕ) :
    relativeToOpenRestrictionLim A L K ≫
        (openRestrictionTower (complInclusion A) L K).limComplexπ n =
      (TopTriple.ofSubset
        (subset_compl_image_complInclusion A (K n))).twistedChainComplexTotalToOuter L :=
  (openRestrictionTower (complInclusion A) L K).isLimitLimComplexCone.fac
    (relativeOpenRestrictionCone A L K) (op n)

/-- On absolute twisted chains on `X`, projecting to `C(X, A; L)` and mapping to the ambient
relative tower agrees with viewing finite chains as locally finite chains and restricting. -/
@[reassoc (attr := simp)]
theorem twistedChainComplexπ_comp_relativeToOpenRestrictionLim (A : Set X)
    (L : LocalCoefficientSystem.{u, v, max v w} R X) (K : CompactExhaustion (Aᶜ : Set X)) :
    (TopPair.ofSubset A).twistedChainComplexπ L ≫ relativeToOpenRestrictionLim A L K =
      toLocallyFiniteChainComplex L ≫
        locallyFiniteChainComplexToOpenRestrictionLim (complInclusion A) L K := by
  apply (openRestrictionTower (complInclusion A) L K).isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  let PiK := TopPair.ofSubset (complInclusion A '' K n)ᶜ
  exact (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (relativeToOpenRestrictionLim_comp_π A L K n)).trans <|
      ((TopTriple.ofSubset
        (subset_compl_image_complInclusion A (K n))).twistedChainComplexπ_comp_totalToOuter
          L).trans <|
        (PiK.toLocallyFiniteChainComplex_comp_locallyFiniteChainComplexToRelative
          L _).symm.trans <|
          (congrArg (_ ≫ ·)
            (locallyFiniteChainComplexToOpenRestrictionLim_comp_π
              (complInclusion A) L K n).symm).trans
            (Category.assoc _ _ _).symm

@[reassoc (attr := simp)]
lemma relativeToOpenRestrictionLim_comp_limComplexMap {A : Set X}
    (L : LocalCoefficientSystem.{u, v, max v w} R X) {K K' : CompactExhaustion (Aᶜ : Set X)}
    (h : ∀ n, K n ⊆ K' n) :
    relativeToOpenRestrictionLim A L K' ≫
        ComplexTower.limComplexMap (openRestrictionTowerMap (complInclusion A) L h) =
      relativeToOpenRestrictionLim A L K := by
  apply (openRestrictionTower (complInclusion A) L K).isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  refine (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (ComplexTower.limComplexMap_comp_π _ n)).trans <|
      (relativeToOpenRestrictionLim_comp_π_assoc A L K' n _).trans <|
        (?_ : _ = _).trans (relativeToOpenRestrictionLim_comp_π A L K n).symm
  apply (TopPair.ofSubset A).twistedChainComplex_hom_ext L
  exact ((TopTriple.ofSubset
    (subset_compl_image_complInclusion A (K' n))).twistedChainComplexπ_comp_totalToOuter_assoc
      L _).trans <|
    (twistedChainComplexπ_comp_openRestrictionTowerMap_app (complInclusion A) L h n).trans
      ((TopTriple.ofSubset
        (subset_compl_image_complInclusion A (K n))).twistedChainComplexπ_comp_totalToOuter L).symm

@[reassoc]
lemma twistedChainComplexCoefficientMap_comp_relativeToOpenRestrictionLim (A : Set X)
    {L L' : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ L')
    (K : CompactExhaustion (Aᶜ : Set X)) :
    (TopPair.ofSubset A).twistedChainComplexCoefficientMap η ≫
        relativeToOpenRestrictionLim A L' K =
      relativeToOpenRestrictionLim A L K ≫
        ComplexTower.limComplexMap (openRestrictionTowerCoefficientMap (complInclusion A) K η) := by
  apply (openRestrictionTower (complInclusion A) L' K).isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  apply (TopPair.ofSubset A).twistedChainComplex_hom_ext L
  have hL :
      (TopPair.ofSubset A).twistedChainComplexπ L ≫
          ((TopPair.ofSubset A).twistedChainComplexCoefficientMap η ≫
            relativeToOpenRestrictionLim A L' K) ≫
            (openRestrictionTower (complInclusion A) L' K).limComplexCone.π.app (op n) =
        twistedChainComplexCoefficientMap η ≫
          (TopPair.ofSubset (complInclusion A '' K n)ᶜ).twistedChainComplexπ L' :=
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ _)
        ((TopPair.ofSubset A).twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc
          η _)).trans <|
        (Category.assoc _ _ _).trans <|
          (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans <|
            (congrArg (_ ≫ ·)
              (congrArg (_ ≫ ·) (relativeToOpenRestrictionLim_comp_π A L' K n))).trans
              (congrArg (_ ≫ ·)
                ((TopTriple.ofSubset
                  (subset_compl_image_complInclusion A
                    (K n))).twistedChainComplexπ_comp_totalToOuter L'))
  have hR :
      (TopPair.ofSubset A).twistedChainComplexπ L ≫
          (relativeToOpenRestrictionLim A L K ≫
            ComplexTower.limComplexMap
              (openRestrictionTowerCoefficientMap (complInclusion A) K η)) ≫
            (openRestrictionTower (complInclusion A) L' K).limComplexCone.π.app (op n) =
        twistedChainComplexCoefficientMap η ≫
          (TopPair.ofSubset (complInclusion A '' K n)ᶜ).twistedChainComplexπ L' :=
    (congrArg (_ ≫ ·) <|
      (Category.assoc _ _ _).trans <|
        (congrArg (_ ≫ ·)
          (ComplexTower.limComplexMap_comp_π
            (openRestrictionTowerCoefficientMap (complInclusion A) K η) n)).trans
          (relativeToOpenRestrictionLim_comp_π_assoc A L K n _)).trans <|
      ((TopTriple.ofSubset
        (subset_compl_image_complInclusion A (K n))).twistedChainComplexπ_comp_totalToOuter_assoc
          L _).trans <|
        (congrArg (_ ≫ ·)
          (openRestrictionTowerCoefficientMap_app (complInclusion A) K η n)).trans
          ((TopPair.ofSubset
            (complInclusion A '' K n)ᶜ).twistedChainComplexπ_comp_twistedChainComplexCoefficientMap
              η)
  exact hL.trans hR.symm

section T2

variable [T2Space X] {A : Set X} (hA : IsClosed A)
  (L : LocalCoefficientSystem.{u, v, max v w} R X) (K : CompactExhaustion (Aᶜ : Set X))

/-- **Comparison morphism from relative twisted homology to Borel–Moore homology of the
complement**, defined with respect to an explicit compact exhaustion `K` of `Aᶜ` (and independent of
`K` by `twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq`). -/
def twistedHomologyToBorelMooreHomologyComplOfExhaustion (j : ℕ) :
    (TopPair.ofSubset A).twistedHomology L j ⟶
      borelMooreHomology ((pullback (complInclusion A).hom).obj L) j :=
  have := isIso_homologyMap_locallyFiniteToOpenRestrictionLim (complInclusion A)
    (isOpenEmbedding_complInclusion hA) L K j
  HomologicalComplex.homologyMap (relativeToOpenRestrictionLim A L K) j ≫
    inv (HomologicalComplex.homologyMap
      ((locallyFiniteChainComplexIsoLimComplex ((pullback (complInclusion A).hom).obj L) K).hom ≫
        ComplexTower.limComplexMap (openRestrictionExcisionTowerMap (complInclusion A)
          (isOpenEmbedding_complInclusion hA).injective L K)) j)

@[reassoc (attr := simp)]
theorem twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap (j : ℕ) :
    twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j ≫
        HomologicalComplex.homologyMap
          ((locallyFiniteChainComplexIsoLimComplex
              ((pullback (complInclusion A).hom).obj L) K).hom ≫
            ComplexTower.limComplexMap (openRestrictionExcisionTowerMap (complInclusion A)
              (isOpenEmbedding_complInclusion hA).injective L K)) j =
      HomologicalComplex.homologyMap (relativeToOpenRestrictionLim A L K) j := by
  have := isIso_homologyMap_locallyFiniteToOpenRestrictionLim (complInclusion A)
    (isOpenEmbedding_complInclusion hA) L K j
  simp [twistedHomologyToBorelMooreHomologyComplOfExhaustion]

private lemma twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq_of_subset
    {K' : CompactExhaustion (Aᶜ : Set X)} (h : ∀ n, K n ⊆ K' n) (j : ℕ) :
    twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K' j =
      twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j := by
  have := isIso_homologyMap_locallyFiniteToOpenRestrictionLim (complInclusion A)
    (isOpenEmbedding_complInclusion hA) L K j
  apply (cancel_mono (HomologicalComplex.homologyMap
    ((locallyFiniteChainComplexIsoLimComplex ((pullback (complInclusion A).hom).obj L) K).hom ≫
      ComplexTower.limComplexMap (openRestrictionExcisionTowerMap (complInclusion A)
        (isOpenEmbedding_complInclusion hA).injective L K)) j)).1
  rw [twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap,
    ← locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexMap
      ((pullback (complInclusion A).hom).obj L) h,
    Category.assoc, ← ComplexTower.limComplexMap_comp,
    relativeChainComplexTowerMap_comp_openRestrictionExcisionTowerMap,
    ComplexTower.limComplexMap_comp, ← Category.assoc, HomologicalComplex.homologyMap_comp,
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
        borelMooreHomologyCoefficientMap ((pullback (complInclusion A).hom).map η) j := by
  let eMap (L₀ : LocalCoefficientSystem.{u, v, max v w} R X) :=
    (locallyFiniteChainComplexIsoLimComplex ((pullback (complInclusion A).hom).obj L₀) K).hom ≫
      ComplexTower.limComplexMap (openRestrictionExcisionTowerMap (complInclusion A)
        (isOpenEmbedding_complInclusion hA).injective L₀ K)
  have hchain :
      locallyFiniteChainComplexCoefficientMap ((pullback (complInclusion A).hom).map η) ≫
          eMap L' =
        eMap L ≫
          ComplexTower.limComplexMap
            (openRestrictionTowerCoefficientMap (complInclusion A) K η) := by
    dsimp [eMap]
    rw [← Category.assoc, locallyFiniteChainComplexCoefficientMap_comp_isoLimComplex_hom,
      Category.assoc, ← ComplexTower.limComplexMap_comp,
      ← openRestrictionExcisionTowerMap_naturality,
      ComplexTower.limComplexMap_comp, Category.assoc]
  have := isIso_homologyMap_locallyFiniteToOpenRestrictionLim (complInclusion A)
    (isOpenEmbedding_complInclusion hA) L' K j
  apply (cancel_mono (HomologicalComplex.homologyMap (eMap L') j)).1
  exact (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·)
      (twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap hA L' K j)).trans <|
      (HomologicalComplex.homologyMap_comp _ _ j).symm.trans <|
        (congrArg (HomologicalComplex.homologyMap · j)
          (twistedChainComplexCoefficientMap_comp_relativeToOpenRestrictionLim A η K)).trans <|
          (HomologicalComplex.homologyMap_comp _ _ j).trans <|
            (congrArg (· ≫ _)
              (twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap
                hA L K j).symm).trans <|
              (Category.assoc _ _ _).trans <|
                (congrArg (_ ≫ ·) (HomologicalComplex.homologyMap_comp _ _ j).symm).trans <|
                  (congrArg (fun φ ↦ _ ≫ HomologicalComplex.homologyMap φ j) hchain.symm).trans <|
                    (congrArg (_ ≫ ·) (HomologicalComplex.homologyMap_comp _ _ j)).trans
                      (Category.assoc _ _ _).symm

/-- **Compatibility with open restriction:** on absolute twisted homology of `X`, passing to
relative homology `H_j(X, A; L)` and applying the comparison map agrees with viewing finite chains
as Borel–Moore classes on `X` and restricting to `X \ A`. -/
@[reassoc (attr := simp)]
theorem twistedHomologyπ_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion (j : ℕ) :
    (TopPair.ofSubset A).twistedHomologyπ L j ≫
        twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j =
      twistedHomologyToBorelMooreHomology L j ≫
        borelMooreHomologyOpenRestrictionOfExhaustion (complInclusion A)
          (isOpenEmbedding_complInclusion hA) L K j := by
  refine eq_borelMooreHomologyOpenRestrictionOfExhaustion (complInclusion A)
    (isOpenEmbedding_complInclusion hA) L K ?_
  exact (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·)
      (twistedHomologyToBorelMooreHomologyComplOfExhaustion_comp_homologyMap hA L K j)).trans <|
      (HomologicalComplex.homologyMap_comp _ _ j).symm.trans <|
        (congrArg (HomologicalComplex.homologyMap · j)
          (twistedChainComplexπ_comp_relativeToOpenRestrictionLim A L K)).trans
          (HomologicalComplex.homologyMap_comp _ _ j)

/-- **Comparison morphism from relative twisted homology to Borel–Moore homology of the
complement** when `X \ A` is weakly locally compact and `σ`-compact. -/
def twistedHomologyToBorelMooreHomologyCompl
    [WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)] (j : ℕ) :
    (TopPair.ofSubset A).twistedHomology L j ⟶
      borelMooreHomology ((pullback (complInclusion A).hom).obj L) j :=
  twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L
    (CompactExhaustion.choice (Aᶜ : Set X)) j

@[simp]
theorem twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq_compl
    [WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)] (j : ℕ) :
    twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j =
      twistedHomologyToBorelMooreHomologyCompl hA L j :=
  twistedHomologyToBorelMooreHomologyComplOfExhaustion_eq hA L K
    (CompactExhaustion.choice (Aᶜ : Set X)) j

@[reassoc]
theorem twistedHomologyToBorelMooreHomologyCompl_naturality
    [WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)]
    {L' : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ L') (j : ℕ) :
    (TopPair.ofSubset A).twistedHomologyCoefficientMap η j ≫
        twistedHomologyToBorelMooreHomologyCompl hA L' j =
      twistedHomologyToBorelMooreHomologyCompl hA L j ≫
        borelMooreHomologyCoefficientMap ((pullback (complInclusion A).hom).map η) j :=
  twistedHomologyToBorelMooreHomologyComplOfExhaustion_naturality hA L
    (CompactExhaustion.choice (Aᶜ : Set X)) η j

@[reassoc (attr := simp)]
theorem twistedHomologyπ_comp_twistedHomologyToBorelMooreHomologyCompl
    [WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)] (j : ℕ) :
    (TopPair.ofSubset A).twistedHomologyπ L j ≫
        twistedHomologyToBorelMooreHomologyCompl hA L j =
      twistedHomologyToBorelMooreHomology L j ≫
        borelMooreHomologyOpenRestriction (complInclusion A)
          (isOpenEmbedding_complInclusion hA) L j :=
  (twistedHomologyπ_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L
    (CompactExhaustion.choice (Aᶜ : Set X)) j).trans
    (congrArg (_ ≫ ·)
      (borelMooreHomologyOpenRestrictionOfExhaustion_eq_borelMooreHomologyOpenRestriction
        (complInclusion A) (isOpenEmbedding_complInclusion hA) L
        (CompactExhaustion.choice (Aᶜ : Set X)) j))

/-- On a compact Hausdorff space `X`, open restriction of Borel–Moore homology from `X` to `X \ A`
factors through `(twistedHomologyIsoBorelMooreHomology L j).inv`, the relative quotient map
`H_j(X; L) ⟶ H_j(X, A; L)`, and the compact-pair comparison map. -/
theorem borelMooreHomologyOpenRestrictionOfExhaustion_complInclusion_eq [CompactSpace X] (j : ℕ) :
    borelMooreHomologyOpenRestrictionOfExhaustion (complInclusion A)
        (isOpenEmbedding_complInclusion hA) L K j =
      (twistedHomologyIsoBorelMooreHomology L j).inv ≫
        (TopPair.ofSubset A).twistedHomologyπ L j ≫
          twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j :=
  (Iso.inv_hom_id_assoc (twistedHomologyIsoBorelMooreHomology L j) _).symm.trans <|
    (congrArg (fun g ↦ (twistedHomologyIsoBorelMooreHomology L j).inv ≫ g ≫ _)
      (twistedHomologyIsoBorelMooreHomology_hom L)).trans
      (congrArg (_ ≫ ·)
        (twistedHomologyπ_comp_twistedHomologyToBorelMooreHomologyComplOfExhaustion
          hA L K j).symm)

theorem borelMooreHomologyOpenRestriction_complInclusion_eq [CompactSpace X]
    [WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)] (j : ℕ) :
    borelMooreHomologyOpenRestriction (complInclusion A)
        (isOpenEmbedding_complInclusion hA) L j =
      (twistedHomologyIsoBorelMooreHomology L j).inv ≫
        (TopPair.ofSubset A).twistedHomologyπ L j ≫
          twistedHomologyToBorelMooreHomologyCompl hA L j :=
  (borelMooreHomologyOpenRestrictionOfExhaustion_eq_borelMooreHomologyOpenRestriction
    (complInclusion A) (isOpenEmbedding_complInclusion hA) L
    (CompactExhaustion.choice (Aᶜ : Set X)) j).symm.trans
    (borelMooreHomologyOpenRestrictionOfExhaustion_complInclusion_eq hA L
      (CompactExhaustion.choice (Aᶜ : Set X)) j)

end T2

end ComparisonMap

/-! ### Compact-pair isomorphism from cofinal open neighbourhoods -/

section CofinalNeighborhoods

private lemma quasiIso_twistedChainComplexTotalToOuter_of_eq {X : TopCat.{v}}
    {L : LocalCoefficientSystem.{u, v, max v w} R X} {A B B' : Set X}
    (hAB : A ⊆ B) (hAB' : A ⊆ B') (hBB' : B = B')
    [QuasiIso ((TopTriple.ofSubset hAB').twistedChainComplexTotalToOuter L)] :
    QuasiIso ((TopTriple.ofSubset hAB).twistedChainComplexTotalToOuter L) := by
  subst hBB'
  infer_instance

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
    (openRestrictionTower_shift_surjective (complInclusion A) L K)
    (relativeOpenRestrictionCone A L K) fun j ↦ ⟨0, fun n _ ↦ ?_⟩
  have := hU_qi (CompactExhaustion.cofinalNhdsIndex hA hU_open hAU hU_cofinal n)
  have hq : QuasiIso ((TopTriple.ofSubset
      (subset_compl_image_complInclusion A (K n))).twistedChainComplexTotalToOuter L) :=
    quasiIso_twistedChainComplexTotalToOuter_of_eq
      (subset_compl_image_complInclusion A (K n))
      (hAU (CompactExhaustion.cofinalNhdsIndex hA hU_open hAU hU_cofinal n))
      (CompactExhaustion.compl_image_subtypeVal_complOfCofinalNhds
        hA hU_open hAU hU_cofinal n)
  exact (quasiIso_iff _).1 hq j

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
  have := quasiIso_relativeToOpenRestrictionLim_complOfCofinalNhds
    hA hU_open hAU hU_cofinal L hU_qi
  have := isIso_homologyMap_locallyFiniteToOpenRestrictionLim (complInclusion A)
    (isOpenEmbedding_complInclusion hA) L K₀ j
  unfold twistedHomologyToBorelMooreHomologyComplOfExhaustion
  infer_instance

/-- **Compact-pair Borel–Moore comparison isomorphism** `H_j(X, A; L) ≅ H_j^{BM}(X \ A; L|_{X \ A})`
with respect to an explicit compact exhaustion `K` of `X \ A`. -/
def twistedHomologyIsoBorelMooreHomologyComplOfExhaustion
    (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n)) (hAU : ∀ n, A ⊆ U n)
    (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W)
    (L : LocalCoefficientSystem.{u, v, max v w} R X)
    (hU_qi : ∀ n, QuasiIso ((TopTriple.ofSubset (hAU n)).twistedChainComplexTotalToOuter L))
    (K : CompactExhaustion (Aᶜ : Set X)) (j : ℕ) :
    (TopPair.ofSubset A).twistedHomology L j ≅
      borelMooreHomology ((pullback (complInclusion A).hom).obj L) j :=
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
      twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j :=
  (rfl)

/-- **Compact-pair Borel–Moore comparison isomorphism** `H_j(X, A; L) ≅ H_j^{BM}(X \ A; L|_{X \ A})`
for `[WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)]` (both of which are
supplied automatically by `(CompactExhaustion.complOfCofinalNhds ...).weaklyLocallyCompactSpace`
and `.sigmaCompactSpace`). -/
def twistedHomologyIsoBorelMooreHomologyCompl
    [WeaklyLocallyCompactSpace (Aᶜ : Set X)] [SigmaCompactSpace (Aᶜ : Set X)]
    (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n)) (hAU : ∀ n, A ⊆ U n)
    (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W)
    (L : LocalCoefficientSystem.{u, v, max v w} R X)
    (hU_qi : ∀ n, QuasiIso ((TopTriple.ofSubset (hAU n)).twistedChainComplexTotalToOuter L))
    (j : ℕ) :
    (TopPair.ofSubset A).twistedHomology L j ≅
      borelMooreHomology ((pullback (complInclusion A).hom).obj L) j :=
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
      twistedHomologyToBorelMooreHomologyCompl hA L j :=
  (rfl)

/-- **Compact-pair Borel–Moore comparison isomorphism under deformation retractions:** if `A` is a
closed subset of a compact Hausdorff space `X` admitting a countable cofinal family `U` of open
neighbourhoods each of which deformation retracts onto `A`, then
`H_j(X, A; L) ≅ H_j^{BM}(X \ A; L|_{X \ A})` for every local coefficient system `L` on `X`. -/
def twistedHomologyIsoBorelMooreHomologyComplOfExhaustionOfDeformationRetraction
    (hA : IsClosed A) {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n)) (hAU : ∀ n, A ⊆ U n)
    (hU_cofinal : ∀ {W : Set X}, IsOpen W → A ⊆ W → ∃ n, U n ⊆ W)
    (hU_ret : ∀ n, ∃ r : C(U n, A),
      (∀ a, r (ContinuousMap.inclusion (hAU n) a) = a) ∧
      ((ContinuousMap.inclusion (hAU n)).comp r).Homotopic (ContinuousMap.id (U n)))
    (L : LocalCoefficientSystem.{u, v, max v w} R X)
    (K : CompactExhaustion (Aᶜ : Set X)) (j : ℕ) :
    (TopPair.ofSubset A).twistedHomology L j ≅
      borelMooreHomology ((pullback (complInclusion A).hom).obj L) j :=
  twistedHomologyIsoBorelMooreHomologyComplOfExhaustion hA hU_open hAU hU_cofinal L
    (fun n ↦
      let ⟨r, hr, hH⟩ := hU_ret n
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
      twistedHomologyToBorelMooreHomologyComplOfExhaustion hA L K j :=
  (rfl)

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
      borelMooreHomology ((pullback (complInclusion A).hom).obj L) j :=
  twistedHomologyIsoBorelMooreHomologyCompl hA hU_open hAU hU_cofinal L
    (fun n ↦
      let ⟨r, hr, hH⟩ := hU_ret n
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
      twistedHomologyToBorelMooreHomologyCompl hA L j :=
  (rfl)

end CofinalNeighborhoods

end TauCeti.LocalCoefficientSystem
