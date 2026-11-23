/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.TowerExcision
import TauCeti.Topology.Compactness.SigmaCompact

/-!
# Open restriction in Borel–Moore homology

Borel–Moore homology is contravariant for open embeddings `j : V ⟶ X`. Unlike finite singular
chains, locally finite chains cannot be restricted directly to an open subset at the chain level,
because simplices in `X` may cross the boundary of `V`. Instead, given a compact exhaustion `K` of
`V` whose images in `X` have closure inside `Set.range j` (automatic when `X` is Hausdorff), the
restriction on homology is defined by the excision zigzag

`C^lf(X; L) ⟶ limₙ C(X, X \ j '' Kₙ; L) ⟵ limₙ C(V, V \ Kₙ; j⁎L) ≅ C^lf(V; j⁎L)`.

The left chain map sends a locally finite chain on `X` to the compatible family of its relative
classes modulo `X \ j '' Kₙ`
(`TauCeti.LocalCoefficientSystem.locallyFiniteChainComplexToLimComplex` applied to the monotone
sequence `fun n ↦ j.hom '' K n`). The right chain map
(`TauCeti.LocalCoefficientSystem.locallyFiniteChainComplexToLimComplexOfInjective`) composes the
limit identification on `V` with the inverse-limit map induced by the levelwise excision maps of
pairs `(V, V \ Kₙ) ⟶ (X, X \ j '' Kₙ)`
(`TauCeti.LocalCoefficientSystem.excisionRelativeChainComplexTowerMap`).
Because `Set.range j` is open and contains the closure of `j '' Kₙ`,
`TauCeti.LocalCoefficientSystem.quasiIso_limComplexMap_excisionRelativeChainComplexTowerMap`
upgrades this to a quasi-isomorphism of limit complexes. Inverting the resulting isomorphism on
homology yields `TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrictOfExhaustion`, whose
composition with projection to any relative stage is given by
`borelMooreHomologyRestrictOfExhaustion_comp_locallyFiniteChainComplexToRelative`.

Any two compact exhaustions `K` and `K'` of `V` are dominated by their pointwise union
`K.union K'`, and enlarging the compact sets induces compatible triple-quotient maps on both
towers (`TauCeti.LocalCoefficientSystem.relativeChainComplexTowerMap`), so the restriction
morphism is independent of the chosen exhaustion
(`TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrictOfExhaustion_eq`). When `X` is Hausdorff
and `V` is weakly locally compact and sigma-compact, choosing `CompactExhaustion.choice V` defines
the canonical open restriction `TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrict`.

Functoriality and naturality in local coefficients are in
`TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Restriction.Functoriality`, the
degree-zero discrete computation is in
`TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Restriction.Discrete`, and proper-map
base change is in
`TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Restriction.BaseChange`.

## Main declarations

* `TauCeti.LocalCoefficientSystem.locallyFiniteChainComplexToLimComplexOfInjective` and
  `TauCeti.LocalCoefficientSystem.quasiIso_locallyFiniteChainComplexToLimComplexOfInjective`: the
  chain map from locally finite chains on `V` to the limit of the ambient relative tower on `X`
  and its quasi-isomorphism property for open embeddings.
* `TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrictOfExhaustion` and
  `TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrictOfExhaustion_eq`: open restriction via
  an explicit compact exhaustion and its exhaustion independence.
* `borelMooreHomologyRestrictOfExhaustion_comp_locallyFiniteChainComplexToRelative`:
  stagewise equation relating open restriction to projection into relative chains.
* `TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrict`: canonical open restriction for an
  open embedding into a Hausdorff space from a weakly locally compact sigma-compact space.

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

variable {R : Type u} [Ring R]

section ExcisionTower

variable {V X : TopCat.{v}} {j : V ⟶ X}
  (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- The chain map `C^lf(V; j⁎L) ⟶ limₙ C(X, X \ j '' Kₙ; L)` formed by composing the limit
identification of locally finite chains on `V` with the excision map of relative towers along an
injective map `j : V ⟶ X`. -/
def locallyFiniteChainComplexToLimComplexOfInjective (K : CompactExhaustion V)
    (hj : Function.Injective j.hom) :
    locallyFiniteChainComplex ((pullback j.hom).obj L) ⟶
      (relativeChainComplexTower L (fun n ↦ j.hom '' K n)
        (fun n ↦ Set.image_mono (K.subset_succ n))).limComplex :=
  (locallyFiniteChainComplexIsoLimComplex ((pullback j.hom).obj L) K).hom ≫
    ComplexTower.limComplexMap (excisionRelativeChainComplexTowerMap L K K.subset_succ hj)

/-- Unfolding `locallyFiniteChainComplexToLimComplexOfInjective` as the limit identification on `V`
followed by the excision tower map. -/
lemma locallyFiniteChainComplexToLimComplexOfInjective_eq (K : CompactExhaustion V)
    (hj : Function.Injective j.hom) :
    locallyFiniteChainComplexToLimComplexOfInjective L K hj =
      locallyFiniteChainComplexToLimComplex ((pullback j.hom).obj L) K K.subset_succ
          K.isCompact ≫
        ComplexTower.limComplexMap (excisionRelativeChainComplexTowerMap L K K.subset_succ hj) := by
  rw [locallyFiniteChainComplexToLimComplexOfInjective,
    locallyFiniteChainComplexIsoLimComplex_hom_eq]

/-- The `n`-th projection of `locallyFiniteChainComplexToLimComplexOfInjective` takes relative
classes on `V` and pushes them along the excision map of pairs. -/
@[reassoc (attr := simp)]
lemma locallyFiniteChainComplexToLimComplexOfInjective_comp_limComplexπ (K : CompactExhaustion V)
    (hj : Function.Injective j.hom) (n : ℕ) :
    locallyFiniteChainComplexToLimComplexOfInjective L K hj ≫
        (relativeChainComplexTower L (fun n ↦ j.hom '' K n)
          (fun n ↦ Set.image_mono (K.subset_succ n))).limComplexπ n =
      (TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative ((pullback j.hom).obj L)
          (K.isCompact n).compl_range_ofSubset_compl_map ≫
        TopPair.twistedChainComplexMapOfFstEq (TopPair.ofSubsetMap j
          (Set.SurjOn.mapsTo_compl (Set.surjOn_image j.hom (K n)) hj))
          (TopPair.ofSubsetMap_fst _ _) L := by
  rw [locallyFiniteChainComplexToLimComplexOfInjective, Category.assoc,
    ComplexTower.limComplexMap_comp_π,
    locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexπ_assoc,
    excisionRelativeChainComplexTowerMap_app]
  rfl

/-- For an open embedding `j : V ⟶ X` and a compact exhaustion `K` with
`closure (j '' Kₙ) ⊆ Set.range j`, `locallyFiniteChainComplexToLimComplexOfInjective` is a
quasi-isomorphism. -/
theorem quasiIso_locallyFiniteChainComplexToLimComplexOfInjective (K : CompactExhaustion V)
    (hj : IsOpenEmbedding j.hom) (hK : ∀ n, closure (j.hom '' K n) ⊆ Set.range j.hom) :
    QuasiIso (locallyFiniteChainComplexToLimComplexOfInjective L K hj.injective) := by
  have := quasiIso_limComplexMap_excisionRelativeChainComplexTowerMap L K K.subset_succ hj hK
  exact quasiIso_comp _ _

end ExcisionTower

section ExhaustionRestriction

variable {V X : TopCat.{v}} {j : V ⟶ X}
  (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- **Open restriction in Borel–Moore homology via a compact exhaustion.** Given an open embedding
`j : V ⟶ X` and a compact exhaustion `K` of `V` with `closure (j '' Kₙ) ⊆ Set.range j`, this
morphism `Hₖ^BM(X; L) ⟶ Hₖ^BM(V; j⁎L)` is obtained by inverting the excision quasi-isomorphism
`locallyFiniteChainComplexToLimComplexOfInjective`. By
`borelMooreHomologyRestrictOfExhaustion_eq`, it does not depend on the choice of `K`. -/
def borelMooreHomologyRestrictOfExhaustion (hj : IsOpenEmbedding j.hom)
    (K : CompactExhaustion V) (hK : ∀ n, closure (j.hom '' K n) ⊆ Set.range j.hom) (k : ℕ) :
    borelMooreHomology L k ⟶ borelMooreHomology ((pullback j.hom).obj L) k :=
  have := quasiIso_locallyFiniteChainComplexToLimComplexOfInjective L K hj hK
  HomologicalComplex.homologyMap
      (locallyFiniteChainComplexToLimComplex L (fun n ↦ j.hom '' K n)
        (fun n ↦ Set.image_mono (K.subset_succ n))
        (fun n ↦ (K.isCompact n).image j.hom.continuous)) k ≫
    inv (HomologicalComplex.homologyMap
      (locallyFiniteChainComplexToLimComplexOfInjective L K hj.injective) k)

/-- The defining zigzag equation for `borelMooreHomologyRestrictOfExhaustion`. -/
@[reassoc (attr := simp)]
theorem borelMooreHomologyRestrictOfExhaustion_comp_locallyFiniteChainComplexToLimComplexOfInjective
    (hj : IsOpenEmbedding j.hom) (K : CompactExhaustion V)
    (hK : ∀ n, closure (j.hom '' K n) ⊆ Set.range j.hom) (k : ℕ) :
    borelMooreHomologyRestrictOfExhaustion L hj K hK k ≫
        HomologicalComplex.homologyMap
          (locallyFiniteChainComplexToLimComplexOfInjective L K hj.injective) k =
      HomologicalComplex.homologyMap
        (locallyFiniteChainComplexToLimComplex L (fun n ↦ j.hom '' K n)
          (fun n ↦ Set.image_mono (K.subset_succ n))
          (fun n ↦ (K.isCompact n).image j.hom.continuous)) k := by
  have := quasiIso_locallyFiniteChainComplexToLimComplexOfInjective L K hj hK
  simp [borelMooreHomologyRestrictOfExhaustion]

/-- Uniqueness characterization of `borelMooreHomologyRestrictOfExhaustion`: a morphism
`Hₖ^BM(X; L) ⟶ Hₖ^BM(V; j⁎L)` equals open restriction if and only if postcomposing with
`locallyFiniteChainComplexToLimComplexOfInjective` yields
`locallyFiniteChainComplexToLimComplex`. -/
theorem eq_borelMooreHomologyRestrictOfExhaustion_iff (hj : IsOpenEmbedding j.hom)
    (K : CompactExhaustion V) (hK : ∀ n, closure (j.hom '' K n) ⊆ Set.range j.hom) (k : ℕ)
    (φ : borelMooreHomology L k ⟶ borelMooreHomology ((pullback j.hom).obj L) k) :
    φ = borelMooreHomologyRestrictOfExhaustion L hj K hK k ↔
      φ ≫ HomologicalComplex.homologyMap
          (locallyFiniteChainComplexToLimComplexOfInjective L K hj.injective) k =
        HomologicalComplex.homologyMap
          (locallyFiniteChainComplexToLimComplex L (fun n ↦ j.hom '' K n)
            (fun n ↦ Set.image_mono (K.subset_succ n))
            (fun n ↦ (K.isCompact n).image j.hom.continuous)) k := by
  have := quasiIso_locallyFiniteChainComplexToLimComplexOfInjective L K hj hK
  constructor
  · rintro rfl
    exact
      borelMooreHomologyRestrictOfExhaustion_comp_locallyFiniteChainComplexToLimComplexOfInjective
        L hj K hK k
  · intro h
    rw [← cancel_mono (HomologicalComplex.homologyMap
        (locallyFiniteChainComplexToLimComplexOfInjective L K hj.injective) k),
      h,
      borelMooreHomologyRestrictOfExhaustion_comp_locallyFiniteChainComplexToLimComplexOfInjective]

/-- Restricting via a compact exhaustion and mapping into the `n`-th relative stage of `V` agrees
with mapping directly into the `n`-th relative stage of `X` modulo `X \ j '' K n`. -/
@[reassoc]
theorem borelMooreHomologyRestrictOfExhaustion_comp_locallyFiniteChainComplexToRelative
    (hj : IsOpenEmbedding j.hom) (K : CompactExhaustion V)
    (hK : ∀ n, closure (j.hom '' K n) ⊆ Set.range j.hom) (k n : ℕ) :
    borelMooreHomologyRestrictOfExhaustion L hj K hK k ≫
        HomologicalComplex.homologyMap
          ((TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative ((pullback j.hom).obj L)
              (K.isCompact n).compl_range_ofSubset_compl_map ≫
            TopPair.twistedChainComplexMapOfFstEq (TopPair.ofSubsetMap j
              (Set.SurjOn.mapsTo_compl (Set.surjOn_image j.hom (K n)) hj.injective))
              (TopPair.ofSubsetMap_fst _ _) L) k =
      HomologicalComplex.homologyMap
        ((TopPair.ofSubset (j.hom '' K n)ᶜ).locallyFiniteChainComplexToRelative L
          ((K.isCompact n).image j.hom.continuous).compl_range_ofSubset_compl_map) k := by
  -- Align `(relativeChainComplexTower …).obj (op n)` with
  -- `(TopPair.ofSubset _).twistedChainComplex` across `limComplexπ n`.
  have hπ : HomologicalComplex.homologyMap
        ((TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative ((pullback j.hom).obj L)
            (K.isCompact n).compl_range_ofSubset_compl_map ≫
          TopPair.twistedChainComplexMapOfFstEq (TopPair.ofSubsetMap j
            (Set.SurjOn.mapsTo_compl (Set.surjOn_image j.hom (K n)) hj.injective))
            (TopPair.ofSubsetMap_fst _ _) L) k =
      HomologicalComplex.homologyMap
        (locallyFiniteChainComplexToLimComplexOfInjective L K hj.injective) k ≫
      HomologicalComplex.homologyMap
        ((relativeChainComplexTower L (fun m ↦ j.hom '' K m)
          (fun m ↦ Set.image_mono (K.subset_succ m))).limComplexπ n) k := by
    rw [← HomologicalComplex.homologyMap_comp,
      locallyFiniteChainComplexToLimComplexOfInjective_comp_limComplexπ]
    rfl
  exact (congrArg (_ ≫ ·) hπ).trans <| (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _)
      (borelMooreHomologyRestrictOfExhaustion_comp_locallyFiniteChainComplexToLimComplexOfInjective
        L hj K hK k)).trans <|
      (HomologicalComplex.homologyMap_comp _ _ k).symm.trans <|
        congrArg (fun φ ↦ HomologicalComplex.homologyMap φ k)
          (locallyFiniteChainComplexToLimComplex_comp_limComplexπ L (fun m ↦ j.hom '' K m)
            (fun m ↦ Set.image_mono (K.subset_succ m))
            (fun m ↦ (K.isCompact m).image j.hom.continuous) n)

/-- `locallyFiniteChainComplexToLimComplexOfInjective` is compatible with enlargement of the
compact exhaustion of `V`. -/
@[reassoc]
lemma locallyFiniteChainComplexToLimComplexOfInjective_comp_limComplexMap
    (hj : Function.Injective j.hom) {K K' : CompactExhaustion V} (h : ∀ n, K n ⊆ K' n) :
    locallyFiniteChainComplexToLimComplexOfInjective L K' hj ≫
        ComplexTower.limComplexMap (relativeChainComplexTowerMap L
          (fun n ↦ Set.image_mono (K.subset_succ n))
          (fun n ↦ Set.image_mono (K'.subset_succ n))
          fun n ↦ Set.image_mono (h n)) =
      locallyFiniteChainComplexToLimComplexOfInjective L K hj := by
  rw [locallyFiniteChainComplexToLimComplexOfInjective,
    locallyFiniteChainComplexToLimComplexOfInjective,
    locallyFiniteChainComplexIsoLimComplex_hom_eq, locallyFiniteChainComplexIsoLimComplex_hom_eq,
    Category.assoc]
  exact locallyFiniteChainComplexToLimComplex_comp_limComplexMap_excision L K.subset_succ
    K'.subset_succ K.isCompact K'.isCompact h hj

private lemma borelMooreHomologyRestrictOfExhaustion_eq_of_subset (hj : IsOpenEmbedding j.hom)
    {K K' : CompactExhaustion V} (h : ∀ n, K n ⊆ K' n)
    (hK : ∀ n, closure (j.hom '' K n) ⊆ Set.range j.hom)
    (hK' : ∀ n, closure (j.hom '' K' n) ⊆ Set.range j.hom) (k : ℕ) :
    borelMooreHomologyRestrictOfExhaustion L hj K' hK' k =
      borelMooreHomologyRestrictOfExhaustion L hj K hK k := by
  rw [eq_borelMooreHomologyRestrictOfExhaustion_iff]
  calc borelMooreHomologyRestrictOfExhaustion L hj K' hK' k ≫
        HomologicalComplex.homologyMap
          (locallyFiniteChainComplexToLimComplexOfInjective L K hj.injective) k
    _ = (borelMooreHomologyRestrictOfExhaustion L hj K' hK' k ≫
          HomologicalComplex.homologyMap
            (locallyFiniteChainComplexToLimComplexOfInjective L K' hj.injective) k) ≫
          HomologicalComplex.homologyMap
            (ComplexTower.limComplexMap (relativeChainComplexTowerMap L
              (fun n ↦ Set.image_mono (K.subset_succ n))
              (fun n ↦ Set.image_mono (K'.subset_succ n))
              fun n ↦ Set.image_mono (h n))) k := by
        rw [← locallyFiniteChainComplexToLimComplexOfInjective_comp_limComplexMap L hj.injective h,
          HomologicalComplex.homologyMap_comp, Category.assoc]
    _ = HomologicalComplex.homologyMap
          (locallyFiniteChainComplexToLimComplex L (fun n ↦ j.hom '' K n)
            (fun n ↦ Set.image_mono (K.subset_succ n))
            (fun n ↦ (K.isCompact n).image j.hom.continuous)) k := by
      simp only [← HomologicalComplex.homologyMap_comp,
        borelMooreHomologyRestrictOfExhaustion_comp_locallyFiniteChainComplexToLimComplexOfInjective
      ]
      rw [locallyFiniteChainComplexToLimComplex_comp_limComplexMap]

/-- **Exhaustion independence of open restriction.** Any two compact exhaustions of `V` whose
images in `X` have closure in `Set.range j` define the same open restriction map on Borel–Moore
homology. -/
theorem borelMooreHomologyRestrictOfExhaustion_eq (hj : IsOpenEmbedding j.hom)
    (K K' : CompactExhaustion V)
    (hK : ∀ n, closure (j.hom '' K n) ⊆ Set.range j.hom)
    (hK' : ∀ n, closure (j.hom '' K' n) ⊆ Set.range j.hom) (k : ℕ) :
    borelMooreHomologyRestrictOfExhaustion L hj K hK k =
      borelMooreHomologyRestrictOfExhaustion L hj K' hK' k := by
  let K'' := K.union K'
  have hK'' (n : ℕ) : closure (j.hom '' K'' n) ⊆ Set.range j.hom := by
    simp only [K'', CompactExhaustion.union_apply, Set.image_union, closure_union]
    exact Set.union_subset (hK n) (hK' n)
  exact (borelMooreHomologyRestrictOfExhaustion_eq_of_subset L hj
      (fun _ ↦ by simp [K'']) hK hK'' k).symm.trans
    (borelMooreHomologyRestrictOfExhaustion_eq_of_subset L hj
      (fun _ ↦ by simp [K'']) hK' hK'' k)

end ExhaustionRestriction

section CanonicalRestriction

variable {V X : TopCat.{v}}

/-- **Canonical open restriction in Borel–Moore homology.** For an open embedding `j : V ⟶ X`
into a Hausdorff space `X` from a weakly locally compact, sigma-compact space `V`, this is the
restriction morphism `Hₖ^BM(X; L) ⟶ Hₖ^BM(V; j⁎L)`. It agrees with
`borelMooreHomologyRestrictOfExhaustion` for every compact exhaustion of `V`. -/
def borelMooreHomologyRestrict [T2Space X] [WeaklyLocallyCompactSpace V] [SigmaCompactSpace V]
    (j : V ⟶ X) (hj : IsOpenEmbedding j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R X) (k : ℕ) :
    borelMooreHomology L k ⟶ borelMooreHomology ((pullback j.hom).obj L) k :=
  borelMooreHomologyRestrictOfExhaustion L hj (CompactExhaustion.choice V)
    ((CompactExhaustion.choice V).closure_image_subset_range j.hom.continuous) k

/-- Canonical open restriction agrees with the exhaustion-explicit restriction for every compact
exhaustion of `V`. -/
theorem borelMooreHomologyRestrict_eq_ofExhaustion [T2Space X] [WeaklyLocallyCompactSpace V]
    [SigmaCompactSpace V] (j : V ⟶ X) (hj : IsOpenEmbedding j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R X) (K : CompactExhaustion V)
    (hK : ∀ n, closure (j.hom '' K n) ⊆ Set.range j.hom) (k : ℕ) :
    borelMooreHomologyRestrict j hj L k =
      borelMooreHomologyRestrictOfExhaustion L hj K hK k :=
  borelMooreHomologyRestrictOfExhaustion_eq L hj _ K _ hK k

/-- Canonical open restriction followed by mapping into the `n`-th relative stage of
`CompactExhaustion.choice V` agrees with mapping directly into the `n`-th relative stage of `X`. -/
@[reassoc]
theorem borelMooreHomologyRestrict_comp_locallyFiniteChainComplexToRelative
    [T2Space X] [WeaklyLocallyCompactSpace V] [SigmaCompactSpace V]
    (j : V ⟶ X) (hj : IsOpenEmbedding j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R X) (k n : ℕ) :
    borelMooreHomologyRestrict j hj L k ≫
        HomologicalComplex.homologyMap
          ((TopPair.ofSubset (CompactExhaustion.choice V n)ᶜ).locallyFiniteChainComplexToRelative
              ((pullback j.hom).obj L)
              ((CompactExhaustion.choice V).isCompact n).compl_range_ofSubset_compl_map ≫
            TopPair.twistedChainComplexMapOfFstEq (TopPair.ofSubsetMap j
              (Set.SurjOn.mapsTo_compl
                (Set.surjOn_image j.hom (CompactExhaustion.choice V n)) hj.injective))
              (TopPair.ofSubsetMap_fst _ _) L) k =
      HomologicalComplex.homologyMap
        (TopPair.locallyFiniteChainComplexToRelative
          (TopPair.ofSubset (j.hom '' CompactExhaustion.choice V n)ᶜ) L
          (((CompactExhaustion.choice V).isCompact n).image
            j.hom.continuous).compl_range_ofSubset_compl_map) k := by
  rw [borelMooreHomologyRestrict_eq_ofExhaustion j hj L (CompactExhaustion.choice V)
    ((CompactExhaustion.choice V).closure_image_subset_range j.hom.continuous) k]
  exact borelMooreHomologyRestrictOfExhaustion_comp_locallyFiniteChainComplexToRelative L hj
    (CompactExhaustion.choice V) _ k n

end CanonicalRestriction

end TauCeti.LocalCoefficientSystem
