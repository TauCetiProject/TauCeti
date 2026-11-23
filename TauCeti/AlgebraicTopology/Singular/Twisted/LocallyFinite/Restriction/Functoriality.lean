/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Restriction.Basic
import TauCeti.Topology.Compactness.SigmaCompact

/-!
# Functoriality and naturality of Borel–Moore open restriction

This file establishes the functoriality and naturality laws for open restriction in Borel–Moore
homology (`TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrictOfExhaustion` and
`TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrict`):

* naturality in morphisms of local coefficient systems (`borelMooreHomologyRestrict_naturality`),
* identity law (`borelMooreHomologyRestrict_id`),
* contravariant composition law for composable open embeddings `W ⟶ V ⟶ X`
  (`borelMooreHomologyRestrict_comp`).

## Main results

* `TauCeti.LocalCoefficientSystem.locallyFiniteChainComplexToLimComplexOfInjective_naturality`:
  naturality of the excision chain map in local coefficient morphisms.
* `TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrictOfExhaustion_naturality` and
  `TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrict_naturality`: naturality in local
  coefficient morphisms.
* `TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrictOfExhaustion_id` and
  `TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrict_id`: restriction along the identity.
* `TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrictOfExhaustion_comp` and
  `TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrict_comp`: contravariant functoriality
  under composition of open embeddings.

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

section ExhaustionRestriction

variable {V X : TopCat.{v}} {j : V ⟶ X}
  (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- `locallyFiniteChainComplexToLimComplexOfInjective` is natural in morphisms of local coefficient
systems. -/
@[reassoc]
lemma locallyFiniteChainComplexToLimComplexOfInjective_naturality (hj : Function.Injective j.hom)
    {L K : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ K) (E : CompactExhaustion V) :
    locallyFiniteChainComplexCoefficientMap ((pullback j.hom).map η) ≫
        locallyFiniteChainComplexToLimComplexOfInjective K E hj =
      locallyFiniteChainComplexToLimComplexOfInjective L E hj ≫
        ComplexTower.limComplexMap (relativeChainComplexTowerCoefficientMap η
          (fun n ↦ j.hom '' E n) fun n ↦ Set.image_mono (E.subset_succ n)) := by
  apply (relativeChainComplexTower K (fun n ↦ j.hom '' E n)
    (fun n ↦ Set.image_mono (E.subset_succ n))).isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  simp only [ComplexTower.limComplexCone_π_app, Category.assoc,
    ComplexTower.limComplexMap_comp_π,
    locallyFiniteChainComplexToLimComplexOfInjective_comp_limComplexπ,
    locallyFiniteChainComplexToLimComplexOfInjective_comp_limComplexπ_assoc]
  -- `(TopPair.ofSubset _).fst` is only definitionally `V`/`X`, so explicit `trans` aligns the
  -- ambient types across the coefficient-map and pair-map naturality lemmas.
  let p := TopPair.ofSubsetMap j (Set.SurjOn.mapsTo_compl (Set.surjOn_image j.hom (E n)) hj)
  trans (TopPair.ofSubset (E n)ᶜ).locallyFiniteChainComplexToRelative ((pullback j.hom).obj L)
        (E.isCompact n).compl_range_ofSubset_compl_map ≫
      (TopPair.ofSubset (E n)ᶜ).twistedChainComplexCoefficientMap ((pullback j.hom).map η) ≫
      TopPair.twistedChainComplexMapOfFstEq p (TopPair.ofSubsetMap_fst _ _) K
  · exact
      TopPair.locallyFiniteChainComplexCoefficientMap_comp_locallyFiniteChainComplexToRelative_assoc
        (TopPair.ofSubset (E n)ᶜ) ((pullback j.hom).map η)
        (E.isCompact n).compl_range_ofSubset_compl_map _
  trans (TopPair.ofSubset (E n)ᶜ).locallyFiniteChainComplexToRelative ((pullback j.hom).obj L)
        (E.isCompact n).compl_range_ofSubset_compl_map ≫
      TopPair.twistedChainComplexMapOfFstEq p (TopPair.ofSubsetMap_fst _ _) L ≫
      (TopPair.ofSubset (j.hom '' E n)ᶜ).twistedChainComplexCoefficientMap η
  · exact congrArg (_ ≫ ·)
      (TopPair.twistedChainComplexMapOfFstEq_naturality p (TopPair.ofSubsetMap_fst _ _) η).symm
  · rw [relativeChainComplexTowerCoefficientMap_app]
    exact (Category.assoc _ _ _).symm

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
  have := quasiIso_locallyFiniteChainComplexToLimComplexOfInjective K E hj hE
  have hrL :=
    borelMooreHomologyRestrictOfExhaustion_comp_locallyFiniteChainComplexToLimComplexOfInjective
      L hj E hE k
  have hrK :=
    borelMooreHomologyRestrictOfExhaustion_comp_locallyFiniteChainComplexToLimComplexOfInjective
      K hj E hE k
  rw [← cancel_mono (HomologicalComplex.homologyMap
      (locallyFiniteChainComplexToLimComplexOfInjective K E hj.injective) k),
    Category.assoc, hrK]
  calc borelMooreHomologyCoefficientMap η k ≫
        HomologicalComplex.homologyMap
          (locallyFiniteChainComplexToLimComplex K (fun n ↦ j.hom '' E n)
            (fun n ↦ Set.image_mono (E.subset_succ n))
            (fun n ↦ (E.isCompact n).image j.hom.continuous)) k
    _ = HomologicalComplex.homologyMap
          (locallyFiniteChainComplexToLimComplex L (fun n ↦ j.hom '' E n)
            (fun n ↦ Set.image_mono (E.subset_succ n))
            (fun n ↦ (E.isCompact n).image j.hom.continuous)) k ≫
          HomologicalComplex.homologyMap
            (ComplexTower.limComplexMap (relativeChainComplexTowerCoefficientMap η
              (fun n ↦ j.hom '' E n) fun n ↦ Set.image_mono (E.subset_succ n))) k := by
        rw [← HomologicalComplex.homologyMap_comp,
          locallyFiniteChainComplexToLimComplex_naturality, HomologicalComplex.homologyMap_comp]
    _ = borelMooreHomologyRestrictOfExhaustion L hj E hE k ≫
          borelMooreHomologyCoefficientMap ((pullback j.hom).map η) k ≫
            HomologicalComplex.homologyMap
              (locallyFiniteChainComplexToLimComplexOfInjective K E hj.injective) k := by
        rw [← hrL, Category.assoc, ← HomologicalComplex.homologyMap_comp,
          ← locallyFiniteChainComplexToLimComplexOfInjective_naturality,
          HomologicalComplex.homologyMap_comp]
    _ = (borelMooreHomologyRestrictOfExhaustion L hj E hE k ≫
          borelMooreHomologyCoefficientMap ((pullback j.hom).map η) k) ≫
          HomologicalComplex.homologyMap
            (locallyFiniteChainComplexToLimComplexOfInjective K E hj.injective) k :=
        (Category.assoc _ _ _).symm

/-- Open restriction along the identity map is the coefficient comparison `pullbackIdIso.inv`. -/
theorem borelMooreHomologyRestrictOfExhaustion_id
    (hid : IsOpenEmbedding (TopCat.Hom.hom (𝟙 X))) (K : CompactExhaustion X) (k : ℕ) :
    borelMooreHomologyRestrictOfExhaustion L (j := 𝟙 X) hid K (fun _ ↦ by simp) k =
      borelMooreHomologyCoefficientMap ((pullbackIdIso X).inv.app L) k := by
  refine ((eq_borelMooreHomologyRestrictOfExhaustion_iff L (j := 𝟙 X) hid K
    (fun _ ↦ by simp) k _).2 ?_).symm
  rw [← HomologicalComplex.homologyMap_comp]
  congr 1
  apply (relativeChainComplexTower L (fun n ↦ TopCat.Hom.hom (𝟙 X) '' K n)
    (fun n ↦ Set.image_mono (K.subset_succ n))).isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  have hEq : (K n)ᶜ = (TopCat.Hom.hom (𝟙 X) '' K n)ᶜ := by simp
  let p := TopPair.ofSubsetMap (𝟙 X)
    (Set.SurjOn.mapsTo_compl (Set.surjOn_image (TopCat.Hom.hom (𝟙 X)) (K n)) hid.injective)
  have hcomp : (TopPair.ofSubset (K n)ᶜ).twistedChainComplexCoefficientMap
        ((pullbackIdIso X).inv.app L) ≫
      TopPair.twistedChainComplexMapOfFstEq p (TopPair.ofSubsetMap_fst _ _) L =
      eqToHom (congrArg (fun A : Set X ↦ (TopPair.ofSubset A).twistedChainComplex L) hEq) := by
    apply (TopPair.ofSubset (K n)ᶜ).twistedChainComplex_hom_ext L
    have hfst : twistedChainComplexCoefficientMap ((pullbackIdIso X).inv.app L) ≫
        twistedChainComplexMap (𝟙 X) L = 𝟙 (twistedChainComplex L) := by
      rw [twistedChainComplexMap_id, ← twistedChainComplexCoefficientMap_comp]
      simp
    have h1 : (TopPair.ofSubset (K n)ᶜ).twistedChainComplexπ L ≫
        (TopPair.ofSubset (K n)ᶜ).twistedChainComplexCoefficientMap
          ((pullbackIdIso X).inv.app L) ≫
        TopPair.twistedChainComplexMapOfFstEq p (TopPair.ofSubsetMap_fst _ _) L =
        (TopPair.ofSubset (TopCat.Hom.hom (𝟙 X) '' K n)ᶜ).twistedChainComplexπ L := by
      -- `(TopPair.ofSubset _).fst` is only definitionally `X`, so `trans` aligns the ambient types.
      trans twistedChainComplexCoefficientMap ((pullbackIdIso X).inv.app L) ≫
          (TopPair.ofSubset (K n)ᶜ).twistedChainComplexπ
            ((pullback (TopCat.Hom.hom (𝟙 X))).obj L) ≫
          TopPair.twistedChainComplexMapOfFstEq p (TopPair.ofSubsetMap_fst _ _) L
      · exact TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc
          (TopPair.ofSubset (K n)ᶜ) ((pullbackIdIso X).inv.app L) _
      trans twistedChainComplexCoefficientMap ((pullbackIdIso X).inv.app L) ≫
          twistedChainComplexMap (𝟙 X) L ≫
          (TopPair.ofSubset (TopCat.Hom.hom (𝟙 X) '' K n)ᶜ).twistedChainComplexπ L
      · exact congrArg (_ ≫ ·)
          (TopPair.twistedChainComplexπ_comp_twistedChainComplexMapOfFstEq p
            (TopPair.ofSubsetMap_fst _ _) L)
      trans (twistedChainComplexCoefficientMap ((pullbackIdIso X).inv.app L) ≫
          twistedChainComplexMap (𝟙 X) L) ≫
          (TopPair.ofSubset (TopCat.Hom.hom (𝟙 X) '' K n)ᶜ).twistedChainComplexπ L
      · exact (Category.assoc _ _ _).symm
      · exact (congrArg (· ≫ _) hfst).trans (Category.id_comp _)
    refine h1.trans ?_
    generalize hS : (TopCat.Hom.hom (𝟙 X) '' K n)ᶜ = S at hEq ⊢
    subst hEq
    simp
  simp only [ComplexTower.limComplexCone_π_app, Category.assoc,
    locallyFiniteChainComplexToLimComplexOfInjective_comp_limComplexπ,
    locallyFiniteChainComplexToLimComplex_comp_limComplexπ]
  -- Align `(TopPair.ofSubset (K n)ᶜ).fst` with `X` via `trans`.
  trans (TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative L
        (K.isCompact n).compl_range_ofSubset_compl_map ≫
      (TopPair.ofSubset (K n)ᶜ).twistedChainComplexCoefficientMap
        ((pullbackIdIso X).inv.app L) ≫
      TopPair.twistedChainComplexMapOfFstEq p (TopPair.ofSubsetMap_fst _ _) L
  · exact
      TopPair.locallyFiniteChainComplexCoefficientMap_comp_locallyFiniteChainComplexToRelative_assoc
        (TopPair.ofSubset (K n)ᶜ) ((pullbackIdIso X).inv.app L)
        (K.isCompact n).compl_range_ofSubset_compl_map _
  trans (TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative L
        (K.isCompact n).compl_range_ofSubset_compl_map ≫
      eqToHom (congrArg (fun A : Set X ↦ (TopPair.ofSubset A).twistedChainComplex L) hEq)
  · exact congrArg (_ ≫ ·) hcomp
  · exact locallyFiniteChainComplexToRelative_congr L hEq _ _

section CompHelpers

variable {W : TopCat.{v}} {i : W ⟶ V}

private lemma image_comp_subset {KW : CompactExhaustion W} {KV' : CompactExhaustion V}
    (hsub : ∀ n, i.hom '' KW n ⊆ KV' n) (n : ℕ) :
    (i ≫ j).hom '' KW n ⊆ j.hom '' KV' n := by
  have h : (i ≫ j).hom '' KW n = j.hom '' (i.hom '' KW n) := by simp [Set.image_image]
  rw [h]
  exact Set.image_mono (hsub n)

private abbrev compTowerExcisionJ (hj : Function.Injective j.hom) (KW : CompactExhaustion W) :
    relativeChainComplexTower ((pullback j.hom).obj L) (fun n ↦ i.hom '' KW n)
        (fun n ↦ Set.image_mono (KW.subset_succ n)) ⟶
      relativeChainComplexTower L (fun n ↦ (i ≫ j).hom '' KW n)
        (fun n ↦ Set.image_mono (KW.subset_succ n)) :=
  excisionRelativeChainComplexTowerMap L (fun n ↦ i.hom '' KW n)
      (fun n ↦ Set.image_mono (KW.subset_succ n)) hj ≫
    relativeChainComplexTowerMap L (fun n ↦ Set.image_mono (KW.subset_succ n))
      (fun n ↦ Set.image_mono (Set.image_mono (KW.subset_succ n)))
      fun n ↦ (Set.image_image j.hom i.hom (KW n)).ge

private lemma comp_middle_square (hj : Function.Injective j.hom)
    (KW : CompactExhaustion W) (KV' : CompactExhaustion V)
    (hsub : ∀ n, i.hom '' KW n ⊆ KV' n) :
    locallyFiniteChainComplexToLimComplexOfInjective L KV' hj ≫
        ComplexTower.limComplexMap (relativeChainComplexTowerMap L
          (fun n ↦ Set.image_mono (KW.subset_succ n))
          (fun n ↦ Set.image_mono (KV'.subset_succ n))
          (image_comp_subset (i := i) (j := j) hsub)) =
      locallyFiniteChainComplexToLimComplex ((pullback j.hom).obj L) (fun n ↦ i.hom '' KW n)
          (fun n ↦ Set.image_mono (KW.subset_succ n))
          (fun n ↦ (KW.isCompact n).image i.hom.continuous) ≫
        ComplexTower.limComplexMap (compTowerExcisionJ (i := i) (j := j) L hj KW) := by
  have hcomp := relativeChainComplexTowerMap_comp L
    (fun n ↦ Set.image_mono (KW.subset_succ n))
    (fun n ↦ Set.image_mono (Set.image_mono (KW.subset_succ n)))
    (fun n ↦ Set.image_mono (KV'.subset_succ n))
    (fun n ↦ (Set.image_image j.hom i.hom (KW n)).ge)
    fun n ↦ Set.image_mono (hsub n)
  rw [← hcomp, ComplexTower.limComplexMap_comp,
    locallyFiniteChainComplexToLimComplexOfInjective_eq, Category.assoc,
    locallyFiniteChainComplexToLimComplex_comp_limComplexMap_excision_assoc L
      (fun n ↦ Set.image_mono (KW.subset_succ n)) KV'.subset_succ
      (fun n ↦ (KW.isCompact n).image i.hom.continuous) KV'.isCompact hsub hj,
    ← ComplexTower.limComplexMap_comp]

private lemma comp_right_square (hi : Function.Injective i.hom) (hj : Function.Injective j.hom)
    (hij : Function.Injective (i ≫ j).hom) (KW : CompactExhaustion W) :
    locallyFiniteChainComplexCoefficientMap ((pullbackCompIso i.hom j.hom).hom.app L) ≫
        locallyFiniteChainComplexToLimComplexOfInjective ((pullback j.hom).obj L) KW hi ≫
          ComplexTower.limComplexMap (compTowerExcisionJ (i := i) (j := j) L hj KW) =
      locallyFiniteChainComplexToLimComplexOfInjective L KW hij := by
  apply (relativeChainComplexTower L (fun n ↦ (i ≫ j).hom '' KW n)
    (fun n ↦ Set.image_mono (KW.subset_succ n))).isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  let φ := compTowerExcisionJ (i := i) (j := j) L hj KW
  let pᵢ := TopPair.ofSubsetMap i (Set.SurjOn.mapsTo_compl (Set.surjOn_image i.hom (KW n)) hi)
  let pⱼ := TopPair.ofSubsetMap j
    (Set.SurjOn.mapsTo_compl (Set.surjOn_image j.hom (i.hom '' KW n)) hj)
  let pᵢⱼ := TopPair.ofSubsetMap (i ≫ j)
    (Set.SurjOn.mapsTo_compl (Set.surjOn_image (i ≫ j).hom (KW n)) hij)
  have hmap : (TopPair.ofSubset (KW n)ᶜ).twistedChainComplexCoefficientMap
        ((pullbackCompIso i.hom j.hom).hom.app L) ≫
      TopPair.twistedChainComplexMapOfFstEq pᵢ (TopPair.ofSubsetMap_fst _ _)
          ((pullback j.hom).obj L) ≫
        φ.app (op n) =
      TopPair.twistedChainComplexMapOfFstEq pᵢⱼ (TopPair.ofSubsetMap_fst _ _) L := by
    apply (TopPair.ofSubset (KW n)ᶜ).twistedChainComplex_hom_ext _
    -- `(TopPair.ofSubset _).fst` is only definitionally `W`/`V`/`X`; `trans` aligns ambient types.
    trans twistedChainComplexCoefficientMap ((pullbackCompIso i.hom j.hom).hom.app L) ≫
        (TopPair.ofSubset (KW n)ᶜ).twistedChainComplexπ
          ((pullback i.hom).obj ((pullback j.hom).obj L)) ≫
        TopPair.twistedChainComplexMapOfFstEq pᵢ (TopPair.ofSubsetMap_fst _ _)
          ((pullback j.hom).obj L) ≫
        φ.app (op n)
    · exact TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc
        (TopPair.ofSubset (KW n)ᶜ) ((pullbackCompIso i.hom j.hom).hom.app L) _
    trans twistedChainComplexCoefficientMap ((pullbackCompIso i.hom j.hom).hom.app L) ≫
        twistedChainComplexMap i ((pullback j.hom).obj L) ≫
        (TopPair.ofSubset (i.hom '' KW n)ᶜ).twistedChainComplexπ ((pullback j.hom).obj L) ≫
        (excisionRelativeChainComplexTowerMap L (fun n ↦ i.hom '' KW n)
          (fun n ↦ Set.image_mono (KW.subset_succ n)) hj).app (op n) ≫
        (relativeChainComplexTowerMap L (fun n ↦ Set.image_mono (KW.subset_succ n))
          (fun n ↦ Set.image_mono (Set.image_mono (KW.subset_succ n)))
          (fun n ↦ (Set.image_image j.hom i.hom (KW n)).ge)).app (op n)
    · exact congrArg (_ ≫ ·)
        (TopPair.twistedChainComplexπ_comp_twistedChainComplexMapOfFstEq_assoc
          pᵢ (TopPair.ofSubsetMap_fst _ _) ((pullback j.hom).obj L) _)
    trans twistedChainComplexCoefficientMap ((pullbackCompIso i.hom j.hom).hom.app L) ≫
        twistedChainComplexMap i ((pullback j.hom).obj L) ≫
        twistedChainComplexMap j L ≫
        (TopPair.ofSubset (j.hom '' (i.hom '' KW n))ᶜ).twistedChainComplexπ L ≫
        (relativeChainComplexTowerMap L (fun n ↦ Set.image_mono (KW.subset_succ n))
          (fun n ↦ Set.image_mono (Set.image_mono (KW.subset_succ n)))
          (fun n ↦ (Set.image_image j.hom i.hom (KW n)).ge)).app (op n)
    · rw [excisionRelativeChainComplexTowerMap_app]
      exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·)
        (TopPair.twistedChainComplexπ_comp_twistedChainComplexMapOfFstEq_assoc pⱼ
          (TopPair.ofSubsetMap_fst _ _) L _))
    trans twistedChainComplexCoefficientMap ((pullbackCompIso i.hom j.hom).hom.app L) ≫
        twistedChainComplexMap i ((pullback j.hom).obj L) ≫
        twistedChainComplexMap j L ≫
        (TopPair.ofSubset ((i ≫ j).hom '' KW n)ᶜ).twistedChainComplexπ L
    · exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (congrArg (_ ≫ ·)
        (twistedChainComplexπ_comp_relativeChainComplexTowerMap_app L _ _ _ n)))
    trans (twistedChainComplexCoefficientMap ((pullbackCompIso i.hom j.hom).hom.app L) ≫
          twistedChainComplexMap i ((pullback j.hom).obj L) ≫
          twistedChainComplexMap j L) ≫
        (TopPair.ofSubset ((i ≫ j).hom '' KW n)ᶜ).twistedChainComplexπ L
    · exact (Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm
    trans twistedChainComplexMap (i ≫ j) L ≫
        (TopPair.ofSubset ((i ≫ j).hom '' KW n)ᶜ).twistedChainComplexπ L
    · exact congrArg (· ≫ _) (twistedChainComplexMap_comp i j L).symm
    · exact (TopPair.twistedChainComplexπ_comp_twistedChainComplexMapOfFstEq pᵢⱼ
        (TopPair.ofSubsetMap_fst _ _) L).symm
  simp only [ComplexTower.limComplexCone_π_app, Category.assoc,
    ComplexTower.limComplexMap_comp_π,
    locallyFiniteChainComplexToLimComplexOfInjective_comp_limComplexπ,
    locallyFiniteChainComplexToLimComplexOfInjective_comp_limComplexπ_assoc]
  -- Align `(TopPair.ofSubset (KW n)ᶜ).fst` with `W` via `trans`.
  trans locallyFiniteChainComplexCoefficientMap ((pullbackCompIso i.hom j.hom).hom.app L) ≫
      (TopPair.ofSubset (KW n)ᶜ).locallyFiniteChainComplexToRelative
        ((pullback i.hom).obj ((pullback j.hom).obj L))
        (KW.isCompact n).compl_range_ofSubset_compl_map ≫
      TopPair.twistedChainComplexMapOfFstEq pᵢ (TopPair.ofSubsetMap_fst _ _)
        ((pullback j.hom).obj L) ≫
      φ.app (op n)
  · exact congrArg (_ ≫ ·) (Category.assoc _ _ _)
  trans (TopPair.ofSubset (KW n)ᶜ).locallyFiniteChainComplexToRelative
        ((pullback (i ≫ j).hom).obj L) (KW.isCompact n).compl_range_ofSubset_compl_map ≫
      (TopPair.ofSubset (KW n)ᶜ).twistedChainComplexCoefficientMap
        ((pullbackCompIso i.hom j.hom).hom.app L) ≫
      TopPair.twistedChainComplexMapOfFstEq pᵢ (TopPair.ofSubsetMap_fst _ _)
        ((pullback j.hom).obj L) ≫
      φ.app (op n)
  · exact
      TopPair.locallyFiniteChainComplexCoefficientMap_comp_locallyFiniteChainComplexToRelative_assoc
        (TopPair.ofSubset (KW n)ᶜ) ((pullbackCompIso i.hom j.hom).hom.app L)
        (KW.isCompact n).compl_range_ofSubset_compl_map _
  · exact congrArg (_ ≫ ·) hmap

private lemma quasiIso_locallyFiniteChainComplexToLimComplexOfInjective_comp
    (hi : IsOpenEmbedding i.hom) (hj : IsOpenEmbedding j.hom) (KW : CompactExhaustion W)
    (hKW_X : ∀ n, closure ((i ≫ j).hom '' KW n) ⊆ Set.range (i ≫ j).hom) :
    QuasiIso (locallyFiniteChainComplexToLimComplexOfInjective ((pullback j.hom).obj L) KW
        hi.injective ≫
      ComplexTower.limComplexMap (compTowerExcisionJ (i := i) (j := j) L hj.injective KW)) := by
  have : QuasiIso
      (locallyFiniteChainComplexCoefficientMap ((pullbackCompIso i.hom j.hom).hom.app L)) :=
    quasiIso_of_isIso _
  have := quasiIso_locallyFiniteChainComplexToLimComplexOfInjective L KW (hj.comp hi) hKW_X
  have h3 := comp_right_square (i := i) (j := j) L hi.injective hj.injective
    (hj.comp hi).injective KW
  have : QuasiIso
      (locallyFiniteChainComplexCoefficientMap ((pullbackCompIso i.hom j.hom).hom.app L) ≫
        locallyFiniteChainComplexToLimComplexOfInjective ((pullback j.hom).obj L) KW
          hi.injective ≫
        ComplexTower.limComplexMap (compTowerExcisionJ (i := i) (j := j) L hj.injective KW)) := by
    rw [h3]
    infer_instance
  exact quasiIso_of_comp_left
    (locallyFiniteChainComplexCoefficientMap ((pullbackCompIso i.hom j.hom).hom.app L)) _

end CompHelpers

/-- Composition law for exhaustion-explicit open restrictions. -/
theorem borelMooreHomologyRestrictOfExhaustion_comp {W : TopCat.{v}} {i : W ⟶ V}
    (hi : IsOpenEmbedding i.hom) (hj : IsOpenEmbedding j.hom)
    (KW : CompactExhaustion W) (KV : CompactExhaustion V)
    (hKW_X : ∀ n, closure ((i ≫ j).hom '' KW n) ⊆ Set.range (i ≫ j).hom)
    (hKV_X : ∀ n, closure (j.hom '' KV n) ⊆ Set.range j.hom) (k : ℕ) :
    borelMooreHomologyRestrictOfExhaustion L hj KV hKV_X k ≫
        borelMooreHomologyRestrictOfExhaustion ((pullback j.hom).obj L) hi KW
          (fun n ↦ by
            rw [hj.isEmbedding.closure_eq_preimage_closure_image]
            intro v hv
            have hv' : j.hom v ∈ closure ((i ≫ j).hom '' KW n) := by
              simpa only [Set.mem_preimage, Set.image_image, TopCat.hom_comp,
                ContinuousMap.coe_comp, Function.comp_apply] using hv
            obtain ⟨w, hw⟩ := hKW_X n hv'
            exact ⟨w, hj.injective hw⟩) k =
      borelMooreHomologyRestrictOfExhaustion L (j := i ≫ j) (hj.comp hi) KW hKW_X k ≫
        borelMooreHomologyCoefficientMap ((pullbackCompIso i.hom j.hom).hom.app L) k := by
  -- Enlarge `KV` to `KV' := KV.unionImage KW` so `i '' KW n ⊆ KV' n` for every `n`, then cancel
  -- the quasi-isomorphism `locallyFiniteChainComplexToLimComplexOfInjective … ≫ limComplexMap`
  -- on the right and chase the three commuting squares (`comp_middle_square`,
  -- `locallyFiniteChainComplexToLimComplex_comp_limComplexMap`, and `comp_right_square`).
  have hKW_V (n : ℕ) : closure (i.hom '' KW n) ⊆ Set.range i.hom := by
    rw [hj.isEmbedding.closure_eq_preimage_closure_image]
    intro v hv
    have hv' : j.hom v ∈ closure ((i ≫ j).hom '' KW n) := by
      simpa only [Set.mem_preimage, Set.image_image, TopCat.hom_comp, ContinuousMap.coe_comp,
        Function.comp_apply] using hv
    obtain ⟨w, hw⟩ := hKW_X n hv'
    exact ⟨w, hj.injective hw⟩
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
  let eJ := compTowerExcisionJ (i := i) (j := j) L hj.injective KW
  have := quasiIso_locallyFiniteChainComplexToLimComplexOfInjective_comp
    (i := i) (j := j) L hi hj KW hKW_X
  have h3 := comp_right_square (i := i) (j := j) L hi.injective hj.injective
    (hj.comp hi).injective KW
  have hri :=
    borelMooreHomologyRestrictOfExhaustion_comp_locallyFiniteChainComplexToLimComplexOfInjective
      ((pullback j.hom).obj L) hi KW hKW_V k
  have hrj :=
    borelMooreHomologyRestrictOfExhaustion_comp_locallyFiniteChainComplexToLimComplexOfInjective
      L hj KV' hKV'_X k
  have hrij :=
    borelMooreHomologyRestrictOfExhaustion_comp_locallyFiniteChainComplexToLimComplexOfInjective
      L (j := i ≫ j) (hj.comp hi) KW hKW_X k
  rw [← cancel_mono (HomologicalComplex.homologyMap
    (locallyFiniteChainComplexToLimComplexOfInjective ((pullback j.hom).obj L) KW hi.injective ≫
      ComplexTower.limComplexMap eJ) k)]
  calc (borelMooreHomologyRestrictOfExhaustion L hj KV' hKV'_X k ≫
          borelMooreHomologyRestrictOfExhaustion ((pullback j.hom).obj L) hi KW _ k) ≫
        HomologicalComplex.homologyMap
          (locallyFiniteChainComplexToLimComplexOfInjective ((pullback j.hom).obj L) KW
              hi.injective ≫
            ComplexTower.limComplexMap eJ) k
    _ = borelMooreHomologyRestrictOfExhaustion L hj KV' hKV'_X k ≫
          HomologicalComplex.homologyMap
            (locallyFiniteChainComplexToLimComplex ((pullback j.hom).obj L)
                (fun n ↦ i.hom '' KW n) (fun n ↦ Set.image_mono (KW.subset_succ n))
                (fun n ↦ (KW.isCompact n).image i.hom.continuous) ≫
              ComplexTower.limComplexMap eJ) k := by
      rw [HomologicalComplex.homologyMap_comp, Category.assoc, reassoc_of% hri,
        ← HomologicalComplex.homologyMap_comp]
    _ = HomologicalComplex.homologyMap
          (locallyFiniteChainComplexToLimComplex L (fun n ↦ (i ≫ j).hom '' KW n)
            (fun n ↦ Set.image_mono (KW.subset_succ n))
            (fun n ↦ (KW.isCompact n).image (i ≫ j).hom.continuous)) k := by
      rw [← comp_middle_square L hj.injective KW KV' hsub, HomologicalComplex.homologyMap_comp,
        ← Category.assoc, hrj, ← HomologicalComplex.homologyMap_comp,
        locallyFiniteChainComplexToLimComplex_comp_limComplexMap]
    _ = (borelMooreHomologyRestrictOfExhaustion L (j := i ≫ j) (hj.comp hi) KW hKW_X k ≫
          borelMooreHomologyCoefficientMap ((pullbackCompIso i.hom j.hom).hom.app L) k) ≫
          HomologicalComplex.homologyMap
            (locallyFiniteChainComplexToLimComplexOfInjective ((pullback j.hom).obj L) KW
                hi.injective ≫
              ComplexTower.limComplexMap eJ) k := by
      rw [← hrij, ← h3, HomologicalComplex.homologyMap_comp, Category.assoc]

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
    ((CompactExhaustion.choice X).closure_image_subset_range
      (TopCat.Hom.hom (𝟙 X)).continuous) k]
  exact borelMooreHomologyRestrictOfExhaustion_id L hid (CompactExhaustion.choice X) k

/-- Open restriction is contravariantly functorial for composable open embeddings. -/
@[reassoc]
theorem borelMooreHomologyRestrict_comp [T2Space X] [T2Space V]
    {W : TopCat.{v}} [WeaklyLocallyCompactSpace W] [SigmaCompactSpace W]
    [WeaklyLocallyCompactSpace V] [SigmaCompactSpace V]
    (i : W ⟶ V) (j : V ⟶ X) (hi : IsOpenEmbedding i.hom) (hj : IsOpenEmbedding j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R X) (k : ℕ) :
    borelMooreHomologyRestrict j hj L k ≫
        borelMooreHomologyRestrict i hi ((pullback j.hom).obj L) k =
      borelMooreHomologyRestrict (i ≫ j) (hj.comp hi) L k ≫
        borelMooreHomologyCoefficientMap ((pullbackCompIso i.hom j.hom).hom.app L) k := by
  rw [borelMooreHomologyRestrict_eq_ofExhaustion j hj L (CompactExhaustion.choice V)
      ((CompactExhaustion.choice V).closure_image_subset_range j.hom.continuous) k,
    borelMooreHomologyRestrict_eq_ofExhaustion i hi ((pullback j.hom).obj L)
      (CompactExhaustion.choice W)
      ((CompactExhaustion.choice W).closure_image_subset_range i.hom.continuous) k,
    borelMooreHomologyRestrict_eq_ofExhaustion (i ≫ j) (hj.comp hi) L
      (CompactExhaustion.choice W)
      ((CompactExhaustion.choice W).closure_image_subset_range (i ≫ j).hom.continuous) k]
  exact borelMooreHomologyRestrictOfExhaustion_comp L hi hj
    (CompactExhaustion.choice W) (CompactExhaustion.choice V) _ _ k

/-- Open restriction is natural in morphisms of local coefficient systems. -/
@[reassoc]
theorem borelMooreHomologyRestrict_naturality [T2Space X] [WeaklyLocallyCompactSpace V]
    [SigmaCompactSpace V] (j : V ⟶ X) (hj : IsOpenEmbedding j.hom)
    {L K : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ K) (k : ℕ) :
    borelMooreHomologyCoefficientMap η k ≫ borelMooreHomologyRestrict j hj K k =
      borelMooreHomologyRestrict j hj L k ≫
        borelMooreHomologyCoefficientMap ((pullback j.hom).map η) k := by
  rw [borelMooreHomologyRestrict_eq_ofExhaustion j hj K (CompactExhaustion.choice V)
      ((CompactExhaustion.choice V).closure_image_subset_range j.hom.continuous) k,
    borelMooreHomologyRestrict_eq_ofExhaustion j hj L (CompactExhaustion.choice V)
      ((CompactExhaustion.choice V).closure_image_subset_range j.hom.continuous) k]
  exact borelMooreHomologyRestrictOfExhaustion_naturality hj η (CompactExhaustion.choice V) _ k

end CanonicalRestriction

end TauCeti.LocalCoefficientSystem
