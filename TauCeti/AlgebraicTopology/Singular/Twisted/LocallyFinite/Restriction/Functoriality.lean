/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Restriction.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Discrete
import TauCeti.Topology.Compactness.SigmaCompact

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
  trans (TopPair.ofSubset (E n)ᶜ).locallyFiniteChainComplexToRelative ((pullback j.hom).obj L)
        (E.isCompact n).compl_range_ofSubset_compl_map ≫
      (TopPair.ofSubset (E n)ᶜ).twistedChainComplexCoefficientMap ((pullback j.hom).map η) ≫
      TopPair.twistedChainComplexMap (injectivePairMap hj (E n)) K
  · exact
      TopPair.locallyFiniteChainComplexCoefficientMap_comp_locallyFiniteChainComplexToRelative_assoc
        (TopPair.ofSubset (E n)ᶜ) ((pullback j.hom).map η)
        (E.isCompact n).compl_range_ofSubset_compl_map _
  trans (TopPair.ofSubset (E n)ᶜ).locallyFiniteChainComplexToRelative ((pullback j.hom).obj L)
        (E.isCompact n).compl_range_ofSubset_compl_map ≫
      TopPair.twistedChainComplexMap (injectivePairMap hj (E n)) L ≫
      (TopPair.ofSubset (j.hom '' E n)ᶜ).twistedChainComplexCoefficientMap η
  · exact congrArg (_ ≫ ·)
      (TopPair.twistedChainComplexMap_naturality (injectivePairMap hj (E n)) L η).symm
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
        (TopPair.ofSubset (TopCat.Hom.hom (𝟙 X) '' K n)ᶜ).twistedChainComplexπ L := by
      -- `(TopPair.ofSubset _).fst` is only definitionally `X`, so `trans` aligns the ambient types.
      trans twistedChainComplexCoefficientMap ((pullbackIdIso X).inv.app L) ≫
          (TopPair.ofSubset (K n)ᶜ).twistedChainComplexπ
            ((pullback (TopCat.Hom.hom (𝟙 X))).obj L) ≫
          TopPair.twistedChainComplexMap (injectivePairMap (j := 𝟙 X) hid.injective (K n)) L
      · exact TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc
          (TopPair.ofSubset (K n)ᶜ) ((pullbackIdIso X).inv.app L) _
      trans twistedChainComplexCoefficientMap ((pullbackIdIso X).inv.app L) ≫
          twistedChainComplexMap (𝟙 X) L ≫
          (TopPair.ofSubset (TopCat.Hom.hom (𝟙 X) '' K n)ᶜ).twistedChainComplexπ L
      · exact congrArg (_ ≫ ·) (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap
          (injectivePairMap (j := 𝟙 X) hid.injective (K n)) L)
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
      TopPair.twistedChainComplexMap (injectivePairMap (j := 𝟙 X) hid.injective (K n)) L
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
  apply (relativeChainComplexTower L (fun n ↦ (i ≫ j).hom '' KW n)
    (fun n ↦ Set.image_mono (KW.subset_succ n))).isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  have hsqn : TopPair.twistedChainComplexMap (injectivePairMap hj (KV' n)) L ≫
        (relativeChainComplexTowerMap L
          (fun n ↦ Set.image_mono (KW.subset_succ n))
          (fun n ↦ Set.image_mono (KV'.subset_succ n))
          (image_comp_subset (i := i) (j := j) hsub)).app (op n) =
      (relativeChainComplexTowerMap ((pullback j.hom).obj L)
          (fun n ↦ Set.image_mono (KW.subset_succ n)) KV'.subset_succ hsub).app (op n) ≫
        (compTowerExcisionJ (i := i) (j := j) L hj KW).app (op n) := by
    apply (TopPair.ofSubset (KV' n)ᶜ).twistedChainComplex_hom_ext ((pullback j.hom).obj L)
    -- `(TopPair.ofSubset _).fst` is only definitionally `V`/`X`, so `trans` aligns ambient types.
    trans twistedChainComplexMap j L ≫
        (TopPair.ofSubset (j.hom '' KV' n)ᶜ).twistedChainComplexπ L ≫
        (relativeChainComplexTowerMap L
          (fun n ↦ Set.image_mono (KW.subset_succ n))
          (fun n ↦ Set.image_mono (KV'.subset_succ n))
          (image_comp_subset (i := i) (j := j) hsub)).app (op n)
    · exact TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc
        (injectivePairMap hj (KV' n)) L _
    trans twistedChainComplexMap j L ≫
        (TopPair.ofSubset ((i ≫ j).hom '' KW n)ᶜ).twistedChainComplexπ L
    · exact congrArg (_ ≫ ·)
        (twistedChainComplexπ_comp_relativeChainComplexTowerMap_app L _ _ _ n)
    trans twistedChainComplexMap j L ≫
        (TopPair.ofSubset (j.hom '' (i.hom '' KW n))ᶜ).twistedChainComplexπ L ≫
        (relativeChainComplexTowerMap L (fun n ↦ Set.image_mono (KW.subset_succ n))
          (fun n ↦ Set.image_mono (Set.image_mono (KW.subset_succ n)))
          (fun n ↦ (Set.image_image j.hom i.hom (KW n)).ge)).app (op n)
    · exact congrArg (_ ≫ ·)
        (twistedChainComplexπ_comp_relativeChainComplexTowerMap_app L
          (fun n ↦ Set.image_mono (KW.subset_succ n))
          (fun n ↦ Set.image_mono (Set.image_mono (KW.subset_succ n)))
          (fun n ↦ (Set.image_image j.hom i.hom (KW n)).ge) n).symm
    trans (TopPair.ofSubset (i.hom '' KW n)ᶜ).twistedChainComplexπ ((pullback j.hom).obj L) ≫
        (excisionRelativeChainComplexTowerMap L (fun n ↦ i.hom '' KW n)
          (fun n ↦ Set.image_mono (KW.subset_succ n)) hj).app (op n) ≫
        (relativeChainComplexTowerMap L (fun n ↦ Set.image_mono (KW.subset_succ n))
          (fun n ↦ Set.image_mono (Set.image_mono (KW.subset_succ n)))
          (fun n ↦ (Set.image_image j.hom i.hom (KW n)).ge)).app (op n)
    · rw [excisionRelativeChainComplexTowerMap_app]
      exact (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc
        (injectivePairMap hj (i.hom '' KW n)) L _).symm
    · exact (Category.assoc _ _ _).trans <|
        (twistedChainComplexπ_comp_relativeChainComplexTowerMap_app_assoc
          ((pullback j.hom).obj L) _ _ hsub n _).symm
  simp only [ComplexTower.limComplexCone_π_app, Category.assoc,
    ComplexTower.limComplexMap_comp_π,
    locallyFiniteChainComplexToLimComplexOfInjective_comp_limComplexπ_assoc,
    locallyFiniteChainComplexToLimComplex_comp_limComplexπ_assoc]
  -- Align `(TopPair.ofSubset _).fst` with `V`/`X` via `trans`.
  trans (TopPair.ofSubset (KV' n)ᶜ).locallyFiniteChainComplexToRelative ((pullback j.hom).obj L)
        (KV'.isCompact n).compl_range_ofSubset_compl_map ≫
      TopPair.twistedChainComplexMap (injectivePairMap hj (KV' n)) L ≫
      (relativeChainComplexTowerMap L
        (fun n ↦ Set.image_mono (KW.subset_succ n))
        (fun n ↦ Set.image_mono (KV'.subset_succ n))
        (image_comp_subset (i := i) (j := j) hsub)).app (op n)
  · exact Category.assoc _ _ _
  trans ((TopPair.ofSubset (KV' n)ᶜ).locallyFiniteChainComplexToRelative ((pullback j.hom).obj L)
          (KV'.isCompact n).compl_range_ofSubset_compl_map ≫
        (relativeChainComplexTowerMap ((pullback j.hom).obj L)
          (fun n ↦ Set.image_mono (KW.subset_succ n)) KV'.subset_succ hsub).app (op n)) ≫
      (compTowerExcisionJ (i := i) (j := j) L hj KW).app (op n)
  · exact (congrArg (_ ≫ ·) hsqn).trans (Category.assoc _ _ _).symm
  · exact congrArg (· ≫ _)
      (locallyFiniteChainComplexToRelative_comp_relativeChainComplexTowerMap_app
        ((pullback j.hom).obj L) (fun n ↦ Set.image_mono (KW.subset_succ n)) KV'.subset_succ
        (fun n ↦ (KW.isCompact n).image i.hom.continuous) KV'.isCompact hsub n)

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
  have hmap : (TopPair.ofSubset (KW n)ᶜ).twistedChainComplexCoefficientMap
        ((pullbackCompIso i.hom j.hom).hom.app L) ≫
      TopPair.twistedChainComplexMap (injectivePairMap hi (KW n)) ((pullback j.hom).obj L) ≫
        φ.app (op n) =
      TopPair.twistedChainComplexMap (injectivePairMap hij (KW n)) L := by
    apply (TopPair.ofSubset (KW n)ᶜ).twistedChainComplex_hom_ext _
    -- `(TopPair.ofSubset _).fst` is only definitionally `W`/`V`/`X`; `trans` aligns ambient types.
    trans twistedChainComplexCoefficientMap ((pullbackCompIso i.hom j.hom).hom.app L) ≫
        (TopPair.ofSubset (KW n)ᶜ).twistedChainComplexπ
          ((pullback i.hom).obj ((pullback j.hom).obj L)) ≫
        TopPair.twistedChainComplexMap (injectivePairMap hi (KW n)) ((pullback j.hom).obj L) ≫
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
        (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc
          (injectivePairMap hi (KW n)) ((pullback j.hom).obj L) _)
    trans twistedChainComplexCoefficientMap ((pullbackCompIso i.hom j.hom).hom.app L) ≫
        twistedChainComplexMap i ((pullback j.hom).obj L) ≫
        twistedChainComplexMap j L ≫
        (TopPair.ofSubset (j.hom '' (i.hom '' KW n))ᶜ).twistedChainComplexπ L ≫
        (relativeChainComplexTowerMap L (fun n ↦ Set.image_mono (KW.subset_succ n))
          (fun n ↦ Set.image_mono (Set.image_mono (KW.subset_succ n)))
          (fun n ↦ (Set.image_image j.hom i.hom (KW n)).ge)).app (op n)
    · rw [excisionRelativeChainComplexTowerMap_app]
      exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·)
        (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc
          (injectivePairMap hj (i.hom '' KW n)) L _))
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
    · exact (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap
        (injectivePairMap hij (KW n)) L).symm
  simp only [ComplexTower.limComplexCone_π_app, Category.assoc,
    ComplexTower.limComplexMap_comp_π,
    locallyFiniteChainComplexToLimComplexOfInjective_comp_limComplexπ,
    locallyFiniteChainComplexToLimComplexOfInjective_comp_limComplexπ_assoc]
  -- Align `(TopPair.ofSubset (KW n)ᶜ).fst` with `W` via `trans`.
  trans locallyFiniteChainComplexCoefficientMap ((pullbackCompIso i.hom j.hom).hom.app L) ≫
      (TopPair.ofSubset (KW n)ᶜ).locallyFiniteChainComplexToRelative
        ((pullback i.hom).obj ((pullback j.hom).obj L))
        (KW.isCompact n).compl_range_ofSubset_compl_map ≫
      TopPair.twistedChainComplexMap (injectivePairMap hi (KW n)) ((pullback j.hom).obj L) ≫
      φ.app (op n)
  · exact congrArg (_ ≫ ·) (Category.assoc _ _ _)
  trans (TopPair.ofSubset (KW n)ᶜ).locallyFiniteChainComplexToRelative
        ((pullback (i ≫ j).hom).obj L) (KW.isCompact n).compl_range_ofSubset_compl_map ≫
      (TopPair.ofSubset (KW n)ᶜ).twistedChainComplexCoefficientMap
        ((pullbackCompIso i.hom j.hom).hom.app L) ≫
      TopPair.twistedChainComplexMap (injectivePairMap hi (KW n)) ((pullback j.hom).obj L) ≫
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
  have := quasiIso_locallyFiniteChainComplexToLimComplexOfInjective L KW (hj.comp hi) hKW_X
  have h3 := comp_right_square (i := i) (j := j) L hi.injective hj.injective
    (hj.comp hi).injective KW
  refine ⟨fun k ↦ ?_⟩
  have hcompIso : IsIso (borelMooreHomologyCoefficientMap
        ((pullbackCompIso i.hom j.hom).hom.app L) k ≫
      HomologicalComplex.homologyMap
        (locallyFiniteChainComplexToLimComplexOfInjective ((pullback j.hom).obj L) KW
            hi.injective ≫
          ComplexTower.limComplexMap
            (compTowerExcisionJ (i := i) (j := j) L hj.injective KW)) k) := by
    rw [← HomologicalComplex.homologyMap_comp, h3]
    infer_instance
  exact (quasiIsoAt_iff_isIso_homologyMap _ k).2 <| IsIso.of_isIso_comp_left
    (borelMooreHomologyCoefficientMap ((pullbackCompIso i.hom j.hom).hom.app L) k)
    (HomologicalComplex.homologyMap
      (locallyFiniteChainComplexToLimComplexOfInjective ((pullback j.hom).obj L) KW hi.injective ≫
        ComplexTower.limComplexMap (compTowerExcisionJ (i := i) (j := j) L hj.injective KW)) k)

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
      borelMooreHomologyRestrictOfExhaustion L (j := i ≫ j) (hj.comp hi) KW hKW_X k ≫
        borelMooreHomologyCoefficientMap ((pullbackCompIso i.hom j.hom).hom.app L) k := by
  -- Enlarge `KV` to `KV' := KV.unionImage KW` so `i '' KW n ⊆ KV' n` for every `n`, then cancel
  -- the quasi-isomorphism `locallyFiniteChainComplexToLimComplexOfInjective … ≫ limComplexMap`
  -- on the right and chase the three commuting squares (`comp_middle_square`,
  -- `locallyFiniteChainComplexToLimComplex_comp_limComplexMap`, and `comp_right_square`).
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
          borelMooreHomologyRestrictOfExhaustion ((pullback j.hom).obj L) hi KW hKW_V k) ≫
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
      ((CompactExhaustion.choice V).closure_image_subset_range j.hom.continuous) k,
    borelMooreHomologyRestrict_eq_ofExhaustion j hj L (CompactExhaustion.choice V)
      ((CompactExhaustion.choice V).closure_image_subset_range j.hom.continuous) k]
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
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.hom_inv_id, ModuleCat.hom_id,
      LinearMap.id_apply]
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
  have : Mono j := (TopCat.mono_iff_injective j).2 hj
  have hcore : (twistedChainComplexMap j L).f 0 ≫
      twistedChainComplexCoeff L (TopCat.toSSetObj₀Equiv.symm (j.hom v)) =
      twistedChainComplexCoeff ((pullback j.hom).obj L) (TopCat.toSSetObj₀Equiv.symm v) := by
    have heq : twistedChainComplexCoeff L (TopCat.toSSetObj₀Equiv.symm (j.hom v)) ≍
        twistedChainComplexCoeff L
          ((TopCat.toSSet.map j).app (op ⦋0⦌) (TopCat.toSSetObj₀Equiv.symm v)) := by
      rw [TauCeti.TopCat.toSSet_map_app_toSSetObj₀Equiv_symm j v]
    rw [eq_of_heq heq]
    exact twistedChainComplexMap_f_comp_twistedChainComplexCoeff j L (TopCat.toSSetObj₀Equiv.symm v)
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
    -- `(TopPair.ofSubset _).fst` is only definitionally `V`/`X`, so `trans` aligns ambient types.
    trans ((twistedChainComplexMap j L).f 0 ≫
        ((TopPair.ofSubset (j.hom '' S)ᶜ).twistedChainComplexπ L).f 0) ≫
        (TopPair.ofSubset (j.hom '' S)ᶜ).twistedChainComplexCoeff L
          (TopCat.toSSetObj₀Equiv.symm (j.hom v)) hρ
    · exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hπ0)
    trans (twistedChainComplexMap j L).f 0 ≫
        twistedChainComplexCoeff L (TopCat.toSSetObj₀Equiv.symm (j.hom v))
    · exact (Category.assoc _ _ _).trans <| congrArg (_ ≫ ·)
        ((TopPair.ofSubset (j.hom '' S)ᶜ).twistedChainComplexπ_f_twistedChainComplexCoeff
          L _ hρ)
    · exact hcore.trans
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
  -- `(TopPair.ofSubset S).fst` is definitionally `X`, so `a` has type `L.twistedChainComplex.X 1`.
  let a' : L.twistedChainComplex.X 1 := a
  have h0 : (L.twistedChainComplex.d 1 0).hom a' = 0 := by
    rw [twistedChainComplex_d_one_zero_eq_zero L, ModuleCat.hom_zero, LinearMap.zero_apply]
  exact (congrArg (fun f ↦ f.hom a)
    (((TopPair.ofSubset S).twistedChainComplexπ L).comm 1 0)).trans <|
    (congrArg (((TopPair.ofSubset S).twistedChainComplexπ L).f 0).hom h0).trans (map_zero _)

private lemma borelMooreHomologyRestrict_zero_comp_locallyFiniteChainComplexToRelative
    {V X : TopCat.{v}} [T2Space X] [WeaklyLocallyCompactSpace V] [SigmaCompactSpace V]
    (j : V ⟶ X) (hj : IsOpenEmbedding j.hom)
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
  set K := CompactExhaustion.choice V
  rw [borelMooreHomologyRestrict_eq_ofExhaustion j hj L K
    (K.closure_image_subset_range j.hom.continuous) 0]
  have hres :=
    borelMooreHomologyRestrictOfExhaustion_comp_locallyFiniteChainComplexToLimComplexOfInjective
      L hj K (K.closure_image_subset_range j.hom.continuous) 0
  -- Align `(relativeChainComplexTower …).obj (op n)` with
  -- `(TopPair.ofSubset _).twistedChainComplex` via `trans`.
  trans (borelMooreHomologyRestrictOfExhaustion L hj K
          (K.closure_image_subset_range j.hom.continuous) 0 ≫
        HomologicalComplex.homologyMap
          (locallyFiniteChainComplexToLimComplexOfInjective L K hj.injective) 0) ≫
      HomologicalComplex.homologyMap
        ((relativeChainComplexTower L (fun m ↦ j.hom '' K m)
          (fun m ↦ Set.image_mono (K.subset_succ m))).limComplexπ n) 0
  · have hπ : HomologicalComplex.homologyMap
        ((TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative
            ((pullback j.hom).obj L)
            (K.isCompact n).compl_range_ofSubset_compl_map ≫
          TopPair.twistedChainComplexMap (injectivePairMap hj.injective (K n)) L) 0 =
        HomologicalComplex.homologyMap
          (locallyFiniteChainComplexToLimComplexOfInjective L K hj.injective) 0 ≫
        HomologicalComplex.homologyMap
          ((relativeChainComplexTower L (fun m ↦ j.hom '' K m)
            (fun m ↦ Set.image_mono (K.subset_succ m))).limComplexπ n) 0 := by
      rw [← HomologicalComplex.homologyMap_comp,
        locallyFiniteChainComplexToLimComplexOfInjective_comp_limComplexπ]
      rfl
    exact (congrArg (_ ≫ ·) hπ).trans (Category.assoc _ _ _).symm
  · exact (congrArg (· ≫ _) hres).trans <|
      (HomologicalComplex.homologyMap_comp _ _ 0).symm.trans <|
        congrArg (fun φ ↦ HomologicalComplex.homologyMap φ 0)
          (locallyFiniteChainComplexToLimComplex_comp_limComplexπ L (fun m ↦ j.hom '' K m)
            (fun m ↦ Set.image_mono (K.subset_succ m))
            (fun m ↦ (K.isCompact m).image j.hom.continuous) n)

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
  -- Pick a stage `n` of `CompactExhaustion.choice V` containing `v`. Since `X` is discrete, the
  -- differential `d 1 0` of `C(X, X \ j '' K n; L)` vanishes, so evaluating the coefficient on the
  -- 0-simplex `j v` descends to degree-0 relative homology (`eval`). Applying `eval` to both sides
  -- of `borelMooreHomologyRestrict_zero_comp_locallyFiniteChainComplexToRelative` recovers the
  -- `v`-coordinate of the restricted class on the left and the `(j v)`-coordinate of `x` on the
  -- right.
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
  have hzigH := borelMooreHomologyRestrict_zero_comp_locallyFiniteChainComplexToRelative j hj L n
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
      (borelMooreHomologyZeroIsoPi L).hom.hom x n.val :=
  borelMooreHomologyRestrict_zero_comp_isoPi
    (TopCat.ofHom (ContinuousMap.subtypeVal (Set.ofPred Even)))
    (isOpen_discrete _).isOpenEmbedding_subtypeVal L x n

end DiscreteCheck

end TauCeti.LocalCoefficientSystem
