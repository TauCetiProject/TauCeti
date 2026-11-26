/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Restriction.Basic
public import TauCeti.Topology.Maps.Proper.Basic
import TauCeti.Data.Set.Image
import TauCeti.Topology.Compactness.SigmaCompact

/-!
# Proper-map base change for Borel–Moore open restriction

For a Cartesian square of topological spaces

```
U --i--> X
|        |
f'       f
v        v
V --j--> Y
```

in which `f` is a proper map and `i` and `j` are open embeddings satisfying
`Set.range i = f⁻¹(Set.range j)` (so `f'` is automatically proper by
`IsProperMap.of_isEmbedding_of_range_eq`), pushing forward along `f` and restricting to `V` agrees
on Borel–Moore homology with restricting to `U`, changing local coefficients across the commuting
square via `pullbackSquareIso`, and pushing forward along `f'`.

Given a compact exhaustion `K` of `V`, pulling it back along the proper map `f'` produces a
compact exhaustion `K.preimage hf'` of `U` satisfying `i '' (f'⁻¹(Kₙ)) = f⁻¹(j '' Kₙ)`. Thus
`f` induces a levelwise map of ambient relative towers `(X, X \ i '' f'⁻¹(Kₙ)) ⟶ (Y, Y \ j '' Kₙ)`
fitting into a commuting ladder between the open-restriction zigzags for `i` and `j`. Exhaustion
independence of open restriction (`borelMooreHomologyRestrictOfExhaustion_eq`) then gives the
result for arbitrary exhaustions of `U` and `V`, and specializing to `CompactExhaustion.choice`
gives the canonical version for Hausdorff targets.

## Main declarations

* `TauCeti.LocalCoefficientSystem.borelMooreHomologyMap_comp_borelMooreHomologyRestrictOfExhaustion`
  : proper-map base change for exhaustion-explicit open restriction.
* `TauCeti.LocalCoefficientSystem.borelMooreHomologyMap_comp_borelMooreHomologyRestrict`:
  proper-map base change for canonical open restriction.

## References

* A. Borel and J. C. Moore, *Homology theory for locally compact spaces*, Michigan Math. J. 7
  (1960), 137–159.
* G. E. Bredon, *Sheaf Theory*, 2nd ed., Graduate Texts in Mathematics 170, Chapter V.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Topology

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R]

section Helpers

variable {U V X Y : TopCat.{v}} {f : X ⟶ Y} {f' : U ⟶ V} {i : U ⟶ X} {j : V ⟶ Y}

private lemma preimage_mapsTo_compl (hf' : IsProperMap f'.hom) (K : CompactExhaustion V) (n : ℕ) :
    Set.MapsTo f'.hom (K.preimage hf' n)ᶜ (K n)ᶜ := by
  rw [CompactExhaustion.preimage_apply]
  exact Set.mapsTo_preimage f'.hom (K n)ᶜ

private lemma baseChange_mapsTo_compl (hf' : IsProperMap f'.hom) (hj : Function.Injective j.hom)
    (hsq : i ≫ f = f' ≫ j) (hpre : Set.range i.hom = f.hom ⁻¹' Set.range j.hom)
    (K : CompactExhaustion V) (n : ℕ) :
    Set.MapsTo f.hom (i.hom '' K.preimage hf' n)ᶜ (j.hom '' K n)ᶜ := by
  have hcomm : f.hom ∘ i.hom = j.hom ∘ f'.hom := congrArg (fun g : U ⟶ Y ↦ ⇑g.hom) hsq
  simp only [CompactExhaustion.preimage_apply,
    hj.image_preimage_eq_preimage_image hcomm hpre]
  exact Set.mapsTo_preimage f.hom (j.hom '' K n)ᶜ

private def baseChangeTowerMap (hf' : IsProperMap f'.hom) (hj : Function.Injective j.hom)
    (hsq : i ≫ f = f' ≫ j) (hpre : Set.range i.hom = f.hom ⁻¹' Set.range j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R Y) (K : CompactExhaustion V) :
    relativeChainComplexTower ((pullback f.hom).obj L) (fun n ↦ i.hom '' K.preimage hf' n)
        (fun n ↦ Set.image_mono ((K.preimage hf').subset_succ n)) ⟶
      relativeChainComplexTower L (fun n ↦ j.hom '' K n)
        (fun n ↦ Set.image_mono (K.subset_succ n)) :=
  relativeChainComplexTowerHomMk (fun n ↦ Set.image_mono ((K.preimage hf').subset_succ n))
    (fun n ↦ Set.image_mono (K.subset_succ n)) (twistedChainComplexMap f L)
    (fun n ↦ TopPair.twistedChainComplexMapOfFstEq
      (TopPair.ofSubsetMap f (baseChange_mapsTo_compl hf' hj hsq hpre K n))
      (TopPair.ofSubsetMap_fst _ _) L)
    fun n ↦ TopPair.twistedChainComplexπ_comp_twistedChainComplexMapOfFstEq
      (TopPair.ofSubsetMap f (baseChange_mapsTo_compl hf' hj hsq hpre K n))
      (TopPair.ofSubsetMap_fst _ _) L

@[simp]
private lemma baseChangeTowerMap_app (hf' : IsProperMap f'.hom) (hj : Function.Injective j.hom)
    (hsq : i ≫ f = f' ≫ j) (hpre : Set.range i.hom = f.hom ⁻¹' Set.range j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R Y) (K : CompactExhaustion V) (n : ℕ) :
    (baseChangeTowerMap hf' hj hsq hpre L K).app (op n) =
      TopPair.twistedChainComplexMapOfFstEq
        (TopPair.ofSubsetMap f (baseChange_mapsTo_compl hf' hj hsq hpre K n))
        (TopPair.ofSubsetMap_fst _ _) L :=
  relativeChainComplexTowerHomMk_app _ _ _ _ _ n

private lemma baseChange_left_square (hf : IsProperMap f.hom) (hf' : IsProperMap f'.hom)
    (hj : Function.Injective j.hom) (hsq : i ≫ f = f' ≫ j)
    (hpre : Set.range i.hom = f.hom ⁻¹' Set.range j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R Y) (K : CompactExhaustion V) :
    locallyFiniteChainComplexMap f hf L ≫
        locallyFiniteChainComplexToLimComplex L (fun n ↦ j.hom '' K n)
          (fun n ↦ Set.image_mono (K.subset_succ n))
          (fun n ↦ (K.isCompact n).image j.hom.continuous) =
      locallyFiniteChainComplexToLimComplex ((pullback f.hom).obj L)
          (fun n ↦ i.hom '' K.preimage hf' n)
          (fun n ↦ Set.image_mono ((K.preimage hf').subset_succ n))
          (fun n ↦ ((K.preimage hf').isCompact n).image i.hom.continuous) ≫
        ComplexTower.limComplexMap (baseChangeTowerMap hf' hj hsq hpre L K) := by
  apply (relativeChainComplexTower L (fun n ↦ j.hom '' K n)
    (fun n ↦ Set.image_mono (K.subset_succ n))).isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  simp only [ComplexTower.limComplexCone_π_app, Category.assoc,
    ComplexTower.limComplexMap_comp_π,
    locallyFiniteChainComplexToLimComplex_comp_limComplexπ,
    locallyFiniteChainComplexToLimComplex_comp_limComplexπ_assoc]
  rw [baseChangeTowerMap_app]
  exact TopPair.locallyFiniteChainComplexMap_comp_locallyFiniteChainComplexToRelative_ofFstEq
    (TopPair.ofSubsetMap f (baseChange_mapsTo_compl hf' hj hsq hpre K n))
    (TopPair.ofSubsetMap_fst _ _) hf L
    (((K.preimage hf').isCompact n).image i.hom.continuous).compl_range_ofSubset_compl_map
    ((K.isCompact n).image j.hom.continuous).compl_range_ofSubset_compl_map

private lemma baseChange_right_square_level (hf' : IsProperMap f'.hom)
    (hi : Function.Injective i.hom) (hj : Function.Injective j.hom)
    (hsq : i ≫ f = f' ≫ j) (hpre : Set.range i.hom = f.hom ⁻¹' Set.range j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R Y) (K : CompactExhaustion V) (n : ℕ) :
    (TopPair.ofSubset (K.preimage hf' n)ᶜ).twistedChainComplexCoefficientMap
          ((pullbackSquareIso i.hom f.hom f'.hom j.hom (congrArg (·.hom) hsq)).hom.app L) ≫
        TopPair.twistedChainComplexMapOfFstEq
          (TopPair.ofSubsetMap f' (preimage_mapsTo_compl hf' K n))
          (TopPair.ofSubsetMap_fst _ _) ((pullback j.hom).obj L) ≫
        TopPair.twistedChainComplexMapOfFstEq (TopPair.ofSubsetMap j
          (Set.SurjOn.mapsTo_compl (Set.surjOn_image j.hom (K n)) hj))
          (TopPair.ofSubsetMap_fst _ _) L =
      TopPair.twistedChainComplexMapOfFstEq (TopPair.ofSubsetMap i
          (Set.SurjOn.mapsTo_compl (Set.surjOn_image i.hom (K.preimage hf' n)) hi))
          (TopPair.ofSubsetMap_fst _ _) ((pullback f.hom).obj L) ≫
        (baseChangeTowerMap hf' hj hsq hpre L K).app (op n) := by
  let KU := K.preimage hf'
  let sqIso := (pullbackSquareIso i.hom f.hom f'.hom j.hom (congrArg (·.hom) hsq)).hom.app L
  let pf' := TopPair.ofSubsetMap f' (preimage_mapsTo_compl hf' K n)
  let pj := TopPair.ofSubsetMap j (Set.SurjOn.mapsTo_compl (Set.surjOn_image j.hom (K n)) hj)
  let pi := TopPair.ofSubsetMap i (Set.SurjOn.mapsTo_compl (Set.surjOn_image i.hom (KU n)) hi)
  let pf := TopPair.ofSubsetMap f (baseChange_mapsTo_compl hf' hj hsq hpre K n)
  apply (TopPair.ofSubset (KU n)ᶜ).twistedChainComplex_hom_ext _
  -- `(TopPair.ofSubset _).fst` is only definitionally `U`/`V`/`X`/`Y`, so `trans` aligns types.
  trans twistedChainComplexCoefficientMap sqIso ≫
      (TopPair.ofSubset (KU n)ᶜ).twistedChainComplexπ
        ((pullback f'.hom).obj ((pullback j.hom).obj L)) ≫
      TopPair.twistedChainComplexMapOfFstEq pf' (TopPair.ofSubsetMap_fst _ _)
        ((pullback j.hom).obj L) ≫
      TopPair.twistedChainComplexMapOfFstEq pj (TopPair.ofSubsetMap_fst _ _) L
  · exact TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc
      (TopPair.ofSubset (KU n)ᶜ) sqIso _
  trans twistedChainComplexCoefficientMap sqIso ≫
      twistedChainComplexMap f' ((pullback j.hom).obj L) ≫
      (TopPair.ofSubset (K n)ᶜ).twistedChainComplexπ ((pullback j.hom).obj L) ≫
      TopPair.twistedChainComplexMapOfFstEq pj (TopPair.ofSubsetMap_fst _ _) L
  · exact congrArg (_ ≫ ·) (TopPair.twistedChainComplexπ_comp_twistedChainComplexMapOfFstEq_assoc
      pf' (TopPair.ofSubsetMap_fst _ _) ((pullback j.hom).obj L) _)
  trans (twistedChainComplexCoefficientMap sqIso ≫
        twistedChainComplexMap f' ((pullback j.hom).obj L) ≫
        twistedChainComplexMap j L) ≫
      (TopPair.ofSubset (j.hom '' K n)ᶜ).twistedChainComplexπ L
  · exact (congrArg (_ ≫ ·) (congrArg (_ ≫ ·)
      (TopPair.twistedChainComplexπ_comp_twistedChainComplexMapOfFstEq pj
        (TopPair.ofSubsetMap_fst _ _) L))).trans <|
      (Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm
  trans (twistedChainComplexMap i ((pullback f.hom).obj L) ≫ twistedChainComplexMap f L) ≫
      (TopPair.ofSubset (j.hom '' K n)ᶜ).twistedChainComplexπ L
  · exact congrArg (· ≫ _) (twistedChainComplexMap_naturality_square i f f' j L hsq).symm
  trans twistedChainComplexMap i ((pullback f.hom).obj L) ≫
      (TopPair.ofSubset (i.hom '' KU n)ᶜ).twistedChainComplexπ ((pullback f.hom).obj L) ≫
      (baseChangeTowerMap hf' hj hsq hpre L K).app (op n)
  · rw [baseChangeTowerMap_app]
    exact (Category.assoc _ _ _).trans <| congrArg (_ ≫ ·)
      (TopPair.twistedChainComplexπ_comp_twistedChainComplexMapOfFstEq pf
        (TopPair.ofSubsetMap_fst _ _) L).symm
  · exact (TopPair.twistedChainComplexπ_comp_twistedChainComplexMapOfFstEq_assoc
      pi (TopPair.ofSubsetMap_fst _ _) ((pullback f.hom).obj L) _).symm

private lemma baseChange_right_square (hf' : IsProperMap f'.hom)
    (hi : Function.Injective i.hom) (hj : Function.Injective j.hom)
    (hsq : i ≫ f = f' ≫ j) (hpre : Set.range i.hom = f.hom ⁻¹' Set.range j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R Y) (K : CompactExhaustion V) :
    locallyFiniteChainComplexCoefficientMap
          ((pullbackSquareIso i.hom f.hom f'.hom j.hom (congrArg (·.hom) hsq)).hom.app L) ≫
        locallyFiniteChainComplexMap f' hf' ((pullback j.hom).obj L) ≫
          locallyFiniteChainComplexToLimComplexOfInjective L K hj =
      locallyFiniteChainComplexToLimComplexOfInjective ((pullback f.hom).obj L)
          (K.preimage hf') hi ≫
        ComplexTower.limComplexMap (baseChangeTowerMap hf' hj hsq hpre L K) := by
  let KU := K.preimage hf'
  let sqIso := (pullbackSquareIso i.hom f.hom f'.hom j.hom (congrArg (·.hom) hsq)).hom.app L
  apply (relativeChainComplexTower L (fun n ↦ j.hom '' K n)
    (fun n ↦ Set.image_mono (K.subset_succ n))).isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  simp only [ComplexTower.limComplexCone_π_app, Category.assoc,
    ComplexTower.limComplexMap_comp_π,
    locallyFiniteChainComplexToLimComplexOfInjective_comp_limComplexπ,
    locallyFiniteChainComplexToLimComplexOfInjective_comp_limComplexπ_assoc]
  -- `(TopPair.ofSubset _).fst` is only definitionally `U`/`V`/`X`/`Y`, so `trans` aligns types.
  trans locallyFiniteChainComplexCoefficientMap sqIso ≫
      (TopPair.ofSubset (KU n)ᶜ).locallyFiniteChainComplexToRelative
        ((pullback f'.hom).obj ((pullback j.hom).obj L))
        (KU.isCompact n).compl_range_ofSubset_compl_map ≫
      TopPair.twistedChainComplexMapOfFstEq
        (TopPair.ofSubsetMap f' (preimage_mapsTo_compl hf' K n))
        (TopPair.ofSubsetMap_fst _ _) ((pullback j.hom).obj L) ≫
      TopPair.twistedChainComplexMapOfFstEq (TopPair.ofSubsetMap j
        (Set.SurjOn.mapsTo_compl (Set.surjOn_image j.hom (K n)) hj))
        (TopPair.ofSubsetMap_fst _ _) L
  · exact congrArg (_ ≫ ·)
      (TopPair.locallyFiniteChainComplexMap_comp_locallyFiniteChainComplexToRelative_ofFstEq_assoc
        (TopPair.ofSubsetMap f' (preimage_mapsTo_compl hf' K n))
        (TopPair.ofSubsetMap_fst _ _) hf' ((pullback j.hom).obj L) _ _ _)
  trans (TopPair.ofSubset (KU n)ᶜ).locallyFiniteChainComplexToRelative
        ((pullback i.hom).obj ((pullback f.hom).obj L))
        (KU.isCompact n).compl_range_ofSubset_compl_map ≫
      (TopPair.ofSubset (KU n)ᶜ).twistedChainComplexCoefficientMap sqIso ≫
      TopPair.twistedChainComplexMapOfFstEq
        (TopPair.ofSubsetMap f' (preimage_mapsTo_compl hf' K n))
        (TopPair.ofSubsetMap_fst _ _) ((pullback j.hom).obj L) ≫
      TopPair.twistedChainComplexMapOfFstEq (TopPair.ofSubsetMap j
        (Set.SurjOn.mapsTo_compl (Set.surjOn_image j.hom (K n)) hj))
        (TopPair.ofSubsetMap_fst _ _) L
  · exact
      TopPair.locallyFiniteChainComplexCoefficientMap_comp_locallyFiniteChainComplexToRelative_assoc
        (TopPair.ofSubset (KU n)ᶜ) sqIso _ _
  · exact congrArg (_ ≫ ·) (baseChange_right_square_level hf' hi hj hsq hpre L K n)

end Helpers

/-- In a Cartesian square `i ≫ f = f' ≫ j` with `f` proper and `i, j` open embeddings, any
compact exhaustion `KU` of `U` satisfies the closure condition `closure (i '' KU n) ⊆ Set.range i`
whenever a compact exhaustion `K` of `V` satisfies `closure (j '' K n) ⊆ Set.range j`. -/
lemma closure_image_subset_range_of_cartesian {U V X Y : TopCat.{v}}
    {f : X ⟶ Y} {f' : U ⟶ V} {i : U ⟶ X} {j : V ⟶ Y}
    (hf : IsProperMap f.hom) (hi : IsOpenEmbedding i.hom) (hj : IsOpenEmbedding j.hom)
    (hsq : i ≫ f = f' ≫ j) (hpre : Set.range i.hom = f.hom ⁻¹' Set.range j.hom)
    (K : CompactExhaustion V) (KU : CompactExhaustion U)
    (hK : ∀ n, closure (j.hom '' K n) ⊆ Set.range j.hom) (n : ℕ) :
    closure (i.hom '' KU n) ⊆ Set.range i.hom := by
  have hcomm : f.hom ∘ i.hom = j.hom ∘ f'.hom := congrArg (fun g : U ⟶ Y ↦ ⇑g.hom) hsq
  have hf' : IsProperMap f'.hom :=
    hf.of_isEmbedding_of_range_eq hi.isEmbedding hj.isEmbedding hcomm hpre
  obtain ⟨N, hN⟩ := (K.preimage hf').exists_superset_of_isCompact (KU.isCompact n)
  refine (closure_mono (Set.image_mono hN)).trans ?_
  simp only [CompactExhaustion.preimage_apply,
    hj.injective.image_preimage_eq_preimage_image hcomm hpre, hpre]
  exact (f.hom.continuous.closure_preimage_subset _).trans (Set.preimage_mono (hK N))

/-- **Proper-map base change for exhaustion-explicit open restriction.** For a Cartesian square
`i ≫ f = f' ≫ j` with `f` proper and `i, j` open embeddings (`range i = f⁻¹(range j)`), the
pulled-back map `f'` is automatically proper by `IsProperMap.of_isEmbedding_of_range_eq`, and
pushing forward along `f` and restricting along `j` agrees with restricting along `i`, changing
coefficients across the square via `pullbackSquareIso`, and pushing forward along `f'`. -/
@[reassoc]
theorem borelMooreHomologyMap_comp_borelMooreHomologyRestrictOfExhaustion
    {U V X Y : TopCat.{v}} {f : X ⟶ Y} {f' : U ⟶ V} {i : U ⟶ X} {j : V ⟶ Y}
    (hf : IsProperMap f.hom) (hi : IsOpenEmbedding i.hom) (hj : IsOpenEmbedding j.hom)
    (hsq : i ≫ f = f' ≫ j) (hpre : Set.range i.hom = f.hom ⁻¹' Set.range j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R Y)
    (K : CompactExhaustion V) (KU : CompactExhaustion U)
    (hK : ∀ n, closure (j.hom '' K n) ⊆ Set.range j.hom) (k : ℕ) :
    borelMooreHomologyMap f hf L k ≫ borelMooreHomologyRestrictOfExhaustion L hj K hK k =
      borelMooreHomologyRestrictOfExhaustion ((pullback f.hom).obj L) hi KU
          (closure_image_subset_range_of_cartesian hf hi hj hsq hpre K KU hK) k ≫
        borelMooreHomologyCoefficientMap
          ((pullbackSquareIso i.hom f.hom f'.hom j.hom (congrArg (·.hom) hsq)).hom.app L) k ≫
        borelMooreHomologyMap f'
          (hf.of_isEmbedding_of_range_eq hi.isEmbedding hj.isEmbedding
            (congrArg (fun g : U ⟶ Y ↦ ⇑g.hom) hsq) hpre)
          ((pullback j.hom).obj L) k := by
  have hcomm : f.hom ∘ i.hom = j.hom ∘ f'.hom := congrArg (fun g : U ⟶ Y ↦ ⇑g.hom) hsq
  have hf' : IsProperMap f'.hom :=
    hf.of_isEmbedding_of_range_eq hi.isEmbedding hj.isEmbedding hcomm hpre
  have hKU := closure_image_subset_range_of_cartesian hf hi hj hsq hpre K KU hK
  let KU' := K.preimage hf'
  have hKU' := closure_image_subset_range_of_cartesian hf hi hj hsq hpre K KU' hK
  rw [borelMooreHomologyRestrictOfExhaustion_eq ((pullback f.hom).obj L) hi KU KU' hKU hKU' k]
  have := quasiIso_locallyFiniteChainComplexToLimComplexOfInjective L K hj hK
  have hrK :=
    borelMooreHomologyRestrictOfExhaustion_comp_locallyFiniteChainComplexToLimComplexOfInjective
      L hj K hK k
  have hrKU' :=
    borelMooreHomologyRestrictOfExhaustion_comp_locallyFiniteChainComplexToLimComplexOfInjective
      ((pullback f.hom).obj L) hi KU' hKU' k
  rw [← cancel_mono (HomologicalComplex.homologyMap
      (locallyFiniteChainComplexToLimComplexOfInjective L K hj.injective) k),
    Category.assoc, hrK]
  calc borelMooreHomologyMap f hf L k ≫
        HomologicalComplex.homologyMap
          (locallyFiniteChainComplexToLimComplex L (fun n ↦ j.hom '' K n)
            (fun n ↦ Set.image_mono (K.subset_succ n))
            (fun n ↦ (K.isCompact n).image j.hom.continuous)) k
    _ = HomologicalComplex.homologyMap
          (locallyFiniteChainComplexToLimComplex ((pullback f.hom).obj L)
            (fun n ↦ i.hom '' KU' n) (fun n ↦ Set.image_mono (KU'.subset_succ n))
            (fun n ↦ (KU'.isCompact n).image i.hom.continuous)) k ≫
          HomologicalComplex.homologyMap
            (ComplexTower.limComplexMap (baseChangeTowerMap hf' hj.injective hsq hpre L K)) k := by
        rw [← HomologicalComplex.homologyMap_comp, baseChange_left_square,
          HomologicalComplex.homologyMap_comp]
    _ = borelMooreHomologyRestrictOfExhaustion ((pullback f.hom).obj L) hi KU' hKU' k ≫
          HomologicalComplex.homologyMap (locallyFiniteChainComplexCoefficientMap _ ≫
            locallyFiniteChainComplexMap f' hf' ((pullback j.hom).obj L) ≫
              locallyFiniteChainComplexToLimComplexOfInjective L K hj.injective) k := by
        rw [← hrKU', Category.assoc, ← HomologicalComplex.homologyMap_comp,
          ← baseChange_right_square hf' hi.injective hj.injective hsq hpre L K]
    _ = (borelMooreHomologyRestrictOfExhaustion ((pullback f.hom).obj L) hi KU' hKU' k ≫
          borelMooreHomologyCoefficientMap _ k ≫
            borelMooreHomologyMap f' hf' ((pullback j.hom).obj L) k) ≫
          HomologicalComplex.homologyMap
            (locallyFiniteChainComplexToLimComplexOfInjective L K hj.injective) k := by
        simp [HomologicalComplex.homologyMap_comp, Category.assoc]

/-- **Proper-map base change for canonical open restriction.** For a Cartesian square
`i ≫ f = f' ≫ j` with `f` proper and `i, j` open embeddings (`range i = f⁻¹(range j)`), the
pulled-back map `f'` is automatically proper by `IsProperMap.of_isEmbedding_of_range_eq`, and
pushing forward along `f` and restricting along `j` agrees with restricting along `i`, changing
coefficients across the square via `pullbackSquareIso`, and pushing forward along `f'`. -/
@[reassoc]
theorem borelMooreHomologyMap_comp_borelMooreHomologyRestrict
    {U V X Y : TopCat.{v}} [T2Space X] [T2Space Y]
    [WeaklyLocallyCompactSpace U] [SigmaCompactSpace U]
    [WeaklyLocallyCompactSpace V] [SigmaCompactSpace V]
    {f : X ⟶ Y} {f' : U ⟶ V} {i : U ⟶ X} {j : V ⟶ Y}
    (hf : IsProperMap f.hom) (hi : IsOpenEmbedding i.hom) (hj : IsOpenEmbedding j.hom)
    (hsq : i ≫ f = f' ≫ j) (hpre : Set.range i.hom = f.hom ⁻¹' Set.range j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R Y) (k : ℕ) :
    borelMooreHomologyMap f hf L k ≫ borelMooreHomologyRestrict j hj L k =
      borelMooreHomologyRestrict i hi ((pullback f.hom).obj L) k ≫
        borelMooreHomologyCoefficientMap
          ((pullbackSquareIso i.hom f.hom f'.hom j.hom (congrArg (·.hom) hsq)).hom.app L) k ≫
        borelMooreHomologyMap f'
          (hf.of_isEmbedding_of_range_eq hi.isEmbedding hj.isEmbedding
            (congrArg (fun g : U ⟶ Y ↦ ⇑g.hom) hsq) hpre)
          ((pullback j.hom).obj L) k := by
  have hKV := (CompactExhaustion.choice V).closure_image_subset_range j.hom.continuous
  have hKU := (CompactExhaustion.choice U).closure_image_subset_range i.hom.continuous
  rw [borelMooreHomologyRestrict_eq_ofExhaustion j hj L (CompactExhaustion.choice V) hKV k,
    borelMooreHomologyRestrict_eq_ofExhaustion i hi ((pullback f.hom).obj L)
      (CompactExhaustion.choice U) hKU k]
  exact borelMooreHomologyMap_comp_borelMooreHomologyRestrictOfExhaustion
    hf hi hj hsq hpre L (CompactExhaustion.choice V) (CompactExhaustion.choice U) hKV k

end TauCeti.LocalCoefficientSystem
