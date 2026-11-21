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

-- Uses `TopPair.ofHom` rather than `TopPair.ofSubsetMap` because `TopPair.ofSubsetMap` is not
-- `@[expose]` in `TopPair.lean`, so across `module` boundaries `Hom.fst (TopPair.ofSubsetMap …)`
-- is not definitionally `f'`.
private abbrev preimagePairMap (hf' : IsProperMap f'.hom) (K : CompactExhaustion V) (n : ℕ) :
    TopPair.ofSubset (K.preimage hf' n)ᶜ ⟶ TopPair.ofSubset (K n)ᶜ :=
  TopPair.ofHom f'
    (TopCat.ofHom ⟨Set.MapsTo.restrict f'.hom (K.preimage hf' n)ᶜ (K n)ᶜ
        (by simp only [CompactExhaustion.preimage_apply]; exact fun _ hx ↦ hx),
      f'.hom.continuous.restrict _⟩)

-- Uses `TopPair.ofHom` rather than `TopPair.ofSubsetMap` because `TopPair.ofSubsetMap` is not
-- `@[expose]` in `TopPair.lean`, so across `module` boundaries `Hom.fst (TopPair.ofSubsetMap …)`
-- is not definitionally `f`.
private abbrev baseChangePairMap (hf' : IsProperMap f'.hom) (hj : Function.Injective j.hom)
    (hsq : i ≫ f = f' ≫ j) (hpre : Set.range i.hom = f.hom ⁻¹' Set.range j.hom)
    (K : CompactExhaustion V) (n : ℕ) :
    TopPair.ofSubset (i.hom '' K.preimage hf' n)ᶜ ⟶
      TopPair.ofSubset (j.hom '' K n)ᶜ :=
  have hmaps : Set.MapsTo f.hom (i.hom '' K.preimage hf' n)ᶜ (j.hom '' K n)ᶜ := by
    have hcomm : f.hom ∘ i.hom = j.hom ∘ f'.hom := congrArg (fun g : U ⟶ Y ↦ ⇑g.hom) hsq
    simp only [CompactExhaustion.preimage_apply,
      hj.image_preimage_eq_preimage_image hcomm hpre]
    exact fun _ hx ↦ hx
  TopPair.ofHom f (TopCat.ofHom ⟨hmaps.restrict, f.hom.continuous.restrict hmaps⟩)

private def baseChangeTowerMap (hf' : IsProperMap f'.hom) (hj : Function.Injective j.hom)
    (hsq : i ≫ f = f' ≫ j) (hpre : Set.range i.hom = f.hom ⁻¹' Set.range j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R Y) (K : CompactExhaustion V) :
    relativeChainComplexTower ((pullback f.hom).obj L) (fun n ↦ i.hom '' K.preimage hf' n)
        (fun n ↦ Set.image_mono ((K.preimage hf').subset_succ n)) ⟶
      relativeChainComplexTower L (fun n ↦ j.hom '' K n)
        (fun n ↦ Set.image_mono (K.subset_succ n)) where
  app n := TopPair.twistedChainComplexMap (baseChangePairMap hf' hj hsq hpre K n.unop) L
  naturality {m n} g := by
    apply (TopPair.ofSubset
      (i.hom '' K.preimage hf' m.unop)ᶜ).twistedChainComplex_hom_ext ((pullback f.hom).obj L)
    -- `(TopPair.ofSubset _).fst` is only definitionally `X`/`Y`, so `trans` aligns ambient types.
    trans (TopPair.ofSubset (i.hom '' K.preimage hf' n.unop)ᶜ).twistedChainComplexπ
          ((pullback f.hom).obj L) ≫
        TopPair.twistedChainComplexMap (baseChangePairMap hf' hj hsq hpre K n.unop) L
    · exact twistedChainComplexπ_comp_relativeChainComplexTower_map_assoc ((pullback f.hom).obj L)
        (fun n ↦ i.hom '' K.preimage hf' n)
        (fun n ↦ Set.image_mono ((K.preimage hf').subset_succ n)) g _
    trans twistedChainComplexMap f L ≫
        (TopPair.ofSubset (j.hom '' K n.unop)ᶜ).twistedChainComplexπ L
    · exact TopPair.twistedChainComplexπ_comp_twistedChainComplexMap
        (baseChangePairMap hf' hj hsq hpre K n.unop) L
    trans twistedChainComplexMap f L ≫
        (TopPair.ofSubset (j.hom '' K m.unop)ᶜ).twistedChainComplexπ L ≫
        (relativeChainComplexTower L (fun n ↦ j.hom '' K n)
          (fun n ↦ Set.image_mono (K.subset_succ n))).map g
    · exact congrArg (_ ≫ ·)
        (twistedChainComplexπ_comp_relativeChainComplexTower_map L (fun n ↦ j.hom '' K n)
          (fun n ↦ Set.image_mono (K.subset_succ n)) g).symm
    · exact (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc
        (baseChangePairMap hf' hj hsq hpre K m.unop) L _).symm

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
  exact TopPair.locallyFiniteChainComplexMap_comp_locallyFiniteChainComplexToRelative
    (baseChangePairMap hf' hj hsq hpre K n) hf L
    (((K.preimage hf').isCompact n).image i.hom.continuous).compl_range_ofSubset_compl_map
    ((K.isCompact n).image j.hom.continuous).compl_range_ofSubset_compl_map

private lemma baseChange_right_square_level (hf' : IsProperMap f'.hom)
    (hi : Function.Injective i.hom) (hj : Function.Injective j.hom)
    (hsq : i ≫ f = f' ≫ j) (hpre : Set.range i.hom = f.hom ⁻¹' Set.range j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R Y) (K : CompactExhaustion V) (n : ℕ) :
    (TopPair.ofSubset (K.preimage hf' n)ᶜ).twistedChainComplexCoefficientMap
          (pullbackSquareIso i.hom f.hom f'.hom j.hom L (congrArg (·.hom) hsq)).hom ≫
        TopPair.twistedChainComplexMap (preimagePairMap hf' K n) ((pullback j.hom).obj L) ≫
        TopPair.twistedChainComplexMap (injectivePairMap hj (K n)) L =
      TopPair.twistedChainComplexMap (injectivePairMap hi (K.preimage hf' n))
          ((pullback f.hom).obj L) ≫
        (baseChangeTowerMap hf' hj hsq hpre L K).app (op n) := by
  let KU := K.preimage hf'
  let sqIso := pullbackSquareIso i.hom f.hom f'.hom j.hom L (congrArg (·.hom) hsq)
  apply (TopPair.ofSubset (KU n)ᶜ).twistedChainComplex_hom_ext _
  -- `(TopPair.ofSubset _).fst` is only definitionally `U`/`V`/`X`/`Y`, so `trans` aligns types.
  trans twistedChainComplexCoefficientMap sqIso.hom ≫
      (TopPair.ofSubset (KU n)ᶜ).twistedChainComplexπ
        ((pullback f'.hom).obj ((pullback j.hom).obj L)) ≫
      TopPair.twistedChainComplexMap (preimagePairMap hf' K n) ((pullback j.hom).obj L) ≫
      TopPair.twistedChainComplexMap (injectivePairMap hj (K n)) L
  · exact TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc
      (TopPair.ofSubset (KU n)ᶜ) sqIso.hom _
  trans twistedChainComplexCoefficientMap sqIso.hom ≫
      twistedChainComplexMap f' ((pullback j.hom).obj L) ≫
      (TopPair.ofSubset (K n)ᶜ).twistedChainComplexπ ((pullback j.hom).obj L) ≫
      TopPair.twistedChainComplexMap (injectivePairMap hj (K n)) L
  · exact congrArg (_ ≫ ·) (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc
      (preimagePairMap hf' K n) ((pullback j.hom).obj L) _)
  trans (twistedChainComplexCoefficientMap sqIso.hom ≫
        twistedChainComplexMap f' ((pullback j.hom).obj L) ≫
        twistedChainComplexMap j L) ≫
      (TopPair.ofSubset (j.hom '' K n)ᶜ).twistedChainComplexπ L
  · exact (congrArg (_ ≫ ·) (congrArg (_ ≫ ·)
      (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap
        (injectivePairMap hj (K n)) L))).trans <|
      (Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm
  trans (twistedChainComplexMap i ((pullback f.hom).obj L) ≫ twistedChainComplexMap f L) ≫
      (TopPair.ofSubset (j.hom '' K n)ᶜ).twistedChainComplexπ L
  · exact congrArg (· ≫ _) (twistedChainComplexMap_naturality_square i f f' j L hsq).symm
  trans twistedChainComplexMap i ((pullback f.hom).obj L) ≫
      (TopPair.ofSubset (i.hom '' KU n)ᶜ).twistedChainComplexπ ((pullback f.hom).obj L) ≫
      (baseChangeTowerMap hf' hj hsq hpre L K).app (op n)
  · exact (Category.assoc _ _ _).trans <| congrArg (_ ≫ ·)
      (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap
        (baseChangePairMap hf' hj hsq hpre K n) L).symm
  · exact (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc
      (injectivePairMap hi (KU n)) ((pullback f.hom).obj L) _).symm

private lemma baseChange_right_square (hf' : IsProperMap f'.hom)
    (hi : Function.Injective i.hom) (hj : Function.Injective j.hom)
    (hsq : i ≫ f = f' ≫ j) (hpre : Set.range i.hom = f.hom ⁻¹' Set.range j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R Y) (K : CompactExhaustion V) :
    locallyFiniteChainComplexCoefficientMap
          (pullbackSquareIso i.hom f.hom f'.hom j.hom L (congrArg (·.hom) hsq)).hom ≫
        locallyFiniteChainComplexMap f' hf' ((pullback j.hom).obj L) ≫
          locallyFiniteChainComplexToLimComplexOfInjective L K hj =
      locallyFiniteChainComplexToLimComplexOfInjective ((pullback f.hom).obj L)
          (K.preimage hf') hi ≫
        ComplexTower.limComplexMap (baseChangeTowerMap hf' hj hsq hpre L K) := by
  let KU := K.preimage hf'
  let sqIso := pullbackSquareIso i.hom f.hom f'.hom j.hom L (congrArg (·.hom) hsq)
  apply (relativeChainComplexTower L (fun n ↦ j.hom '' K n)
    (fun n ↦ Set.image_mono (K.subset_succ n))).isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  simp only [ComplexTower.limComplexCone_π_app, Category.assoc,
    ComplexTower.limComplexMap_comp_π,
    locallyFiniteChainComplexToLimComplexOfInjective_comp_limComplexπ,
    locallyFiniteChainComplexToLimComplexOfInjective_comp_limComplexπ_assoc]
  -- `(TopPair.ofSubset _).fst` is only definitionally `U`/`V`/`X`/`Y`, so `trans` aligns types.
  trans locallyFiniteChainComplexCoefficientMap sqIso.hom ≫
      (TopPair.ofSubset (KU n)ᶜ).locallyFiniteChainComplexToRelative
        ((pullback f'.hom).obj ((pullback j.hom).obj L))
        (KU.isCompact n).compl_range_ofSubset_compl_map ≫
      TopPair.twistedChainComplexMap (preimagePairMap hf' K n) ((pullback j.hom).obj L) ≫
      TopPair.twistedChainComplexMap (injectivePairMap hj (K n)) L
  · exact congrArg (_ ≫ ·)
      (TopPair.locallyFiniteChainComplexMap_comp_locallyFiniteChainComplexToRelative_assoc
        (preimagePairMap hf' K n) hf' ((pullback j.hom).obj L) _ _ _)
  trans (TopPair.ofSubset (KU n)ᶜ).locallyFiniteChainComplexToRelative
        ((pullback i.hom).obj ((pullback f.hom).obj L))
        (KU.isCompact n).compl_range_ofSubset_compl_map ≫
      (TopPair.ofSubset (KU n)ᶜ).twistedChainComplexCoefficientMap sqIso.hom ≫
      TopPair.twistedChainComplexMap (preimagePairMap hf' K n) ((pullback j.hom).obj L) ≫
      TopPair.twistedChainComplexMap (injectivePairMap hj (K n)) L
  · exact
      TopPair.locallyFiniteChainComplexCoefficientMap_comp_locallyFiniteChainComplexToRelative_assoc
        (TopPair.ofSubset (KU n)ᶜ) sqIso.hom _ _
  · exact congrArg (_ ≫ ·) (baseChange_right_square_level hf' hi hj hsq hpre L K n)

end Helpers

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
    (hK : ∀ n, closure (j.hom '' K n) ⊆ Set.range j.hom)
    (hKU : ∀ n, closure (i.hom '' KU n) ⊆ Set.range i.hom) (k : ℕ) :
    borelMooreHomologyMap f hf L k ≫ borelMooreHomologyRestrictOfExhaustion L hj K hK k =
      borelMooreHomologyRestrictOfExhaustion ((pullback f.hom).obj L) hi KU hKU k ≫
        borelMooreHomologyCoefficientMap
          (pullbackSquareIso i.hom f.hom f'.hom j.hom L (congrArg (·.hom) hsq)).hom k ≫
        borelMooreHomologyMap f'
          (hf.of_isEmbedding_of_range_eq hi.isEmbedding hj.isEmbedding
            (congrArg (fun g : U ⟶ Y ↦ ⇑g.hom) hsq) hpre)
          ((pullback j.hom).obj L) k := by
  have hcomm : f.hom ∘ i.hom = j.hom ∘ f'.hom := congrArg (fun g : U ⟶ Y ↦ ⇑g.hom) hsq
  have hf' : IsProperMap f'.hom :=
    hf.of_isEmbedding_of_range_eq hi.isEmbedding hj.isEmbedding hcomm hpre
  let KU' := K.preimage hf'
  have hKU' (n : ℕ) : closure (i.hom '' KU' n) ⊆ Set.range i.hom := by
    simp only [KU', CompactExhaustion.preimage_apply,
      hj.injective.image_preimage_eq_preimage_image hcomm hpre, hpre]
    exact (f.hom.continuous.closure_preimage_subset _).trans (Set.preimage_mono (hK n))
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
          (pullbackSquareIso i.hom f.hom f'.hom j.hom L (congrArg (·.hom) hsq)).hom k ≫
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
    hf hi hj hsq hpre L (CompactExhaustion.choice V) (CompactExhaustion.choice U) hKV hKU k

end TauCeti.LocalCoefficientSystem
