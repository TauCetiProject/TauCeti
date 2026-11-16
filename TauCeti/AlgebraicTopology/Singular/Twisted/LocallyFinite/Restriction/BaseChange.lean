/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Restriction.Basic

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

in which `f` and `f'` are proper maps and `i` and `j` are open embeddings satisfying
`Set.range i = f⁻¹(Set.range j)`, pushing forward along `f` and restricting to `V` agrees on
Borel–Moore homology with restricting to `U`, changing local coefficients across the commuting
square, and pushing forward along `f'`.

Given a compact exhaustion `K` of `V`, pulling it back along the proper map `f'` produces a
compact exhaustion `f'⁻¹(Kₙ)` of `U` satisfying `i '' (f'⁻¹(Kₙ)) = f⁻¹(j '' Kₙ)`. Thus `f`
induces a levelwise map of ambient relative towers `(X, X \ i '' f'⁻¹(Kₙ)) ⟶ (Y, Y \ j '' Kₙ)`
fitting into a commuting ladder between the open-restriction zigzags for `i` and `j`. Exhaustion
independence of open restriction (`borelMooreHomologyRestrictOfExhaustion_eq`) then gives the
result for arbitrary exhaustions of `U` and `V`, and specializing to `CompactExhaustion.choice`
gives the canonical version for Hausdorff targets.

## Main declarations

* `CompactExhaustion.preimage`: pullback of a compact exhaustion along a proper continuous map.
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

namespace CompactExhaustion

/-- Pulling back a compact exhaustion along a proper continuous map yields a compact exhaustion. -/
def preimage {U V : Type*} [TopologicalSpace U] [TopologicalSpace V]
    (K : CompactExhaustion V) {f : U → V} (hf : IsProperMap f) : CompactExhaustion U where
  toFun n := f ⁻¹' K n
  isCompact' n := hf.isCompact_preimage (K.isCompact n)
  subset_interior_succ' n :=
    (Set.preimage_mono (K.subset_interior_succ n)).trans
      (interior_maximal (Set.preimage_mono interior_subset)
        (isOpen_interior.preimage hf.continuous))
  iUnion_eq' := by
    rw [← Set.preimage_iUnion, K.iUnion_eq, Set.preimage_univ]

@[simp]
lemma preimage_apply {U V : Type*} [TopologicalSpace U] [TopologicalSpace V]
    (K : CompactExhaustion V) {f : U → V} (hf : IsProperMap f) (n : ℕ) :
    K.preimage hf n = f ⁻¹' K n := (rfl)

end CompactExhaustion

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R]

section Helpers

variable {U V X Y : TopCat.{v}} {f : X ⟶ Y} {f' : U ⟶ V} {i : U ⟶ X} {j : V ⟶ Y}

private lemma preimage_image_eq_of_cartesian (hj : Function.Injective j.hom)
    (hsq : i ≫ f = f' ≫ j) (hpre : Set.range i.hom = f.hom ⁻¹' Set.range j.hom)
    (S : Set V) : i.hom '' (f'.hom ⁻¹' S) = f.hom ⁻¹' (j.hom '' S) := by
  ext x
  simp only [Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨f'.hom u, hu, (congrArg (fun g : U ⟶ Y ↦ g u) hsq).symm⟩
  · rintro ⟨v, hv, hfx⟩
    have hx : x ∈ Set.range i.hom := by
      rw [hpre]
      exact ⟨v, hfx⟩
    obtain ⟨u, rfl⟩ := hx
    refine ⟨u, ?_, rfl⟩
    have hju : j.hom (f'.hom u) = j.hom v :=
      (congrArg (fun g : U ⟶ Y ↦ g u) hsq).symm.trans hfx.symm
    rwa [hj hju]

-- Uses `TopPair.ofHom` rather than `TopPair.ofSubsetMap` so `Hom.fst` stays definitionally `f'`.
private abbrev preimagePairMap (hf' : IsProperMap f'.hom) (K : CompactExhaustion V) (n : ℕ) :
    TopPair.ofSubset (K.preimage hf' n)ᶜ ⟶ TopPair.ofSubset (K n)ᶜ :=
  TopPair.ofHom f'
    (TopCat.ofHom ⟨Set.MapsTo.restrict f'.hom (K.preimage hf' n)ᶜ (K n)ᶜ (fun _ hx ↦ hx),
      f'.hom.continuous.restrict _⟩)

-- Uses `TopPair.ofHom` rather than `TopPair.ofSubsetMap` so `Hom.fst` stays definitionally `f`.
private abbrev baseChangePairMap (hf' : IsProperMap f'.hom) (hj : Function.Injective j.hom)
    (hsq : i ≫ f = f' ≫ j) (hpre : Set.range i.hom = f.hom ⁻¹' Set.range j.hom)
    (K : CompactExhaustion V) (n : ℕ) :
    TopPair.ofSubset (i.hom '' K.preimage hf' n)ᶜ ⟶
      TopPair.ofSubset (j.hom '' K n)ᶜ :=
  have hmaps : Set.MapsTo f.hom (i.hom '' K.preimage hf' n)ᶜ (j.hom '' K n)ᶜ := by
    simp only [CompactExhaustion.preimage_apply, preimage_image_eq_of_cartesian hj hsq hpre]
    exact fun _ hx ↦ hx
  TopPair.ofHom f (TopCat.ofHom ⟨hmaps.restrict, f.hom.continuous.restrict hmaps⟩)

private def baseChangeTowerMap (hf' : IsProperMap f'.hom) (hj : Function.Injective j.hom)
    (hsq : i ≫ f = f' ≫ j) (hpre : Set.range i.hom = f.hom ⁻¹' Set.range j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R Y) (K : CompactExhaustion V) :
    ambientRelativeChainComplexTower i ((pullback f.hom).obj L) (K.preimage hf') ⟶
      ambientRelativeChainComplexTower j L K where
  app n := TopPair.twistedChainComplexMap (baseChangePairMap hf' hj hsq hpre K n.unop) L
  naturality {m n} g := by
    apply (TopPair.ofSubset
      (i.hom '' K.preimage hf' m.unop)ᶜ).twistedChainComplex_hom_ext ((pullback f.hom).obj L)
    exact (twistedChainComplexπ_comp_ambientRelativeChainComplexTower_map_assoc
        i ((pullback f.hom).obj L) (K.preimage hf') g _).trans <|
      (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap
        (baseChangePairMap hf' hj hsq hpre K n.unop) L).trans <|
        ((TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc
            (baseChangePairMap hf' hj hsq hpre K m.unop) L _).trans <|
          congrArg (_ ≫ ·)
            (twistedChainComplexπ_comp_ambientRelativeChainComplexTower_map j L K g)).symm

private lemma baseChange_left_square (hf : IsProperMap f.hom) (hf' : IsProperMap f'.hom)
    (hj : Function.Injective j.hom) (hsq : i ≫ f = f' ≫ j)
    (hpre : Set.range i.hom = f.hom ⁻¹' Set.range j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R Y) (K : CompactExhaustion V) :
    locallyFiniteChainComplexMap f hf L ≫ locallyFiniteChainComplexToAmbientTower j L K =
      locallyFiniteChainComplexToAmbientTower i ((pullback f.hom).obj L) (K.preimage hf') ≫
        ComplexTower.limComplexMap (baseChangeTowerMap hf' hj hsq hpre L K) := by
  apply (ambientRelativeChainComplexTower j L K).isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  let φ := baseChangeTowerMap hf' hj hsq hpre L K
  have hKU : IsCompact (Set.range (TopPair.ofSubset
      (i.hom '' K.preimage hf' n)ᶜ).map)ᶜ :=
    (((K.preimage hf').isCompact n).image i.hom.continuous).compl_range_ofSubset_compl_map
  have hKV : IsCompact (Set.range (TopPair.ofSubset (j.hom '' K n)ᶜ).map)ᶜ :=
    ((K.isCompact n).image j.hom.continuous).compl_range_ofSubset_compl_map
  exact (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·)
      (locallyFiniteChainComplexToAmbientTower_comp_limComplexπ j L K n)).trans <|
      (TopPair.locallyFiniteChainComplexMap_comp_toRelative
          (baseChangePairMap hf' hj hsq hpre K n) hf L hKU hKV).trans <|
        ((Category.assoc _ _ _).trans <|
          (congrArg (_ ≫ ·) (ComplexTower.limComplexMap_comp_π φ n)).trans
            (locallyFiniteChainComplexToAmbientTower_comp_limComplexπ_assoc
              i ((pullback f.hom).obj L) (K.preimage hf') n (φ.app (op n)))).symm

private lemma baseChange_right_square_level (hf' : IsProperMap f'.hom)
    (hi : Function.Injective i.hom) (hj : Function.Injective j.hom)
    (hsq : i ≫ f = f' ≫ j) (hpre : Set.range i.hom = f.hom ⁻¹' Set.range j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R Y) (K : CompactExhaustion V) (n : ℕ) :
    (TopPair.ofSubset (K.preimage hf' n)ᶜ).twistedChainComplexCoefficientMap
          ((((pullbackCompIso i.hom f.hom).app L).symm ≪≫
            eqToIso (congrArg (fun g : U ⟶ Y ↦ (pullback g.hom).obj L) hsq) ≪≫
            (pullbackCompIso f'.hom j.hom).app L).hom) ≫
        TopPair.twistedChainComplexMap (preimagePairMap hf' K n) ((pullback j.hom).obj L) ≫
        TopPair.twistedChainComplexMap (injectivePairMap hj (K n)) L =
      TopPair.twistedChainComplexMap (injectivePairMap hi (K.preimage hf' n))
          ((pullback f.hom).obj L) ≫
        (baseChangeTowerMap hf' hj hsq hpre L K).app (op n) := by
  let KU := K.preimage hf'
  let sqIso : (pullback i.hom).obj ((pullback f.hom).obj L) ≅
      (pullback f'.hom).obj ((pullback j.hom).obj L) :=
    ((pullbackCompIso i.hom f.hom).app L).symm ≪≫
      eqToIso (congrArg (fun g : U ⟶ Y ↦ (pullback g.hom).obj L) hsq) ≪≫
      (pullbackCompIso f'.hom j.hom).app L
  apply (TopPair.ofSubset (KU n)ᶜ).twistedChainComplex_hom_ext _
  exact (TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc
      (TopPair.ofSubset (KU n)ᶜ) sqIso.hom _).trans <|
    (congrArg (_ ≫ ·) (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc
      (preimagePairMap hf' K n) ((pullback j.hom).obj L) _)).trans <|
      (congrArg (_ ≫ ·) (congrArg (_ ≫ ·)
        (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap
          (injectivePairMap hj (K n)) L))).trans <|
        (Category.assoc _ _ _).symm.trans <|
          (Category.assoc _ _ _).symm.trans <|
            (congrArg (· ≫ _)
              (twistedChainComplexMap_naturality_square i f f' j L hsq).symm).trans <|
              (Category.assoc _ _ _).trans <|
                ((TopPair.twistedChainComplexπ_comp_twistedChainComplexMap_assoc
                  (injectivePairMap hi (KU n)) ((pullback f.hom).obj L) _).trans <|
                  congrArg (_ ≫ ·)
                    (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap
                      (baseChangePairMap hf' hj hsq hpre K n) L)).symm

private lemma baseChange_right_square (hf' : IsProperMap f'.hom)
    (hi : Function.Injective i.hom) (hj : Function.Injective j.hom)
    (hsq : i ≫ f = f' ≫ j) (hpre : Set.range i.hom = f.hom ⁻¹' Set.range j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R Y) (K : CompactExhaustion V) :
    locallyFiniteChainComplexCoefficientMap
          ((((pullbackCompIso i.hom f.hom).app L).symm ≪≫
            eqToIso (congrArg (fun g : U ⟶ Y ↦ (pullback g.hom).obj L) hsq) ≪≫
            (pullbackCompIso f'.hom j.hom).app L).hom) ≫
        locallyFiniteChainComplexMap f' hf' ((pullback j.hom).obj L) ≫
          openEmbeddingRightLeg L K hj =
      openEmbeddingRightLeg ((pullback f.hom).obj L) (K.preimage hf') hi ≫
        ComplexTower.limComplexMap (baseChangeTowerMap hf' hj hsq hpre L K) := by
  let KU := K.preimage hf'
  let sqIso : (pullback i.hom).obj ((pullback f.hom).obj L) ≅
      (pullback f'.hom).obj ((pullback j.hom).obj L) :=
    ((pullbackCompIso i.hom f.hom).app L).symm ≪≫
      eqToIso (congrArg (fun g : U ⟶ Y ↦ (pullback g.hom).obj L) hsq) ≪≫
      (pullbackCompIso f'.hom j.hom).app L
  apply (ambientRelativeChainComplexTower j L K).isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  exact (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans <|
      (congrArg (_ ≫ ·) (congrArg (_ ≫ ·)
        (openEmbeddingRightLeg_comp_limComplexπ L K hj n))).trans <|
        (congrArg (_ ≫ ·) (TopPair.locallyFiniteChainComplexMap_comp_toRelative_assoc
          (preimagePairMap hf' K n) hf' ((pullback j.hom).obj L) _ _ _)).trans <|
          (TopPair.locallyFiniteChainComplexCoefficientMap_comp_toRelative_assoc
            (TopPair.ofSubset (KU n)ᶜ) sqIso.hom _ _).trans <|
            (Category.assoc _ _ _).trans <|
              (congrArg (_ ≫ ·)
                (baseChange_right_square_level hf' hi hj hsq hpre L K n)).trans <|
                ((Category.assoc _ _ _).trans <|
                  (congrArg (_ ≫ ·) (ComplexTower.limComplexMap_comp_π _ n)).trans
                    (openEmbeddingRightLeg_comp_limComplexπ_assoc
                      ((pullback f.hom).obj L) KU hi n _)).symm

end Helpers

/-- **Proper-map base change for exhaustion-explicit open restriction.** For a Cartesian square
`i ≫ f = f' ≫ j` with `f, f'` proper and `i, j` open embeddings (`range i = f⁻¹(range j)`),
pushing forward along `f` and restricting along `j` agrees with restricting along `i`, changing
coefficients across the square, and pushing forward along `f'`. -/
@[reassoc]
theorem borelMooreHomologyMap_comp_borelMooreHomologyRestrictOfExhaustion
    {U V X Y : TopCat.{v}} {f : X ⟶ Y} {f' : U ⟶ V} {i : U ⟶ X} {j : V ⟶ Y}
    (hf : IsProperMap f.hom) (hf' : IsProperMap f'.hom)
    (hi : IsOpenEmbedding i.hom) (hj : IsOpenEmbedding j.hom)
    (hsq : i ≫ f = f' ≫ j) (hpre : Set.range i.hom = f.hom ⁻¹' Set.range j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R Y)
    (K : CompactExhaustion V) (KU : CompactExhaustion U)
    (hK : ∀ n, closure (j.hom '' K n) ⊆ Set.range j.hom)
    (hKU : ∀ n, closure (i.hom '' KU n) ⊆ Set.range i.hom) (k : ℕ) :
    borelMooreHomologyMap f hf L k ≫ borelMooreHomologyRestrictOfExhaustion L hj K hK k =
      borelMooreHomologyRestrictOfExhaustion ((pullback f.hom).obj L) hi KU hKU k ≫
        borelMooreHomologyCoefficientMap
          ((((pullbackCompIso i.hom f.hom).app L).symm ≪≫
            eqToIso (congrArg (fun g : U ⟶ Y ↦ (pullback g.hom).obj L) hsq) ≪≫
            (pullbackCompIso f'.hom j.hom).app L).hom) k ≫
        borelMooreHomologyMap f' hf' ((pullback j.hom).obj L) k := by
  let KU' := K.preimage hf'
  have hKU' (n : ℕ) : closure (i.hom '' KU' n) ⊆ Set.range i.hom := by
    simp only [KU', CompactExhaustion.preimage_apply,
      preimage_image_eq_of_cartesian hj.injective hsq hpre, hpre]
    exact (f.hom.continuous.closure_preimage_subset _).trans (Set.preimage_mono (hK n))
  rw [borelMooreHomologyRestrictOfExhaustion_eq ((pullback f.hom).obj L) hi KU KU' hKU hKU' k]
  have := quasiIso_openEmbeddingRightLeg L K hj hK
  rw [← cancel_mono (HomologicalComplex.homologyMap (openEmbeddingRightLeg L K hj.injective) k),
    Category.assoc, borelMooreHomologyRestrictOfExhaustion_comp_rightLeg]
  calc borelMooreHomologyMap f hf L k ≫
        HomologicalComplex.homologyMap (locallyFiniteChainComplexToAmbientTower j L K) k
    _ = HomologicalComplex.homologyMap
          (locallyFiniteChainComplexToAmbientTower i ((pullback f.hom).obj L) KU') k ≫
          HomologicalComplex.homologyMap
            (ComplexTower.limComplexMap (baseChangeTowerMap hf' hj.injective hsq hpre L K)) k := by
        rw [← HomologicalComplex.homologyMap_comp, baseChange_left_square,
          HomologicalComplex.homologyMap_comp]
    _ = borelMooreHomologyRestrictOfExhaustion ((pullback f.hom).obj L) hi KU' hKU' k ≫
          HomologicalComplex.homologyMap (locallyFiniteChainComplexCoefficientMap _ ≫
            locallyFiniteChainComplexMap f' hf' ((pullback j.hom).obj L) ≫
              openEmbeddingRightLeg L K hj.injective) k := by
        rw [← borelMooreHomologyRestrictOfExhaustion_comp_rightLeg
            ((pullback f.hom).obj L) hi KU' hKU' k,
          Category.assoc, ← HomologicalComplex.homologyMap_comp,
          ← baseChange_right_square hf' hi.injective hj.injective hsq hpre L K]
    _ = (borelMooreHomologyRestrictOfExhaustion ((pullback f.hom).obj L) hi KU' hKU' k ≫
          borelMooreHomologyCoefficientMap _ k ≫
            borelMooreHomologyMap f' hf' ((pullback j.hom).obj L) k) ≫
          HomologicalComplex.homologyMap (openEmbeddingRightLeg L K hj.injective) k := by
        simp [HomologicalComplex.homologyMap_comp, Category.assoc]

/-- **Proper-map base change for canonical open restriction.** For a Cartesian square
`i ≫ f = f' ≫ j` with `f, f'` proper and `i, j` open embeddings, pushing forward along `f` and
restricting along `j` agrees with restricting along `i`, changing coefficients across the square,
and pushing forward along `f'`. -/
@[reassoc]
theorem borelMooreHomologyMap_comp_borelMooreHomologyRestrict
    {U V X Y : TopCat.{v}} [T2Space X] [T2Space Y]
    [WeaklyLocallyCompactSpace U] [SigmaCompactSpace U]
    [WeaklyLocallyCompactSpace V] [SigmaCompactSpace V]
    {f : X ⟶ Y} {f' : U ⟶ V} {i : U ⟶ X} {j : V ⟶ Y}
    (hf : IsProperMap f.hom) (hf' : IsProperMap f'.hom)
    (hi : IsOpenEmbedding i.hom) (hj : IsOpenEmbedding j.hom)
    (hsq : i ≫ f = f' ≫ j) (hpre : Set.range i.hom = f.hom ⁻¹' Set.range j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R Y) (k : ℕ) :
    borelMooreHomologyMap f hf L k ≫ borelMooreHomologyRestrict j hj L k =
      borelMooreHomologyRestrict i hi ((pullback f.hom).obj L) k ≫
        borelMooreHomologyCoefficientMap
          ((((pullbackCompIso i.hom f.hom).app L).symm ≪≫
            eqToIso (congrArg (fun g : U ⟶ Y ↦ (pullback g.hom).obj L) hsq) ≪≫
            (pullbackCompIso f'.hom j.hom).app L).hom) k ≫
        borelMooreHomologyMap f' hf' ((pullback j.hom).obj L) k := by
  have hKV := closure_image_compactExhaustion_subset_range j (CompactExhaustion.choice V)
  have hKU := closure_image_compactExhaustion_subset_range i (CompactExhaustion.choice U)
  rw [borelMooreHomologyRestrict_eq_ofExhaustion j hj L (CompactExhaustion.choice V) hKV k,
    borelMooreHomologyRestrict_eq_ofExhaustion i hi ((pullback f.hom).obj L)
      (CompactExhaustion.choice U) hKU k]
  exact borelMooreHomologyMap_comp_borelMooreHomologyRestrictOfExhaustion
    hf hf' hi hj hsq hpre L (CompactExhaustion.choice V) (CompactExhaustion.choice U) hKV hKU k

end TauCeti.LocalCoefficientSystem
