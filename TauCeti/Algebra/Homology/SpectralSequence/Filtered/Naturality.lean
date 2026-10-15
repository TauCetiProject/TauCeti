/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.SpectralObject

/-!
# Naturality of the spectral object of a filtered complex on graded pieces

A natural transformation `α : F ⟶ G` of functors `ι ⥤ CochainComplex C ℤ` induces a morphism of
spectral objects `CochainComplex.spectralObjectMap α` (in
`TauCeti.Algebra.Homology.SpectralSequence.Filtered.SpectralObject`), which on `H^n(f)` is the map
in cohomology of the induced morphism of mapping cones. When `F.map f` and `G.map f` are
monomorphisms, for instance for a morphism of filtrations, it is the map in cohomology of the
induced morphism of cokernels, that is, of graded pieces
(`CochainComplex.spectralObjectMap_hom_app_spectralObjectHIsoCokernel_hom`).

A morphism of complexes `f : K ⟶ L` sending each piece `F n` of an increasing filtration of `K`
into the piece `G n` of an increasing filtration of `L` induces a morphism of their functors
`CochainComplex.filtrationFunctorMap f hf : filtrationFunctor F hF ⟶ filtrationFunctor G hG`,
compatibly with identities and composition, and hence, through `spectralObjectMap`, a morphism of
their spectral sequences.

## Main definitions

* `CochainComplex.filtrationFunctorMap`: the morphism of filtration functors induced by a
  morphism of filtered complexes.

## Main results

* `CochainComplex.spectralObjectMap_hom_app_spectralObjectHIsoCokernel_hom`: on graded pieces,
  the morphism of spectral objects is the map in cohomology of the morphism of cokernels.
* `CochainComplex.filtrationFunctorMap_id`, `CochainComplex.filtrationFunctorMap_comp`:
  functoriality of `filtrationFunctorMap`.
-/

public section

open CategoryTheory Limits ComposableArrows

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} [Category* ι]
  {F G : ι ⥤ CochainComplex C ℤ}

/-- On `H^n(f)`, for monomorphisms `F.map f` and `G.map f`, the morphism of spectral objects
induced by `α` is the map in cohomology of the induced morphism of cokernels. -/
lemma spectralObjectMap_hom_app_spectralObjectHIsoCokernel_hom (α : F ⟶ G) {i j : ι}
    (f : i ⟶ j) [Mono (F.map f)] [Mono (G.map f)] (n : ℤ) :
    ((spectralObjectMap α).hom n).app (mk₁ f) ≫ (spectralObjectHIsoCokernel G f n).hom =
      (spectralObjectHIsoCokernel F f n).hom ≫
        HomologicalComplex.homologyMap
          (cokernel.map (F.map f) (G.map f) (α.app i) (α.app j) (α.naturality f)) n := by
  -- The square of mapping cones and cokernels, from `mappingCone.map_descShortComplex`.
  have key₀ := mappingCone.map_descShortComplex (ShortComplex.cokernelSequence (F.map f))
    (ShortComplex.cokernelSequence (G.map f))
    { τ₁ := α.app i
      τ₂ := α.app j
      τ₃ := cokernel.map (F.map f) (G.map f) (α.app i) (α.app j) (α.naturality f)
      comm₁₂ := (α.naturality f).symm
      comm₂₃ := (cokernel.π_desc _ _ _).symm }
  have key := (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (HomologicalComplex.homologyMap · n) key₀).trans
      (HomologicalComplex.homologyMap_comp _ _ n))
  rw [spectralObjectHIsoCokernel_hom, spectralObjectHIsoCokernel_hom]
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _) (spectralObjectMap_hom_app_hIso α f n)).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg ((spectralObjectHIso F f n).hom ≫ ·) key).trans (Category.assoc _ _ _).symm

section FiltrationMap

variable {K L N : CochainComplex C ℤ} {F : ℤ → Subobject K} {hF : Monotone F}
  {G : ℤ → Subobject L} {hG : Monotone G} {H : ℤ → Subobject N} {hH : Monotone H}

/-- A morphism of complexes sending each piece of a filtration into the corresponding piece of
another one does so for the extensions of the filtrations to `EInt`. -/
lemma factors_filtrationEInt (f : K ⟶ L) (hf : ∀ n, (G n).Factors ((F n).arrow ≫ f))
    (a : EInt) : (filtrationEInt G a).Factors ((filtrationEInt F a).arrow ≫ f) := by
  induction a using WithBotTop.rec with
  | bot =>
    rw [filtrationEInt_bot, filtrationEInt_bot, Subobject.bot_factors_iff_zero,
      Subobject.bot_arrow, zero_comp]
  | coe n =>
    rw [filtrationEInt_coe G n, filtrationEInt_coe F n]
    exact hf n
  | top =>
    simpa only [filtrationEInt_top] using
      Subobject.top_factors ((filtrationEInt F (⊤ : EInt)).arrow ≫ f)

/-- The inclusion of the object at `a` of the functor of a filtration into the filtered
complex. -/
private noncomputable abbrev filtrationι (F : ℤ → Subobject K) (hF : Monotone F) (a : EInt) :
    (filtrationFunctor F hF).obj a ⟶ K :=
  (filtrationFunctorObjIso F hF a).hom ≫ (filtrationEInt F a).arrow

private lemma map_comp_ι {a b : EInt} (g : a ⟶ b) :
    (filtrationFunctor F hF).map g ≫ filtrationι F hF b = filtrationι F hF a := by
  rw [← Category.assoc, filtrationFunctor_map_comp_objIso_hom, Category.assoc,
    Subobject.ofLE_arrow]

variable (hF hG) in
/-- **The morphism of filtration functors induced by a morphism of filtered complexes**: a
morphism `f : K ⟶ L` sending each piece `F n` into `G n` restricts to morphisms
`F n ⟶ G n`, natural in `n`. -/
noncomputable def filtrationFunctorMap (f : K ⟶ L) (hf : ∀ n, (G n).Factors ((F n).arrow ≫ f)) :
    filtrationFunctor F hF ⟶ filtrationFunctor G hG where
  app a := (filtrationFunctorObjIso F hF a).hom ≫
    (filtrationEInt G a).factorThru _ (factors_filtrationEInt f hf a) ≫
      (filtrationFunctorObjIso G hG a).inv
  naturality a b g := by
    rw [← cancel_mono (filtrationι G hG b), Category.assoc _ ((filtrationFunctor G hG).map g),
      map_comp_ι]
    simp only [filtrationι, Category.assoc, Iso.inv_hom_id_assoc, Subobject.factorThru_arrow]
    rw [← Category.assoc, filtrationFunctor_map_comp_objIso_hom, Category.assoc,
      ← Category.assoc _ _ f, Subobject.ofLE_arrow]

/-- The components of `filtrationFunctorMap f hf` are the restrictions of `f`. -/
@[reassoc (attr := simp)]
lemma filtrationFunctorMap_app_comp (f : K ⟶ L) (hf : ∀ n, (G n).Factors ((F n).arrow ≫ f))
    (a : EInt) :
    (filtrationFunctorMap hF hG f hf).app a ≫ (filtrationFunctorObjIso G hG a).hom ≫
        (filtrationEInt G a).arrow =
      (filtrationFunctorObjIso F hF a).hom ≫ (filtrationEInt F a).arrow ≫ f := by
  simp [filtrationFunctorMap]

/-- `filtrationFunctorMap` only depends on the morphism of complexes. -/
lemma filtrationFunctorMap_congr {f f' : K ⟶ L} (e : f = f')
    (hf : ∀ n, (G n).Factors ((F n).arrow ≫ f)) :
    filtrationFunctorMap hF hG f hf = filtrationFunctorMap hF hG f' (e ▸ hf) := by
  subst e
  rfl

/-- The identity of a filtered complex induces the identity of its filtration functor. -/
@[simp]
lemma filtrationFunctorMap_id (hf : ∀ n, (F n).Factors ((F n).arrow ≫ 𝟙 K)) :
    filtrationFunctorMap hF hF (𝟙 K) hf = 𝟙 _ := by
  ext a : 2
  rw [← cancel_mono (filtrationι F hF a), filtrationι, filtrationFunctorMap_app_comp,
    NatTrans.id_app, Category.id_comp, Category.comp_id]

/-- A composite of morphisms of filtered complexes induces the composite of the morphisms of
filtration functors.  Not `@[simp]`: the intermediate filtration cannot be inferred from the
left-hand side. -/
lemma filtrationFunctorMap_comp (f : K ⟶ L) (g : L ⟶ N)
    (hf : ∀ n, (G n).Factors ((F n).arrow ≫ f)) (hg : ∀ n, (H n).Factors ((G n).arrow ≫ g))
    (hfg : ∀ n, (H n).Factors ((F n).arrow ≫ f ≫ g)) :
    filtrationFunctorMap hF hH (f ≫ g) hfg =
      filtrationFunctorMap hF hG f hf ≫ filtrationFunctorMap hG hH g hg := by
  ext a : 2
  rw [← cancel_mono (filtrationι H hH a), filtrationι, filtrationFunctorMap_app_comp,
    NatTrans.comp_app, Category.assoc, filtrationFunctorMap_app_comp,
    filtrationFunctorMap_app_comp_assoc]

end FiltrationMap

end CochainComplex
