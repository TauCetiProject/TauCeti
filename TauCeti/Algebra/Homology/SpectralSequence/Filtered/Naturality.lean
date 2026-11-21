/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.MappingCone
public import TauCeti.Algebra.Homology.SpectralObject.Basic
public import TauCeti.Algebra.Homology.SpectralObject.SpectralSequenceMap
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Convergence

/-!
# Naturality of the spectral object and spectral sequence of a filtered complex

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
their spectral sequences. On the first page, whose objects are the cohomology of graded pieces,
that morphism is the map in cohomology of the induced morphisms of graded pieces
(`CochainComplex.spectralSequenceFirstPageXIsoCokernel_hom_naturality`). On the abutment,
identified with the cohomology of the filtered complex by `filtrationAbutmentIso`, the morphism of
spectral objects is the map in cohomology of the morphism of complexes
(`CochainComplex.spectralObjectMap_filtrationFunctorMap_hom_app_comp_filtrationAbutmentIso_hom`).

A natural transformation whose components are quasi-isomorphisms induces an isomorphism of
spectral objects (`CochainComplex.isIso_spectralObjectMap`): on each `H^n(f)` it is the map in
cohomology of a morphism of mapping cones, which is a quasi-isomorphism by the five lemma
(`CochainComplex.mappingCone.quasiIso_map`).

## Main definitions

* `CochainComplex.filtrationFunctorMap`: the morphism of filtration functors induced by a
  morphism of filtered complexes.

## Main results

* `CochainComplex.isIso_spectralObjectMap`: a natural transformation by quasi-isomorphisms induces
  an isomorphism of spectral objects.
* `CochainComplex.spectralObjectMap_hom_app_spectralObjectHIsoCokernel_hom`: on graded pieces,
  the morphism of spectral objects is the map in cohomology of the morphism of cokernels.
* `CochainComplex.spectralSequenceFirstPageXIsoCokernel_hom_naturality`:
  on the first page, the morphism of spectral sequences is the map in cohomology of the morphism
  of graded pieces.
* `CochainComplex.filtrationFunctorMap_id`, `CochainComplex.filtrationFunctorMap_comp`:
  functoriality of `filtrationFunctorMap`.
* `CochainComplex.quasiIso_filtrationFunctorMap_app`: a quasi-isomorphism of filtered complexes
  restricting to quasi-isomorphisms of the stages indexed by `ℤ` does so on all stages.
* `CochainComplex.spectralObjectMap_filtrationFunctorMap_hom_app_comp_filtrationAbutmentIso_hom`:
  on the abutment, the morphism of spectral objects is the map in cohomology of the morphism of
  complexes.
-/

public section

open CategoryTheory Limits ComposableArrows Abelian.SpectralObject

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
          (cokernel.map (F.map f) (G.map f) (α.app i) (α.app j) (α.naturality f).symm) n := by
  -- The square of mapping cones and cokernels, from `mappingCone.map_descShortComplex`.
  have key₀ := mappingCone.map_descShortComplex (ShortComplex.cokernelSequence (F.map f))
    (ShortComplex.cokernelSequence (G.map f))
    { τ₁ := α.app i
      τ₂ := α.app j
      τ₃ := cokernel.map (F.map f) (G.map f) (α.app i) (α.app j) (α.naturality f).symm
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

/-- **A quasi-isomorphism of functors to cochain complexes induces an isomorphism of spectral
objects.** If every component of `α : F ⟶ G` is a quasi-isomorphism, then `spectralObjectMap α`
is an isomorphism. -/
instance isIso_spectralObjectMap (α : F ⟶ G) [∀ i, QuasiIso (α.app i)] :
    IsIso (spectralObjectMap α) := by
  refine Abelian.SpectralObject.isIso_of_isIso_hom_app _ fun n i j f ↦ ?_
  have h := spectralObjectMap_hom_app_hIso α f n
  rw [← Iso.eq_comp_inv] at h
  rw [h]
  infer_instance

section FiltrationMap

variable {K L N : CochainComplex C ℤ} {F : ℤ → Subobject K} {hF : Monotone F}
  {G : ℤ → Subobject L} {hG : Monotone G} {H : ℤ → Subobject N} {hH : Monotone H}

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
    rw [← cancel_mono (filtrationFunctorArrow G hG b),
      Category.assoc _ ((filtrationFunctor G hG).map g), filtrationFunctor_map_comp_arrow]
    simp only [filtrationFunctorArrow, Category.assoc, Iso.inv_hom_id_assoc,
      Subobject.factorThru_arrow]
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
  rw [← cancel_mono (filtrationFunctorArrow F hF a), filtrationFunctorArrow,
    filtrationFunctorMap_app_comp,
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
  rw [← cancel_mono (filtrationFunctorArrow H hH a), filtrationFunctorArrow,
    filtrationFunctorMap_app_comp,
    NatTrans.comp_app, Category.assoc, filtrationFunctorMap_app_comp,
    filtrationFunctorMap_app_comp_assoc]

/-- A quasi-isomorphism of filtered complexes `f : K ⟶ L` which restricts to quasi-isomorphisms
`F n ⟶ G n` on every stage restricts to quasi-isomorphisms on every stage indexed by `EInt`: the
stages at `⊥` are zero and those at `⊤` are `K` and `L`. -/
lemma quasiIso_filtrationFunctorMap_app (f : K ⟶ L) (hf : ∀ n, (G n).Factors ((F n).arrow ≫ f))
    [QuasiIso f] (h : ∀ n : ℤ, QuasiIso ((filtrationFunctorMap hF hG f hf).app n)) (a : EInt) :
    QuasiIso ((filtrationFunctorMap hF hG f hf).app a) := by
  induction a using WithBotTop.rec with
  | bot =>
    have : IsIso ((filtrationFunctorMap hF hG f hf).app ⊥) :=
      isIso_of_source_target_iso_zero _ (isZero_filtrationFunctor_obj_bot _ _).isoZero
        (isZero_filtrationFunctor_obj_bot _ _).isoZero
    infer_instance
  | coe n => exact h n
  | top =>
    have : IsIso (filtrationEInt F ⊤).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).2 (filtrationEInt_top _)
    have : IsIso (filtrationEInt G ⊤).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).2 (filtrationEInt_top _)
    rw [← quasiIso_iff_comp_right _
      ((filtrationFunctorObjIso G hG ⊤).hom ≫ (filtrationEInt G ⊤).arrow),
      filtrationFunctorMap_app_comp]
    infer_instance

/-- **The induced morphism on the abutment.** Through `filtrationAbutmentIso`, which identifies
the abutment `H^n(⊥ ≤ ⊤)` with `H^n(K)`, the morphism of spectral objects induced by a morphism
`f : K ⟶ L` of filtered complexes is the map `H^n(f)`. -/
@[reassoc]
lemma spectralObjectMap_filtrationFunctorMap_hom_app_comp_filtrationAbutmentIso_hom (f : K ⟶ L)
    (hf : ∀ n, (G n).Factors ((F n).arrow ≫ f)) (n : ℤ) :
    ((spectralObjectMap (filtrationFunctorMap hF hG f hf)).hom n).app
        (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≫ (filtrationAbutmentIso G hG n).hom =
      (filtrationAbutmentIso F hF n).hom ≫ HomologicalComplex.homologyMap f n := by
  rw [filtrationAbutmentIso_hom, filtrationAbutmentIso_hom, ← Category.assoc,
    spectralObjectMap_hom_app_spectralObjectHIsoCokernel_hom, Category.assoc, Category.assoc,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  congr 2
  refine coequalizer.hom_ext ?_
  simp [filtrationFunctorArrow]

end FiltrationMap

section FirstPage

variable {F G : EInt ⥤ CochainComplex C ℤ}

/-- **The morphism of spectral sequences on the first page.** Let `α : F ⟶ G` be a morphism of
functors `EInt ⥤ CochainComplex C ℤ` whose transition maps `F_q ⟶ F_{q+1}` and `G_q ⟶ G_{q+1}`
are monomorphisms. On the first page, whose object at `(p, q)` is the cohomology
`H^{p+q}(F_{q+1}/F_q)` of a graded piece, the morphism of spectral sequences induced by `α` is the
map in cohomology of the induced morphism of graded pieces `F_{q+1}/F_q ⟶ G_{q+1}/G_q`. -/
@[reassoc]
lemma spectralSequenceFirstPageXIsoCokernel_hom_naturality
    (α : F ⟶ G) (pq : ℤ × ℤ) (i₁ i₂ : ℤ) (hi₁ : i₁ = pq.2) (hi₂ : i₂ = pq.2 + 1) (n : ℤ)
    (hn : n = pq.1 + pq.2) [Mono (F.map (homOfLE (coe_le_coe_of_eq_add_one hi₁ hi₂)))]
    [Mono (G.map (homOfLE (coe_le_coe_of_eq_add_one hi₁ hi₂)))] :
    ((spectralSequenceMap coreE₂Cohomological (spectralObjectMap α)).hom 2 le_rfl).f pq ≫
        (spectralSequenceFirstPageXIsoCokernel G pq i₁ i₂ hi₁ hi₂ n hn).hom =
      (spectralSequenceFirstPageXIsoCokernel F pq i₁ i₂ hi₁ hi₂ n hn).hom ≫
        HomologicalComplex.homologyMap
          (cokernel.map _ _ (α.app i₁) (α.app i₂) (α.naturality _).symm) n := by
  simp only [spectralSequenceMap_hom, spectralSequencePageMap_f,
    spectralSequenceFirstPageXIsoCokernel_eq, Iso.trans_hom]
  -- The degree of the recipe `coreE₂Cohomological` at `pq` is only definitionally
  -- `pq.1 + pq.2`, so the general first-page lemma is instantiated before rewriting with it.
  have h := spectralSequencePageXMap_comp_spectralSequenceFirstPageXIso_hom coreE₂Cohomological
    (spectralObjectMap α) pq (i₁ : EInt) (i₂ : EInt) (by simp [hi₁]) (by simp [hi₂]) n hn
  rw [reassoc_of% h, spectralObjectMap_hom_app_spectralObjectHIsoCokernel_hom]
  exact (Category.assoc _ _ _).symm

end FirstPage

end CochainComplex
