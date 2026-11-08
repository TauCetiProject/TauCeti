/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject
public import Mathlib.Algebra.Homology.SpectralObject.FirstPage
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Subobject.Lattice
public import TauCeti.Algebra.Homology.HomotopyCategory.Triangulated
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# The spectral object and the spectral sequence of a filtered complex

A functor `F : ι ⥤ CochainComplex C ℤ` to cochain complexes in an abelian category `C` gives a
spectral object `CochainComplex.spectralObject F` in `C` indexed by `ι`: to `f : i ⟶ j` and
`n : ℤ` it attaches the `n`th cohomology of the mapping cone of `F.map f`, and its connecting
maps are those of the distinguished triangles of mapping cones in the homotopy category. When
`F.map f` is a monomorphism, this cohomology is that of the cokernel of `F.map f`
(`CochainComplex.spectralObjectHIsoCokernel`). An increasing filtration `ℤ → Subobject K` of a
cochain complex `K`, extended by `⊥` and `⊤`, is such a functor indexed by `EInt`
(`CochainComplex.filtrationFunctor`), whose transition maps are monomorphisms.

The spectral sequence of a functor indexed by `EInt` is Mathlib's spectral sequence of a spectral
object, for the recipe `coreE₂Cohomological`
(`CochainComplex.spectralSequence`): its first page, numbered `2` there, has at `(p, q)` the
cohomology `H^{p+q}` of the mapping cone of `F_q ⟶ F_{q+1}`
(`CochainComplex.spectralSequenceFirstPageXIso`). When this map is a monomorphism, for instance
for a filtration, this is the cohomology `H^{p+q}(F_{q+1}/F_q)` of a graded piece
(`CochainComplex.spectralSequenceFirstPageXIsoCokernel`).

## Main definitions

* `CochainComplex.spectralObject F`: the spectral object of `F : ι ⥤ CochainComplex C ℤ`.
* `CochainComplex.spectralObjectMap α`: the morphism of spectral objects induced by a natural
  transformation `α : F ⟶ G`, functorial in `α`.
* `CochainComplex.filtrationFunctor F hF`: the functor `EInt ⥤ CochainComplex C ℤ` of an
  increasing filtration `F : ℤ → Subobject K`.
* `CochainComplex.spectralSequence F`: the spectral sequence of `F : EInt ⥤ CochainComplex C ℤ`.

## Main results

* `CochainComplex.cokernelFiltrationFunctorMapIso`: the cokernel of a transition map of the
  functor of a filtration is the cokernel of the inclusion of subcomplexes.
* `CochainComplex.cokernelFiltrationFunctorMapIsoOfIsColimit`: when the pieces of a filtration
  are represented by monomorphisms `X p ⟶ K`, that cokernel is any cokernel of `X p ⟶ X (p + 1)`.
* `CochainComplex.spectralObjectHIso`: `H^n(f)` is the cohomology of the mapping cone of
  `F.map f`.
* `CochainComplex.spectralObjectHIsoCokernel`: for a monomorphism `F.map f`, `H^n(f)` is the
  cohomology of the cokernel of `F.map f`.
* `CochainComplex.spectralObject_H_map_comp_spectralObjectHIso_hom` and
  `CochainComplex.spectralObject_H_map_comp_spectralObjectHIsoCokernel_hom`: the maps
  `H^n(f) ⟶ H^n(g)` induced by morphisms of arrows are the maps in cohomology of the induced
  morphisms of mapping cones, respectively cokernels.
* `CochainComplex.spectralSequenceFirstPageXIso`: the first page is the cohomology of the mapping
  cones of `F_q ⟶ F_{q+1}`.
* `CochainComplex.spectralSequenceFirstPageXIsoCokernel`: when `F_q ⟶ F_{q+1}` is a monomorphism,
  the first page is `H^{p+q}(F_{q+1}/F_q)`.
* `CochainComplex.spectralObject_δ`: the connecting maps are those of the triangles of mapping
  cones.
* `CochainComplex.spectralObjectMap_hom_app_hIso`: on `H^n(f)`, `spectralObjectMap α` is the map
  in cohomology of the induced morphism of mapping cones.

## References

* J.-L. Verdier, *Des catégories dérivées des catégories abéliennes*, II.4.
* J. McCleary, *A User's Guide to Spectral Sequences*, Theorem 2.6.
-/

public section

open CategoryTheory Limits ComposableArrows HomotopyCategory

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

section Triangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {ι : Type*} [Category* ι] (F : ι ⥤ CochainComplex C ℤ)

/-- The connecting maps of the triangulated spectral object
`(spectralObjectMappingCone C).precomp F` are the third morphisms of the distinguished
triangles of mapping cones attached to `F.map f` and `F.map g`. -/
lemma precomp_spectralObjectMappingCone_δ {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) :
    ((spectralObjectMappingCone C).precomp F).δ f g =
      ((quotient C (ComplexShape.up ℤ)).mapTriangle.obj
        (mappingConeCompTriangle (F.map f) (F.map g))).mor₃ := by
  -- The comparison isomorphisms `F.mapComposableArrowsObjMk₁Iso` have identity components, so
  -- their images are identities; they are only equal to `𝟙` up to definitional unfolding of the
  -- objects, which is why `erw` is needed below.
  have e (a b : ι) (u : a ⟶ b) :
      (spectralObjectMappingCone C).ω₁.map (F.mapComposableArrowsObjMk₁Iso u).hom = 𝟙 _ :=
    (congrArg (quotient C (ComplexShape.up ℤ)).map (mappingCone.map_id (F.map u))).trans
      (CategoryTheory.Functor.map_id _ _)
  have e' (a b : ι) (u : a ⟶ b) :
      (spectralObjectMappingCone C).ω₁.map (F.mapComposableArrowsObjMk₁Iso u).inv = 𝟙 _ :=
    (congrArg (quotient C (ComplexShape.up ℤ)).map (mappingCone.map_id (F.map u))).trans
      (CategoryTheory.Functor.map_id _ _)
  dsimp [Triangulated.SpectralObject.precomp, Triangulated.SpectralObject.δ]
  rw [e, e']
  erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

variable {F} {G H : ι ⥤ CochainComplex C ℤ}

/-- The morphism of triangulated spectral objects in the homotopy category induced by a natural
transformation `α : F ⟶ G`: on `f : i ⟶ j`, the morphism of mapping cones of `F.map f` and
`G.map f` given by `α.app i` and `α.app j`. -/
noncomputable def triangulatedSpectralObjectMap (α : F ⟶ G) :
    (spectralObjectMappingCone C).precomp F ⟶ (spectralObjectMappingCone C).precomp G where
  hom := Functor.whiskerRight ((Functor.whiskeringRight _ _ _).map α)
    (spectralObjectMappingCone C).ω₁
  comm {i j k} f g := by
    rw [precomp_spectralObjectMappingCone_δ, precomp_spectralObjectMappingCone_δ]
    exact mappingConeCompTriangleh_mor₃_naturality (F.map f) (F.map g) (G.map f)
      (G.map g) (α.app i) (α.app j) (α.app k) (α.naturality f) (α.naturality g)

@[simp]
lemma triangulatedSpectralObjectMap_id (F : ι ⥤ CochainComplex C ℤ) :
    triangulatedSpectralObjectMap (𝟙 F) = 𝟙 _ := by
  ext : 1
  simp [triangulatedSpectralObjectMap]
  rfl

@[simp]
lemma triangulatedSpectralObjectMap_comp (α : F ⟶ G) (β : G ⟶ H) :
    triangulatedSpectralObjectMap (α ≫ β) =
      triangulatedSpectralObjectMap α ≫ triangulatedSpectralObjectMap β := by
  ext : 1
  simp [triangulatedSpectralObjectMap]
  rfl

end Triangulated

section SpectralObject

variable {ι : Type*} [Category* ι] (F : ι ⥤ CochainComplex C ℤ)

/-- The spectral object of a functor `F : ι ⥤ CochainComplex C ℤ`: its object `H^n(f)` for
`f : i ⟶ j` is obtained by applying the cohomology functor of the homotopy category to the mapping
cone of `F.map f` (see `spectralObjectHIso`), and its connecting maps are those of the
distinguished triangles of mapping cones (see `spectralObject_δ`). -/
noncomputable def spectralObject : Abelian.SpectralObject C ι :=
  ((spectralObjectMappingCone C).precomp F).mapHomologicalFunctor
    (homologyFunctor C (ComplexShape.up ℤ) 0)

/-- The objects `H^n(f)` of the spectral object of `F` are the cohomology of the mapping cones of
the maps `F.map f`. -/
noncomputable def spectralObjectHIso {i j : ι} (f : i ⟶ j) (n : ℤ) :
    ((spectralObject F).H n).obj (mk₁ f) ≅ (mappingCone (F.map f)).homology n :=
  (homologyFunctorFactors C (ComplexShape.up ℤ) n).app (mappingCone (F.map f))

/-- The connecting maps of the spectral object of `F`, read through `spectralObjectHIso`, are the
maps in cohomology induced by the third morphisms `cone (F.map g) ⟶ (cone (F.map f))⟦1⟧` of the
triangles of mapping cones attached to `F.map f` and `F.map g`. -/
lemma spectralObject_δ {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (spectralObject F).δ f g n₀ n₁ h =
      (spectralObjectHIso F g n₀).hom ≫
        (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
          (mappingConeCompTriangle (F.map f) (F.map g)).mor₃ n₀ n₁ (by lia) ≫
        (spectralObjectHIso F f n₁).inv := by
  refine (Triangulated.SpectralObject.mapHomologicalFunctor_δ _ _ f g n₀ n₁ h).trans
    (Eq.trans (b := (homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ
      ((quotient C (ComplexShape.up ℤ)).mapTriangle.obj
        (mappingConeCompTriangle (F.map f) (F.map g))) n₀ n₁ h) ?_ ?_)
  · dsimp only [Functor.homologySequenceδ]
    congr 1
    exact precomp_spectralObjectMappingCone_δ F f g
  · exact homologySequenceδ_quotient_mapTriangle_obj _ n₀ n₁ h

/-- The maps `H^n(f) ⟶ H^n(g)` of the spectral object of `F` induced by morphisms of arrows
`φ : f ⟶ g`, read through `spectralObjectHIso`, are the maps in cohomology of the induced
morphisms of mapping cones. -/
@[reassoc]
lemma spectralObject_H_map_comp_spectralObjectHIso_hom {i j i' j' : ι} {f : i ⟶ j}
    {g : i' ⟶ j'} (φ : mk₁ f ⟶ mk₁ g) (n : ℤ) :
    ((spectralObject F).H n).map φ ≫ (spectralObjectHIso F g n).hom =
      (spectralObjectHIso F f n).hom ≫ HomologicalComplex.homologyMap
        (mappingCone.map (F.map f) (F.map g) (F.map (φ.app 0)) (F.map (φ.app 1))
          (naturality' ((F.mapComposableArrows 1).map φ) 0 1)) n :=
  (homologyFunctorFactors C (ComplexShape.up ℤ) n).hom.naturality _

variable {F} {G H : ι ⥤ CochainComplex C ℤ}

/-- The morphism of spectral objects `spectralObject F ⟶ spectralObject G` induced by a natural
transformation `α : F ⟶ G`. -/
noncomputable def spectralObjectMap (α : F ⟶ G) : spectralObject F ⟶ spectralObject G :=
  (Triangulated.SpectralObject.mapHomologicalFunctorFunctor
    (homologyFunctor C (ComplexShape.up ℤ) 0) ι).map (triangulatedSpectralObjectMap α)

@[simp]
lemma spectralObjectMap_id (F : ι ⥤ CochainComplex C ℤ) :
    spectralObjectMap (𝟙 F) = 𝟙 _ := by
  simp [spectralObjectMap]
  rfl

@[simp]
lemma spectralObjectMap_comp (α : F ⟶ G) (β : G ⟶ H) :
    spectralObjectMap (α ≫ β) = spectralObjectMap α ≫ spectralObjectMap β := by
  simp [spectralObjectMap]
  rfl

/-- On `H^n(f)`, the morphism of spectral objects induced by `α` is the map in cohomology of the
morphism of mapping cones of `F.map f` and `G.map f`. -/
lemma spectralObjectMap_hom_app_hIso (α : F ⟶ G) {i j : ι} (f : i ⟶ j) (n : ℤ) :
    ((spectralObjectMap α).hom n).app (mk₁ f) ≫ (spectralObjectHIso G f n).hom =
      (spectralObjectHIso F f n).hom ≫
        HomologicalComplex.homologyMap
          (mappingCone.map (F.map f) (G.map f) (α.app i) (α.app j) (α.naturality f)) n := by
  dsimp [spectralObjectMap, triangulatedSpectralObjectMap, spectralObjectHIso]
  convert ((homologyFunctorFactors C (ComplexShape.up ℤ) n).hom.naturality
    (mappingCone.map (F.map f) (G.map f) (α.app i) (α.app j) (α.naturality f))) using 2
  all_goals rfl

variable (F)

/-- When `F.map f` is a monomorphism, `H^n(f)` is the `n`th cohomology of the cokernel of
`F.map f`, through the quasi-isomorphism `mappingCone.descShortComplex` from the mapping cone of
`F.map f` to its cokernel. -/
noncomputable def spectralObjectHIsoCokernel {i j : ι} (f : i ⟶ j) [Mono (F.map f)] (n : ℤ) :
    ((spectralObject F).H n).obj (mk₁ f) ≅ (cokernel (F.map f)).homology n :=
  have := mappingCone.quasiIso_descShortComplex (TauCeti.cokernelSequence_shortExact (F.map f))
  spectralObjectHIso F f n ≪≫
    isoOfQuasiIsoAt
      (mappingCone.descShortComplex (ShortComplex.cokernelSequence (F.map f))) n

lemma spectralObjectHIsoCokernel_hom {i j : ι} (f : i ⟶ j) [Mono (F.map f)] (n : ℤ) :
    (spectralObjectHIsoCokernel F f n).hom =
      (spectralObjectHIso F f n).hom ≫ HomologicalComplex.homologyMap
        (mappingCone.descShortComplex (ShortComplex.cokernelSequence (F.map f))) n :=
  (rfl)

/-- The maps `H^n(f) ⟶ H^n(g)` of the spectral object of `F` induced by morphisms of arrows
`φ : f ⟶ g` such that `F.map f` and `F.map g` are monomorphisms, read through
`spectralObjectHIsoCokernel`, are the maps in cohomology of the induced morphisms of cokernels. -/
@[reassoc]
lemma spectralObject_H_map_comp_spectralObjectHIsoCokernel_hom {i j i' j' : ι} {f : i ⟶ j}
    {g : i' ⟶ j'} [Mono (F.map f)] [Mono (F.map g)] (φ : mk₁ f ⟶ mk₁ g) (n : ℤ) :
    ((spectralObject F).H n).map φ ≫ (spectralObjectHIsoCokernel F g n).hom =
      (spectralObjectHIsoCokernel F f n).hom ≫ HomologicalComplex.homologyMap
        (cokernel.map (F.map f) (F.map g) (F.map (φ.app 0)) (F.map (φ.app 1))
          (naturality' ((F.mapComposableArrows 1).map φ) 0 1)) n := by
  have w : F.map f ≫ F.map (φ.app 1) = F.map (φ.app 0) ≫ F.map g :=
    naturality' ((F.mapComposableArrows 1).map φ) 0 1
  -- The morphism of cokernel sequences induced by `φ`.
  let ψ : ShortComplex.cokernelSequence (F.map f) ⟶ ShortComplex.cokernelSequence (F.map g) :=
    { τ₁ := F.map (φ.app 0)
      τ₂ := F.map (φ.app 1)
      τ₃ := cokernel.map _ _ _ _ w
      comm₁₂ := w.symm
      comm₂₃ := (cokernel.π_desc _ _ _).symm }
  have e := congrArg (fun u ↦ HomologicalComplex.homologyMap u n)
    (mappingCone.map_descShortComplex _ _ ψ)
  simp only [HomologicalComplex.homologyMap_comp] at e
  rw [spectralObjectHIsoCokernel_hom, spectralObjectHIsoCokernel_hom]
  -- The two sides differ by the identification of `mappingCone (cokernelSequence _).f` with
  -- `mappingCone _`, which only holds up to unfolding, so the associativity steps are terms.
  exact (Category.assoc _ _ _).symm.trans
    ((spectralObject_H_map_comp_spectralObjectHIso_hom F φ n =≫ _).trans
      ((Category.assoc _ _ _).trans ((_ ≫= e).trans (Category.assoc _ _ _).symm)))

end SpectralObject

section Filtration

variable {K : CochainComplex C ℤ} (F : ℤ → Subobject K) (hF : Monotone F)

/-- An increasing filtration `F : ℤ → Subobject K` extended to `EInt`, by `⊥` at `⊥` and `⊤` at
`⊤`. -/
noncomputable def filtrationEInt : EInt → Subobject K :=
  WithBotTop.rec ⊥ F ⊤

@[simp]
lemma filtrationEInt_bot : filtrationEInt F ⊥ = ⊥ := (rfl)

@[simp]
lemma filtrationEInt_coe (n : ℤ) : filtrationEInt F n = F n := (rfl)

@[simp]
lemma filtrationEInt_top : filtrationEInt F ⊤ = ⊤ := (rfl)

include hF in
lemma monotone_filtrationEInt : Monotone (filtrationEInt F) := by
  intro a b hab
  induction a using WithBotTop.rec with
  | bot => simp
  | top =>
    induction b using WithBotTop.rec with
    | top => simp
    | bot => simp at hab
    | coe b => exact absurd hab (by simp)
  | coe a =>
    induction b using WithBotTop.rec with
    | bot => exact absurd hab (by simp)
    | top => simp
    | coe b => simpa using hF (WithBotTop.coe_le_coe.mp hab)

/-- The functor `EInt ⥤ CochainComplex C ℤ` of an increasing filtration `F : ℤ → Subobject K`:
it sends `n : ℤ` to the subcomplex `F n`, `⊥` to the zero subcomplex and `⊤` to `K`. -/
noncomputable def filtrationFunctor : EInt ⥤ CochainComplex C ℤ :=
  (monotone_filtrationEInt F hF).functor ⋙ Subobject.underlying

@[simp]
lemma filtrationFunctor_obj (a : EInt) :
    (filtrationFunctor F hF).obj a = (filtrationEInt F a : CochainComplex C ℤ) :=
  (rfl)

lemma filtrationFunctor_obj_coe (n : ℤ) :
    (filtrationFunctor F hF).obj n = (F n : CochainComplex C ℤ) :=
  (rfl)

/-- The object of the functor of a filtration at `a : EInt` is the subcomplex `filtrationEInt F a`
of `K`. -/
noncomputable def filtrationFunctorObjIso (a : EInt) :
    (filtrationFunctor F hF).obj a ≅ (filtrationEInt F a : CochainComplex C ℤ) :=
  Iso.refl _

/-- The transition maps of the functor of a filtration are the inclusions of subcomplexes. -/
lemma filtrationFunctor_map_comp_objIso_hom {a b : EInt} (f : a ⟶ b) :
    (filtrationFunctor F hF).map f ≫ (filtrationFunctorObjIso F hF b).hom =
      (filtrationFunctorObjIso F hF a).hom ≫
        Subobject.ofLE _ _ (monotone_filtrationEInt F hF (leOfHom f)) := by
  dsimp [filtrationFunctorObjIso, filtrationFunctor]
  simp only [Category.comp_id, Category.id_comp]
  rfl

/-- The maps `F_⊥ ⟶ F_a` of the functor of a filtration vanish, their source being zero. -/
lemma filtrationFunctor_map_bot (a : EInt) :
    (filtrationFunctor F hF).map (homOfLE (bot_le : (⊥ : EInt) ≤ a)) = 0 := by
  refine IsZero.eq_of_src ?_ _ _
  rw [filtrationFunctor_obj, filtrationEInt_bot]
  exact IsZero.of_iso (isZero_zero _) Subobject.botCoeIsoZero

instance {a b : EInt} (f : a ⟶ b) : Mono ((filtrationFunctor F hF).map f) :=
  inferInstanceAs (Mono (Subobject.ofLE _ _ (monotone_filtrationEInt F hF (leOfHom f))))

/-- The cokernel of a transition map of the functor of a filtration is the cokernel of the
corresponding inclusion of subcomplexes. -/
noncomputable def cokernelFiltrationFunctorMapIso {a b : EInt} (f : a ⟶ b) :
    cokernel ((filtrationFunctor F hF).map f) ≅
      cokernel (Subobject.ofLE _ _ (monotone_filtrationEInt F hF (leOfHom f))) :=
  cokernel.mapIso _ _ (filtrationFunctorObjIso F hF a) (filtrationFunctorObjIso F hF b)
    (filtrationFunctor_map_comp_objIso_hom F hF f)

/-- The isomorphism `CochainComplex.cokernelFiltrationFunctorMapIso` is induced by the identity of
the subcomplex. -/
@[reassoc (attr := simp)]
lemma π_cokernelFiltrationFunctorMapIso_hom {a b : EInt} (f : a ⟶ b) :
    cokernel.π _ ≫ (cokernelFiltrationFunctorMapIso F hF f).hom =
      (filtrationFunctorObjIso F hF b).hom ≫ cokernel.π _ := by
  simp [cokernelFiltrationFunctorMapIso]

/-- The inclusion of the object at `a : EInt` of the functor of a filtration into the filtered
complex. -/
noncomputable abbrev filtrationFunctorArrow (a : EInt) : (filtrationFunctor F hF).obj a ⟶ K :=
  (filtrationFunctorObjIso F hF a).hom ≫ (filtrationEInt F a).arrow

/-- The inclusions into the filtered complex are natural in the object of the functor of a
filtration. -/
@[reassoc (attr := simp)]
lemma filtrationFunctor_map_comp_arrow {a b : EInt} (f : a ⟶ b) :
    (filtrationFunctor F hF).map f ≫ filtrationFunctorArrow F hF b =
      filtrationFunctorArrow F hF a := by
  rw [← Category.assoc, filtrationFunctor_map_comp_objIso_hom, Category.assoc,
    Subobject.ofLE_arrow]

/-- At an integer `q`, the inclusion `filtrationFunctorArrow F hF q` is the inclusion of the
subcomplex `F_q`. -/
@[simp]
lemma eqToHom_comp_filtrationFunctorArrow (q : ℤ) :
    eqToHom (filtrationFunctor_obj_coe F hF q).symm ≫ filtrationFunctorArrow F hF q =
      (F q).arrow :=
  -- Both the comparison `eqToHom` and `filtrationFunctorObjIso` are identities by definition.
  (Category.id_comp _).trans (Category.id_comp _)

/-- A morphism of complexes sending each piece of a filtration into the corresponding piece of
another one does so for the extensions of the filtrations to `EInt`. -/
lemma factors_filtrationEInt {F : ℤ → Subobject K} {L : CochainComplex C ℤ}
    {G : ℤ → Subobject L} (f : K ⟶ L) (hf : ∀ n, (G n).Factors ((F n).arrow ≫ f)) (a : EInt) :
    (filtrationEInt G a).Factors ((filtrationEInt F a).arrow ≫ f) := by
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

end Filtration

section SpectralSequence

/-- The inequality `i₁ ≤ i₂` in `EInt` between the indices of a graded piece of a filtration. -/
lemma coe_le_coe_of_eq_add_one {i₁ i₂ q : ℤ} (hi₁ : i₁ = q) (hi₂ : i₂ = q + 1) :
    (i₁ : EInt) ≤ i₂ := by
  simp [hi₁, hi₂]

variable (F : EInt ⥤ CochainComplex C ℤ)

/-- The spectral sequence of a functor `F : EInt ⥤ CochainComplex C ℤ`, starting on page `2`
(the first page in Mathlib's numbering for `coreE₂Cohomological`). -/
noncomputable abbrev spectralSequence :=
  (spectralObject F).spectralSequence Abelian.SpectralObject.coreE₂Cohomological

/-- The objects on the first page of the spectral sequence of `F`: at `pq = (p, q)`, the
`(p + q)`th cohomology of the mapping cone of `F_q ⟶ F_{q+1}`. The indices `q`, `q + 1` and
`p + q` are given as `i₁`, `i₂` and `n` together with equations, for flexibility. -/
noncomputable def spectralSequenceFirstPageXIso (pq : ℤ × ℤ) (i₁ i₂ : ℤ) (hi₁ : i₁ = pq.2)
    (hi₂ : i₂ = pq.2 + 1) (n : ℤ) (hn : n = pq.1 + pq.2) :
    ((spectralSequence F).page 2).X pq ≅
      (mappingCone (F.map (homOfLE (coe_le_coe_of_eq_add_one hi₁ hi₂)))).homology n :=
  (spectralObject F).spectralSequenceFirstPageXIso _ pq i₁ i₂ (by simp [hi₁]) (by simp [hi₂]) n
    hn ≪≫ spectralObjectHIso F _ _

/-- The objects on the first page of the spectral sequence of `F` when the transition maps of
`F` are monomorphisms: at `pq = (p, q)`, the `(p + q)`th cohomology of the graded piece
`F_{q+1}/F_q`. -/
noncomputable def spectralSequenceFirstPageXIsoCokernel (pq : ℤ × ℤ) (i₁ i₂ : ℤ)
    (hi₁ : i₁ = pq.2) (hi₂ : i₂ = pq.2 + 1) (n : ℤ) (hn : n = pq.1 + pq.2)
    [Mono (F.map (homOfLE (coe_le_coe_of_eq_add_one hi₁ hi₂)))] :
    ((spectralSequence F).page 2).X pq ≅
      (cokernel (F.map (homOfLE (coe_le_coe_of_eq_add_one hi₁ hi₂)))).homology n :=
  (spectralObject F).spectralSequenceFirstPageXIso _ pq i₁ i₂ (by simp [hi₁]) (by simp [hi₂]) n
    hn ≪≫ spectralObjectHIsoCokernel F _ _

lemma spectralSequenceFirstPageXIsoCokernel_eq (pq : ℤ × ℤ) (i₁ i₂ : ℤ)
    (hi₁ : i₁ = pq.2) (hi₂ : i₂ = pq.2 + 1) (n : ℤ) (hn : n = pq.1 + pq.2)
    [Mono (F.map (homOfLE (coe_le_coe_of_eq_add_one hi₁ hi₂)))] :
    spectralSequenceFirstPageXIsoCokernel F pq i₁ i₂ hi₁ hi₂ n hn =
      (spectralObject F).spectralSequenceFirstPageXIso _ pq i₁ i₂ (by simp [hi₁]) (by simp [hi₂])
        n hn ≪≫ spectralObjectHIsoCokernel F _ _ :=
  (rfl)

end SpectralSequence

section Stages

variable {K : CochainComplex C ℤ} (F : ℤ → Subobject K) (hF : Monotone F)
  {X : ℤ → CochainComplex C ℤ} (ι : ∀ p, X p ⟶ K) [∀ p, Mono (ι p)]
  (hFι : ∀ p, F p = Subobject.mk (ι p))

/-- When each piece `F p` of a filtration is represented by a monomorphism `ι p : X p ⟶ K`, the
object of the functor of the filtration at `p` is `X p`. -/
noncomputable def filtrationFunctorObjIsoOfEqMk (p : ℤ) :
    (filtrationFunctor F hF).obj p ≅ X p :=
  filtrationFunctorObjIso F hF p ≪≫
    eqToIso (congrArg (fun S : Subobject K ↦ (S : CochainComplex C ℤ))
      ((filtrationEInt_coe F p).trans (hFι p))) ≪≫
    Subobject.underlyingIso (ι p)

/-- The identification `CochainComplex.filtrationFunctorObjIsoOfEqMk` is compatible with the
inclusions into the filtered complex. -/
@[reassoc (attr := simp)]
lemma filtrationFunctorObjIsoOfEqMk_hom_comp (p : ℤ) :
    (filtrationFunctorObjIsoOfEqMk F hF ι hFι p).hom ≫ ι p = filtrationFunctorArrow F hF p := by
  simp only [filtrationFunctorObjIsoOfEqMk, Iso.trans_hom, eqToIso.hom, Category.assoc,
    Subobject.underlyingIso_hom_comp_eq_mk]
  exact congrArg _ (Subobject.arrow_congr _ _ ((filtrationEInt_coe F p).trans (hFι p)))

/-- Under `CochainComplex.filtrationFunctorObjIsoOfEqMk`, the transition map `F_p ⟶ F_{p+1}` of
the functor of the filtration is any map `X p ⟶ X (p + 1)` compatible with the inclusions. -/
@[reassoc]
lemma filtrationFunctor_map_comp_objIsoOfEqMk_hom (p : ℤ) (f : X p ⟶ X (p + 1))
    (hf : f ≫ ι (p + 1) = ι p) :
    (filtrationFunctor F hF).map (homOfLE (coe_le_coe_of_eq_add_one (rfl : p = p) rfl)) ≫
        (filtrationFunctorObjIsoOfEqMk F hF ι hFι (p + 1)).hom =
      (filtrationFunctorObjIsoOfEqMk F hF ι hFι p).hom ≫ f := by
  rw [← cancel_mono (ι (p + 1))]
  simp only [Category.assoc, filtrationFunctorObjIsoOfEqMk_hom_comp, hf,
    filtrationFunctor_map_comp_arrow]

/-- When each piece `F p` of a filtration is represented by a monomorphism `ι p : X p ⟶ K`, the
graded piece `F_{p+1}/F_p`, the cokernel of the transition map of the functor of the filtration,
is the target of any cokernel `g` of a map `X p ⟶ X (p + 1)` compatible with the inclusions. -/
noncomputable def cokernelFiltrationFunctorMapIsoOfIsColimit (p : ℤ) (f : X p ⟶ X (p + 1))
    (hf : f ≫ ι (p + 1) = ι p) {Q : CochainComplex C ℤ} (g : X (p + 1) ⟶ Q) (hfg : f ≫ g = 0)
    (hg : IsColimit (CokernelCofork.ofπ g hfg)) :
    cokernel ((filtrationFunctor F hF).map
      (homOfLE (coe_le_coe_of_eq_add_one (rfl : p = p) rfl))) ≅ Q :=
  cokernel.mapIso _ f (filtrationFunctorObjIsoOfEqMk F hF ι hFι p)
      (filtrationFunctorObjIsoOfEqMk F hF ι hFι (p + 1))
      (filtrationFunctor_map_comp_objIsoOfEqMk_hom F hF ι hFι p f hf) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso hg

/-- The isomorphism `CochainComplex.cokernelFiltrationFunctorMapIsoOfIsColimit` identifies the
cokernel projection with `g`. -/
@[reassoc (attr := simp)]
lemma π_cokernelFiltrationFunctorMapIsoOfIsColimit_hom (p : ℤ) (f : X p ⟶ X (p + 1))
    (hf : f ≫ ι (p + 1) = ι p) {Q : CochainComplex C ℤ} (g : X (p + 1) ⟶ Q) (hfg : f ≫ g = 0)
    (hg : IsColimit (CokernelCofork.ofπ g hfg)) :
    cokernel.π _ ≫ (cokernelFiltrationFunctorMapIsoOfIsColimit F hF ι hFι p f hf g hfg hg).hom =
      (filtrationFunctorObjIsoOfEqMk F hF ι hFι (p + 1)).hom ≫ g := by
  rw [cokernelFiltrationFunctorMapIsoOfIsColimit, Iso.trans_hom, ← Category.assoc,
    cokernel.mapIso_hom, cokernel.π_desc, Category.assoc]
  congr 1
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) hg
    WalkingParallelPair.one

end Stages

end CochainComplex
