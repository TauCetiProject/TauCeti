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

* `CochainComplex.spectralObjectHIso`: `H^n(f)` is the cohomology of the mapping cone of
  `F.map f`.
* `CochainComplex.spectralObjectHIsoCokernel`: for a monomorphism `F.map f`, `H^n(f)` is the
  cohomology of the cokernel of `F.map f`.
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
    exact quotient_mappingConeCompTriangle_mor₃_naturality (F.map f) (F.map g) (G.map f)
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

/-- The map `F_⊥ ⟶ F_⊤` of the functor of a filtration vanishes, its source being zero. -/
lemma filtrationFunctor_map_bot_top :
    (filtrationFunctor F hF).map (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)) = 0 := by
  refine IsZero.eq_of_src ?_ _ _
  rw [filtrationFunctor_obj, filtrationEInt_bot]
  exact IsZero.of_iso (isZero_zero _) Subobject.botCoeIsoZero

instance {a b : EInt} (f : a ⟶ b) : Mono ((filtrationFunctor F hF).map f) :=
  inferInstanceAs (Mono (Subobject.ofLE _ _ (monotone_filtrationEInt F hF (leOfHom f))))

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

end CochainComplex
