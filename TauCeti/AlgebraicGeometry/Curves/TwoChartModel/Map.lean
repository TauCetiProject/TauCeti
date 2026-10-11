/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
public import TauCeti.FieldTheory.FunctionField.HolomorphyRing.Extension
import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# The morphism of two-chart models induced by an extension of function fields

Let `F' / F` be an integral extension of algebraic function fields over `k`, let `x ∈ F` be
nonzero, and let `x' ∈ F'` be its image. A place of `F'` at which `x'` is regular lies over a
place of `F` at which `x` is regular, so `F → F'` maps the holomorphy ring `𝒪_x` of `F` into the
holomorphy ring `𝒪_{x'}` of `F'`, and likewise `𝒪_{x⁻¹}` into `𝒪_{x'⁻¹}` and the overlap ring into
the overlap ring. For `x` transcendental over `k`, on the finite charts this is the inclusion of
the integral closure of `k[x]` in `F` into the integral closure of `k[x]` in `F'`. Taking spectra,
the two chart maps agree on the overlap, so they glue to a morphism of schemes over `k`

`twoChartModel hF' hx' ⟶ twoChartModel hF hx`

(`TauCeti.AlgebraicGeometry.twoChartModel.map`). It is dominant, and for `x` transcendental over
`k` the pullback of rational functions along it is `F → F'`, read through the identifications of
the function fields of the two models with `F` and `F'`. The construction is functorial: the
identity of `F` induces the identity, and a tower `F → F' → F''` induces the composite.

For `x` transcendental over `k`, this is the morphism of normalized models of the projective line
attached to an embedding of function fields, the morphism part of the correspondence between
function fields and regular projective curves.

## Main definitions

* `TauCeti.AlgebraicGeometry.twoChartModel.finiteChartMap`,
  `TauCeti.AlgebraicGeometry.twoChartModel.infinityChartMap`: the maps `𝒪_x → 𝒪_{x'}` and
  `𝒪_{x⁻¹} → 𝒪_{x'⁻¹}` of chart rings induced by `F → F'`.
* `TauCeti.AlgebraicGeometry.twoChartModel.map`: the morphism of two-chart models induced by
  `F → F'`.

## Main results

* `TauCeti.AlgebraicGeometry.twoChartModel.ιFinite_map` and
  `TauCeti.AlgebraicGeometry.twoChartModel.ιInfinity_map`: on each chart, `map` is `Spec` of the
  chart map.
* the instances `(map …).IsOver (Spec k)` and `IsDominant (map …)`.
* `TauCeti.AlgebraicGeometry.twoChartModel.functionFieldEquiv_functionFieldMap_map`: the pullback
  of rational functions along `map` is `F → F'`.
* `TauCeti.AlgebraicGeometry.twoChartModel.map_id` and
  `TauCeti.AlgebraicGeometry.twoChartModel.map_comp`: functoriality.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.2 and Appendix B.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section I.6 (the morphism of
  abstract nonsingular curves attached to an embedding of function fields).
-/

public section

open CategoryTheory Limits _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

namespace twoChartModel

variable {k F F' : Type u} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']
  [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']

/-! ### The chart maps -/

/-- The map `𝒪_x → 𝒪_{x'}` of finite charts induced by `F → F'`, where `x'` is the image of `x`:
a place of `F'` at which `x'` is regular lies over a place of `F` at which `x` is regular. -/
noncomputable def finiteChartMap {x : F} {x' : F'} (h : algebraMap F F' x = x') :
    holomorphyRing {P : Place k F | x ∈ P.integers} →+*
      holomorphyRing {P' : Place k F' | x' ∈ P'.integers} :=
  holomorphyRingMap fun P' hP' ↦ (Place.mem_integers_restrict_iff k F P' x).mpr (h ▸ hP')

@[simp]
theorem coe_finiteChartMap_apply {x : F} {x' : F'} (h : algebraMap F F' x = x')
    (z : holomorphyRing {P : Place k F | x ∈ P.integers}) :
    (finiteChartMap h z : F') = algebraMap F F' z :=
  coe_holomorphyRingMap_apply _ z

/-- The map `𝒪_{x⁻¹} → 𝒪_{x'⁻¹}` of charts at infinity induced by `F → F'`, where `x'` is the
image of `x`. -/
noncomputable def infinityChartMap {x : F} {x' : F'} (h : algebraMap F F' x = x') :
    holomorphyRing {P : Place k F | x⁻¹ ∈ P.integers} →+*
      holomorphyRing {P' : Place k F' | x'⁻¹ ∈ P'.integers} :=
  holomorphyRingMap fun P' hP' ↦
    (Place.mem_integers_restrict_iff k F P' x⁻¹).mpr (by rwa [map_inv₀, h])

@[simp]
theorem coe_infinityChartMap_apply {x : F} {x' : F'} (h : algebraMap F F' x = x')
    (z : holomorphyRing {P : Place k F | x⁻¹ ∈ P.integers}) :
    (infinityChartMap h z : F') = algebraMap F F' z :=
  coe_holomorphyRingMap_apply _ z

/-- The map of overlap rings `𝒪_{x, x⁻¹} → 𝒪_{x', x'⁻¹}` induced by `F → F'`. -/
private noncomputable def overlapMap {x : F} {x' : F'} (h : algebraMap F F' x = x') :
    holomorphyRing ({P : Place k F | x ∈ P.integers} ∩ {P : Place k F | x⁻¹ ∈ P.integers}) →+*
      holomorphyRing
        ({P' : Place k F' | x' ∈ P'.integers} ∩ {P' : Place k F' | x'⁻¹ ∈ P'.integers}) :=
  holomorphyRingMap fun P' hP' ↦
    ⟨(Place.mem_integers_restrict_iff k F P' x).mpr (h ▸ hP'.1),
      (Place.mem_integers_restrict_iff k F P' x⁻¹).mpr (by rw [map_inv₀, h]; exact hP'.2)⟩

@[simp]
private theorem coe_overlapMap_apply {x : F} {x' : F'} (h : algebraMap F F' x = x')
    (z : holomorphyRing
      ({P : Place k F | x ∈ P.integers} ∩ {P : Place k F | x⁻¹ ∈ P.integers})) :
    (overlapMap h z : F') = algebraMap F F' z :=
  coe_holomorphyRingMap_apply _ z

/-! ### The morphism of models -/

variable (hF : IsFunctionField k F) (hF' : IsFunctionField k F') {x : F} (hx : x ≠ 0)
  {x' : F'} (hx' : x' ≠ 0) (h : algebraMap F F' x = x')

/-- The chart maps of `F → F'` agree on the overlap: restricting `Spec 𝒪_{x'} → Spec 𝒪_x` and
`Spec 𝒪_{x'⁻¹} → Spec 𝒪_{x⁻¹}` to `Spec 𝒪_{x', x'⁻¹}` and gluing gives the same morphism. -/
private theorem specMap_finiteChartMap_ιFinite_eq :
    Spec.map (CommRingCat.ofHom (finiteChartRestriction (k := k) x').toRingHom) ≫
        Spec.map (CommRingCat.ofHom (finiteChartMap h)) ≫ ιFinite hF hx =
      Spec.map (CommRingCat.ofHom (infinityChartRestriction (k := k) x').toRingHom) ≫
        Spec.map (CommRingCat.ofHom (infinityChartMap h)) ≫ ιInfinity hF hx := by
  -- Both composites factor through `Spec` of the map of overlap rings.
  have hfin : Spec.map (CommRingCat.ofHom (finiteChartRestriction (k := k) x').toRingHom) ≫
        Spec.map (CommRingCat.ofHom (finiteChartMap h)) =
      Spec.map (CommRingCat.ofHom (overlapMap h)) ≫
        Spec.map (CommRingCat.ofHom (finiteChartRestriction (k := k) x).toRingHom) := by
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun _ ↦ Subtype.ext (by simp)
  have hinf : Spec.map (CommRingCat.ofHom (infinityChartRestriction (k := k) x').toRingHom) ≫
        Spec.map (CommRingCat.ofHom (infinityChartMap h)) =
      Spec.map (CommRingCat.ofHom (overlapMap h)) ≫
        Spec.map (CommRingCat.ofHom (infinityChartRestriction (k := k) x).toRingHom) := by
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun _ ↦ Subtype.ext (by simp)
  calc _ = Spec.map (CommRingCat.ofHom (overlapMap h)) ≫
        Spec.map (CommRingCat.ofHom (finiteChartRestriction (k := k) x).toRingHom) ≫
          ιFinite hF hx := by rw [reassoc_of% hfin]
    _ = Spec.map (CommRingCat.ofHom (overlapMap h)) ≫
        Spec.map (CommRingCat.ofHom (infinityChartRestriction (k := k) x).toRingHom) ≫
          ιInfinity hF hx := by rw [condition]
    _ = _ := by rw [reassoc_of% hinf]

/-- **The morphism of two-chart models induced by `F → F'`**: for `x' ∈ F'` the image of
`x ∈ F`, the morphism `twoChartModel hF' hx' ⟶ twoChartModel hF hx` glued from `Spec` of the
chart maps `𝒪_x → 𝒪_{x'}` and `𝒪_{x⁻¹} → 𝒪_{x'⁻¹}`. -/
noncomputable def map : twoChartModel hF' hx' ⟶ twoChartModel hF hx :=
  (isPushout hF' hx').desc (Spec.map (CommRingCat.ofHom (finiteChartMap h)) ≫ ιFinite hF hx)
    (Spec.map (CommRingCat.ofHom (infinityChartMap h)) ≫ ιInfinity hF hx)
    (specMap_finiteChartMap_ιFinite_eq hF hx h)

/-- On the finite chart, `map` is `Spec` of the map `𝒪_x → 𝒪_{x'}`. -/
@[reassoc (attr := simp)]
theorem ιFinite_map : ιFinite hF' hx' ≫ map hF hF' hx hx' h =
    Spec.map (CommRingCat.ofHom (finiteChartMap h)) ≫ ιFinite hF hx :=
  (isPushout hF' hx').inl_desc _ _ _

/-- On the chart at infinity, `map` is `Spec` of the map `𝒪_{x⁻¹} → 𝒪_{x'⁻¹}`. -/
@[reassoc (attr := simp)]
theorem ιInfinity_map : ιInfinity hF' hx' ≫ map hF hF' hx hx' h =
    Spec.map (CommRingCat.ofHom (infinityChartMap h)) ≫ ιInfinity hF hx :=
  (isPushout hF' hx').inr_desc _ _ _

/-- `map` is a morphism of schemes over `k`. -/
instance : (map hF hF' hx hx' h).IsOver (Spec (.of k)) := by
  rw [Scheme.Hom.isOver_iff]
  refine (isPushout hF' hx').hom_ext ?_ ?_
  · rw [ιFinite_map_assoc, ιFinite_over, ιFinite_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun c ↦ Subtype.ext (by simp [IsScalarTower.algebraMap_apply k F F'])
  · rw [ιInfinity_map_assoc, ιInfinity_over, ιInfinity_over, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun c ↦ Subtype.ext (by simp [IsScalarTower.algebraMap_apply k F F'])

/-- `map` is dominant: the finite chart of `twoChartModel hF' hx'` is dense, and on it `map` is
`Spec` of the injective map `𝒪_x → 𝒪_{x'}` followed by an open immersion with dense image. -/
instance : IsDominant (map hF hF' hx hx' h) := by
  have : IsDominant (Spec.map (CommRingCat.ofHom (finiteChartMap (k := k) h))) :=
    ⟨RingHom.denseRange_comap_of_injective _ (holomorphyRingMap_injective _)⟩
  have : IsDominant (ιFinite hF hx) :=
    ⟨(ιFinite hF hx).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  have : IsDominant (ιFinite hF' hx' ≫ map hF hF' hx hx' h) := by
    rw [ιFinite_map]
    infer_instance
  exact IsDominant.of_comp (ιFinite hF' hx') _

/-! ### Functions on the finite charts and the function field -/

/-- `map` sends the finite chart of `twoChartModel hF' hx'` into the finite chart of
`twoChartModel hF hx`. -/
theorem image_ιFinite_top_le_preimage_map :
    ιFinite hF' hx' ''ᵁ ⊤ ≤ map hF hF' hx hx' h ⁻¹ᵁ (ιFinite hF hx ''ᵁ ⊤) := by
  rintro _ ⟨p, -, rfl⟩
  refine ⟨Spec.map (CommRingCat.ofHom (finiteChartMap h)) p, trivial, ?_⟩
  have hp := congr($(ιFinite_map hF hF' hx hx' h) p)
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hp
  exact hp.symm

/-- **On the finite charts, `map` acts on functions as `F → F'`**: pulling a function of `𝒪_x`
back along `map` and restricting it to the finite chart of `twoChartModel hF' hx'` gives its image
in `𝒪_{x'}`. -/
theorem finiteChartSectionsEquiv_map_appLE (s : Γ(twoChartModel hF hx, ιFinite hF hx ''ᵁ ⊤)) :
    finiteChartSectionsEquiv hF' hx' ((map hF hF' hx hx' h).appLE _ _
        (image_ιFinite_top_le_preimage_map hF hF' hx hx' h) s) =
      finiteChartMap h (finiteChartSectionsEquiv hF hx s) := by
  suffices e : (map hF hF' hx hx' h).appLE _ _ (image_ιFinite_top_le_preimage_map hF hF' hx hx' h) ≫
        ((ιFinite hF' hx').appIso ⊤).hom ≫ (Scheme.ΓSpecIso _).hom =
      ((ιFinite hF hx).appIso ⊤).hom ≫ (Scheme.ΓSpecIso _).hom ≫
        CommRingCat.ofHom (finiteChartMap h) by
    simpa only [finiteChartSectionsEquiv_apply, CategoryTheory.comp_apply,
      CommRingCat.hom_ofHom] using congr($e s)
  -- Equal morphisms have equal maps on sections, whatever the proof that the opens match.
  have appLE_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (hfg : f = g) (U V e) :
      f.appLE U V e = g.appLE U V (hfg ▸ e) := by
    subst hfg
    rfl
  have hle : ⊤ ≤ (Spec.map (CommRingCat.ofHom (finiteChartMap h)) ≫ ιFinite hF hx) ⁻¹ᵁ
      (ιFinite hF hx ''ᵁ ⊤) := by
    rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq]
    exact le_top
  calc _ = (ιFinite hF' hx' ≫ map hF hF' hx hx' h).appLE (ιFinite hF hx ''ᵁ ⊤) ⊤
          (ιFinite_map hF hF' hx hx' h ▸ hle) ≫ (Scheme.ΓSpecIso _).hom := by
        rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE_assoc]
    _ = (Spec.map (CommRingCat.ofHom (finiteChartMap h)) ≫ ιFinite hF hx).appLE
          (ιFinite hF hx ''ᵁ ⊤) ⊤ hle ≫ (Scheme.ΓSpecIso _).hom := by
        rw [appLE_eq (ιFinite_map hF hF' hx hx' h)]
    _ = ((ιFinite hF hx).appIso ⊤).hom ≫
          (Spec.map (CommRingCat.ofHom (finiteChartMap h))).appTop ≫ (Scheme.ΓSpecIso _).hom := by
        rw [← Scheme.Hom.appLE_comp_appLE (Spec.map _) (ιFinite hF hx) _ ⊤ ⊤
            (Scheme.Hom.preimage_image_eq _ _).ge le_top, Category.assoc,
          show Scheme.Hom.appLE _ ⊤ ⊤ le_top = Scheme.Hom.appTop _ from Scheme.Hom.appLE_eq_app _,
          Scheme.Hom.appIso_hom']
    _ = _ := by rw [Scheme.ΓSpecIso_naturality]

/-- **The pullback of rational functions along `map` is `F → F'`**: for `x` transcendental over
`k`, under the identifications `k(X) ≃ F` and `k(X') ≃ F'` of the function fields of the two
models, the pullback along `map : X' ⟶ X` is the algebra map `F → F'`. -/
@[simp]
theorem functionFieldEquiv_functionFieldMap_map (hxt : Transcendental k x) (z : F) :
    functionFieldEquiv (h ▸ (transcendental_algebraMap_iff (algebraMap F F').injective).mpr hxt)
      ((map hF hF' hx hx' h).functionFieldMap ((functionFieldEquiv hxt).symm z)) =
      algebraMap F F' z := by
  have hxt' : Transcendental k x' :=
    h ▸ (transcendental_algebraMap_iff (algebraMap F F').injective).mpr hxt
  -- On a function `a` of `𝒪_x`: `a` is the germ of a section `s` over the finite chart, its
  -- pullback is the germ of the pulled-back section, and that section restricts on the finite
  -- chart of the other model to the image of `a` (`finiteChartSectionsEquiv_map_appLE`).
  have hsec (s : Γ(twoChartModel hF hx, ιFinite hF hx ''ᵁ ⊤)) :
      functionFieldEquiv hxt' ((map hF hF' hx hx' h).functionFieldMap
        ((functionFieldEquiv hxt).symm (finiteChartSectionsEquiv hF hx s))) =
        algebraMap F F' (finiteChartSectionsEquiv hF hx s) := by
    have hgerm : (functionFieldEquiv hxt).symm (finiteChartSectionsEquiv hF hx s : F) =
        (twoChartModel hF hx).germToFunctionField _ s := by
      rw [← functionFieldEquiv_germToFunctionField hxt s, AlgEquiv.symm_apply_apply]
    have hmap := congr($(Scheme.Hom.germToFunctionField_functionFieldMap (map hF hF' hx hx' h)
      (ιFinite hF hx ''ᵁ ⊤)) s)
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hmap
    have hres : (twoChartModel hF' hx').germToFunctionField _
          ((map hF hF' hx hx' h).app (ιFinite hF hx ''ᵁ ⊤) s) =
        (twoChartModel hF' hx').germToFunctionField _ ((map hF hF' hx hx' h).appLE _ _
          (image_ιFinite_top_le_preimage_map hF hF' hx hx' h) s) := by
      rw [Scheme.Hom.appLE, CategoryTheory.comp_apply, TopCat.Presheaf.germ_res_apply]
    rw [hgerm, hmap, hres, functionFieldEquiv_germToFunctionField,
      finiteChartSectionsEquiv_map_appLE, coe_finiteChartMap_apply]
  -- `F` is the fraction field of `𝒪_x`, and both sides are ring homomorphisms in `z`.
  have := isFractionRing_holomorphyRing_setOf_mem hF hxt
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective
    (A := holomorphyRing {P : Place k F | x ∈ P.integers}) z
  obtain ⟨s, rfl⟩ := (finiteChartSectionsEquiv hF hx).surjective a
  obtain ⟨t, rfl⟩ := (finiteChartSectionsEquiv hF hx).surjective b
  simp only [map_div₀, Subalgebra.algebraMap_apply, hsec]

/-! ### Functoriality -/

/-- The identity of `F` induces the identity of `twoChartModel hF hx`. -/
@[simp]
theorem map_id (h : algebraMap F F x = x) : map hF hF hx hx h = 𝟙 _ := by
  have hfin : CommRingCat.ofHom (finiteChartMap (k := k) h) = 𝟙 _ :=
    CommRingCat.hom_ext (RingHom.ext fun _ ↦ Subtype.ext (by simp))
  have hinf : CommRingCat.ofHom (infinityChartMap (k := k) h) = 𝟙 _ :=
    CommRingCat.hom_ext (RingHom.ext fun _ ↦ Subtype.ext (by simp))
  refine (isPushout hF hx).hom_ext ?_ ?_
  · rw [ιFinite_map, hfin, Spec.map_id, Category.id_comp, Category.comp_id]
  · rw [ιInfinity_map, hinf, Spec.map_id, Category.id_comp, Category.comp_id]

variable {F'' : Type u} [Field F''] [Algebra k F''] [Algebra F' F''] [Algebra F F'']
  [IsScalarTower k F' F''] [IsScalarTower k F F''] [IsScalarTower F F' F'']
  [Algebra.IsIntegral F' F''] [Algebra.IsIntegral F F''] (hF'' : IsFunctionField k F'')
  {x'' : F''} (hx'' : x'' ≠ 0)

/-- A tower `F → F' → F''` induces the composite of the morphisms of two-chart models. -/
@[reassoc]
theorem map_comp (h' : algebraMap F' F'' x' = x'') (h'' : algebraMap F F'' x = x'') :
    map hF' hF'' hx' hx'' h' ≫ map hF hF' hx hx' h = map hF hF'' hx hx'' h'' := by
  refine (isPushout hF'' hx'').hom_ext ?_ ?_
  · rw [ιFinite_map_assoc, ιFinite_map, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      ιFinite_map]
    congr 3
    exact RingHom.ext fun z ↦ Subtype.ext (by simp [IsScalarTower.algebraMap_apply F F' F''])
  · rw [ιInfinity_map_assoc, ιInfinity_map, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      ιInfinity_map]
    congr 3
    exact RingHom.ext fun z ↦ Subtype.ext (by simp [IsScalarTower.algebraMap_apply F F' F''])

end twoChartModel

end TauCeti.AlgebraicGeometry
