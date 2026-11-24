/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.RelativeGluing
public import TauCeti.AlgebraicGeometry.AffineScheme.Basic
public import TauCeti.AlgebraicGeometry.Grassmannian.BaseChange
public import TauCeti.AlgebraicGeometry.Modules.AffineRestriction
public import TauCeti.AlgebraicGeometry.Modules.Sections

/-!
# The Grassmannian of a quasi-coherent sheaf over an arbitrary base

Let `E` be a quasi-coherent `𝒪_X`-module on a scheme `X` and `k` a natural number. This file glues
the Grassmannian schemes `G(k, Γ(E, U))` over `Spec Γ(X, U)`, for `U` ranging over the affine opens
of `X`, into the **relative Grassmannian** `AlgebraicGeometry.Scheme.Modules.grassmannian E k`, a
scheme over `X` whose part over each affine open `U` is `G(k, Γ(E, U))`
(`AlgebraicGeometry.Scheme.Modules.isPullback_grassmannianι_fromSpec`).

The gluing uses all affine opens of `X` at once, so no choice of cover or of trivialisations
enters the construction. For affine opens `V ≤ U`, restriction of sections exhibits `Γ(E, V)` as
the base change of `Γ(E, U)` along `Γ(X, U) → Γ(X, V)`
(`AlgebraicGeometry.Scheme.Modules.isBaseChange_sectionsRestrictionLinearMap`), so the
Grassmannian of `Γ(E, V)` is the fibre product `Spec Γ(X, V) ×_{Spec Γ(X, U)} G(k, Γ(E, U))`
(`IsBaseChange.isPullback_grassmannianSchemeHom`). These comparison morphisms
`AlgebraicGeometry.Scheme.Modules.grassmannianChartMap` compose, so they form a relative gluing
datum over the directed cover of `X` by its affine opens
(`AlgebraicGeometry.Scheme.Cover.RelativeGluingData`), whose glued scheme is the relative
Grassmannian.

The construction applies to every quasi-coherent `E`. For a finite locally free `E` each `Γ(E, U)`
is finite projective; the universal quotient over the glued scheme and its universal property
over arbitrary `X`-schemes are not treated here.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.grassmannianChartMap E k h`: for affine opens `V ≤ U`, the
  morphism `G(k, Γ(E, V)) ⟶ G(k, Γ(E, U))` over the restriction `Spec Γ(X, V) ⟶ Spec Γ(X, U)`.
* `AlgebraicGeometry.Scheme.Modules.grassmannian E k`: the relative Grassmannian.
* `AlgebraicGeometry.Scheme.Modules.grassmannianToBase E k`: its structure morphism to `X`.
* `AlgebraicGeometry.Scheme.Modules.grassmannianι E k U`: the inclusion of `G(k, Γ(E, U))` as the
  part over the affine open `U`.
* `AlgebraicGeometry.Scheme.Modules.grassmannianCocone E k` and
  `AlgebraicGeometry.Scheme.Modules.isColimitGrassmannianCocone E k`: the relative Grassmannian as
  the colimit of the `G(k, Γ(E, U))`, with `grassmannian_hom_ext`, `grassmannianDesc` and
  `grassmannianι_grassmannianDesc` stated directly for `grassmannian E k` and `grassmannianι`.
* `AlgebraicGeometry.Scheme.Modules.grassmannianOpenCover E k`: the open cover of the relative
  Grassmannian by the `G(k, Γ(E, U))`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isPullback_grassmannianChartMap`: for affine opens `V ≤ U`,
  `G(k, Γ(E, V))` is the part of `G(k, Γ(E, U))` over `V`; in particular `grassmannianChartMap`
  is an open immersion.
* `AlgebraicGeometry.Scheme.Modules.grassmannianChartMap_comp`: the comparison morphisms compose.
* `AlgebraicGeometry.Scheme.Modules.isPullback_grassmannianι_fromSpec`: over an affine open `U`,
  the relative Grassmannian is `G(k, Γ(E, U))` over `Spec Γ(X, U)`.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7.
* [The Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH), for relative
  gluing.
-/

public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (E : X.Modules)

variable [E.IsQuasicoherent] (k : ℕ)

/-- The Grassmannian `G(k, Γ(E, U))` of the sections of `E` over an affine open `U`, a scheme over
`Spec Γ(X, U)`. -/
noncomputable abbrev grassmannianChart (U : X.affineOpens) : Scheme.{u} :=
  Module.Grassmannian.scheme Γ(X, U.val) Γ(E, U.val) k

variable {E} in
-- For affine opens `V ≤ U`, restriction of sections is a base change along restriction of
-- functions.
private lemma isBaseChange_restriction {U V : X.affineOpens} (h : V.val ≤ U.val) :
    letI := restrictionAlgebra h
    letI := restrictionModule E h
    haveI := isScalarTower_restriction E h
    IsBaseChange Γ(X, V.val) (E.sectionsRestrictionLinearMap h fun _ ↦ rfl) :=
  letI := restrictionAlgebra h
  letI := restrictionModule E h
  haveI := isScalarTower_restriction E h
  E.isBaseChange_sectionsRestrictionLinearMap U.property V.property h _

/-- For affine opens `V ≤ U`, the morphism `G(k, Γ(E, V)) ⟶ G(k, Γ(E, U))` over the restriction
`Spec Γ(X, V) ⟶ Spec Γ(X, U)`: `Γ(E, V)` is the base change of `Γ(E, U)` along restriction of
functions, and this is `IsBaseChange.grassmannianSchemeHom` for that base change. It identifies
`G(k, Γ(E, V))` with the part of `G(k, Γ(E, U))` over `V`
(`AlgebraicGeometry.Scheme.Modules.isPullback_grassmannianChartMap`). -/
noncomputable def grassmannianChartMap {U V : X.affineOpens} (h : V.val ≤ U.val) :
    grassmannianChart E k V ⟶ grassmannianChart E k U :=
  letI := restrictionAlgebra h
  letI := restrictionModule E h
  haveI := isScalarTower_restriction E h
  (isBaseChange_restriction h).grassmannianSchemeHom k

/-- `grassmannianChartMap` is `IsBaseChange.grassmannianSchemeHom` for the base change of sections
along restriction of functions
(`AlgebraicGeometry.Scheme.Modules.isBaseChange_sectionsRestrictionLinearMap`), so
`IsBaseChange.toSchemeHom_comp_grassmannianSchemeHom` computes it on points. -/
theorem grassmannianChartMap_eq {U V : X.affineOpens} (h : V.val ≤ U.val) :
    letI := restrictionAlgebra h
    letI := restrictionModule E h
    haveI := isScalarTower_restriction E h
    grassmannianChartMap E k h =
      (E.isBaseChange_sectionsRestrictionLinearMap U.property V.property h
        fun _ ↦ rfl).grassmannianSchemeHom k :=
  (rfl)

open Module.Grassmannian TensorProduct in
/-- **`grassmannianChartMap` on points.** For affine opens `V ≤ U` and a `Γ(X, V)`-algebra `A`, the
point of `G(k, Γ(E, V))` classifying `N` followed by `grassmannianChartMap` is the point of
`G(k, Γ(E, U))` classifying the image of `N` under `A ⊗[Γ(X, V)] Γ(E, V) ≃ A ⊗[Γ(X, U)] Γ(E, U)`. -/
theorem toSchemeHom_comp_grassmannianChartMap {U V : X.affineOpens} (h : V.val ≤ U.val)
    {A : Type u} [CommRing A] [Algebra Γ(X, V.val) A] [Algebra Γ(X, U.val) A] :
    letI := restrictionAlgebra h
    letI := restrictionModule E h
    haveI := isScalarTower_restriction E h
    ∀ [IsScalarTower Γ(X, U.val) Γ(X, V.val) A] (N : G(k, A ⊗[Γ(X, V.val)] Γ(E, V.val); A)),
      toSchemeHom N ≫ grassmannianChartMap E k h =
        toSchemeHom ((E.isBaseChange_sectionsRestrictionLinearMap U.property V.property h
          fun _ ↦ rfl).grassmannianEquiv A N) := by
  intro _ N
  let _ := restrictionAlgebra h
  let _ := restrictionModule E h
  have _ := isScalarTower_restriction E h
  rw [grassmannianChartMap_eq, IsBaseChange.toSchemeHom_comp_grassmannianSchemeHom]

/-- `grassmannianChartMap` lies over the restriction `Spec Γ(X, V) ⟶ Spec Γ(X, U)`. -/
@[reassoc (attr := simp)]
theorem grassmannianChartMap_toSpec {U V : X.affineOpens} (h : V.val ≤ U.val) :
    grassmannianChartMap E k h ≫ Module.Grassmannian.toSpec Γ(X, U.val) Γ(E, U.val) k =
      Module.Grassmannian.toSpec Γ(X, V.val) Γ(E, V.val) k ≫
        Spec.map (X.presheaf.map (homOfLE h).op) := by
  let _ := restrictionAlgebra h
  let _ := restrictionModule E h
  have _ := isScalarTower_restriction E h
  rw [grassmannianChartMap_eq, IsBaseChange.grassmannianSchemeHom_toSpec,
    algebraMap_restrictionAlgebra, CommRingCat.ofHom_hom]

/-- **The Grassmannian over a smaller affine open.** For affine opens `V ≤ U`, the Grassmannian
`G(k, Γ(E, V))` is the fibre product `Spec Γ(X, V) ×_{Spec Γ(X, U)} G(k, Γ(E, U))`, with
projections `grassmannianChartMap` and the structure morphism. -/
theorem isPullback_grassmannianChartMap {U V : X.affineOpens} (h : V.val ≤ U.val) :
    IsPullback (grassmannianChartMap E k h) (Module.Grassmannian.toSpec Γ(X, V.val) Γ(E, V.val) k)
      (Module.Grassmannian.toSpec Γ(X, U.val) Γ(E, U.val) k)
      (Spec.map (X.presheaf.map (homOfLE h).op)) := by
  let _ := restrictionAlgebra h
  let _ := restrictionModule E h
  have _ := isScalarTower_restriction E h
  have hres : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.val) Γ(X, V.val))) =
      Spec.map (X.presheaf.map (homOfLE h).op) := by
    rw [algebraMap_restrictionAlgebra, CommRingCat.ofHom_hom]
  rw [grassmannianChartMap_eq, ← hres]
  exact IsBaseChange.isPullback_grassmannianSchemeHom _ k

/-- For affine opens `V ≤ U`, the comparison morphism `G(k, Γ(E, V)) ⟶ G(k, Γ(E, U))` is an open
immersion, as the base change of the open immersion `Spec Γ(X, V) ⟶ Spec Γ(X, U)`. -/
instance {U V : X.affineOpens} (h : V.val ≤ U.val) :
    IsOpenImmersion (grassmannianChartMap E k h) :=
  haveI := U.property.isOpenImmersion_SpecMap_presheaf_map V.property (homOfLE h).op
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (isPullback_grassmannianChartMap E k h).flip inferInstance

/-- **The comparison morphisms compose.** For affine opens `W ≤ V ≤ U`, the morphisms
`G(k, Γ(E, W)) ⟶ G(k, Γ(E, V)) ⟶ G(k, Γ(E, U))` compose to the morphism for `W ≤ U`. -/
@[reassoc (attr := simp)]
theorem grassmannianChartMap_comp {U V W : X.affineOpens} (hWV : W.val ≤ V.val)
    (hVU : V.val ≤ U.val) :
    grassmannianChartMap E k hWV ≫ grassmannianChartMap E k hVU =
      grassmannianChartMap E k (hWV.trans hVU) := by
  let _ := restrictionAlgebra hVU
  let _ := restrictionAlgebra hWV
  let _ := restrictionAlgebra (hWV.trans hVU)
  let _ := restrictionModule E hVU
  let _ := restrictionModule E hWV
  let _ := restrictionModule E (hWV.trans hVU)
  have _ := isScalarTower_restriction E hVU
  have _ := isScalarTower_restriction E hWV
  have _ := isScalarTower_restriction E (hWV.trans hVU)
  -- restriction of functions from `U` to `W` factors through `V`
  have hres (r : Γ(X, U.val)) :
      X.presheaf.map (homOfLE hWV).op (X.presheaf.map (homOfLE hVU).op r) =
        X.presheaf.map (homOfLE (hWV.trans hVU)).op r :=
    DFunLike.congr_fun (Scheme.presheaf_map_homOfLE_comp hWV hVU) r
  have _ : IsScalarTower Γ(X, U.val) Γ(X, V.val) Γ(X, W.val) := .of_algebraMap_eq fun r ↦ by
    rw [algebraMap_restrictionAlgebra hVU, algebraMap_restrictionAlgebra hWV,
      algebraMap_restrictionAlgebra (hWV.trans hVU), hres]
  have _ : IsScalarTower Γ(X, U.val) Γ(X, V.val) Γ(E, W.val) := .of_algebraMap_smul fun r m ↦ by
    rw [smul_restrictionModule E hWV, smul_restrictionModule E (hWV.trans hVU),
      algebraMap_restrictionAlgebra hVU, hres]
  have hf := isBaseChange_restriction (E := E) hVU
  have hg := isBaseChange_restriction (E := E) hWV
  rw [grassmannianChartMap_eq, grassmannianChartMap_eq, grassmannianChartMap_eq,
    IsBaseChange.grassmannianSchemeHom_comp hf hg (hf.comp hg)]
  refine IsBaseChange.grassmannianSchemeHom_congr _ k _ (LinearMap.ext fun s ↦ ?_)
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    sectionsRestrictionLinearMap_apply]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- For an affine open `U`, the comparison morphism of `G(k, Γ(E, U))` with itself is the
identity. -/
@[simp]
theorem grassmannianChartMap_self (U : X.affineOpens) :
    grassmannianChartMap E k (le_refl U.val) = 𝟙 _ := by
  -- the morphism is an idempotent isomorphism, as the base change of the identity
  have : IsIso (Spec.map (X.presheaf.map (homOfLE (le_refl U.val)).op)) := by
    simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id]
    infer_instance
  have := (isPullback_grassmannianChartMap E k (le_refl U.val)).isIso_fst_of_isIso
  rw [← cancel_mono (grassmannianChartMap E k (le_refl U.val)), grassmannianChartMap_comp,
    Category.id_comp]

/-- The Grassmannians `G(k, Γ(E, U))` of the sections of `E` over the affine opens `U` of `X`, as
a functor on the directed cover of `X` by its affine opens. -/
noncomputable def grassmannianFunctor : X.directedAffineCover.I₀ ⥤ Scheme.{u} where
  obj U := grassmannianChart E k U
  map h := grassmannianChartMap E k (leOfHom h)
  map_id U := grassmannianChartMap_self E k U
  map_comp h h' := (grassmannianChartMap_comp E k (leOfHom h) (leOfHom h')).symm

/-- The value of `grassmannianFunctor` at an affine open `U` is `G(k, Γ(E, U))`. -/
theorem grassmannianFunctor_obj (U : X.directedAffineCover.I₀) :
    (grassmannianFunctor E k).obj U = grassmannianChart E k U :=
  (rfl)

/-- The value of `grassmannianFunctor` on `V ≤ U` is `grassmannianChartMap`, up to the
identification `grassmannianFunctor_obj` of its values. -/
theorem grassmannianFunctor_map {U V : X.directedAffineCover.I₀} (h : U ⟶ V) :
    (grassmannianFunctor E k).map h = eqToHom (grassmannianFunctor_obj E k U) ≫
      grassmannianChartMap E k (leOfHom h) ≫ eqToHom (grassmannianFunctor_obj E k V).symm := by
  -- by definition `grassmannianFunctor` sends `h` to `grassmannianChartMap`, and the two
  -- `eqToHom` are identities because `grassmannianFunctor_obj` holds by definition
  change grassmannianChartMap E k (leOfHom h) = 𝟙 _ ≫ grassmannianChartMap E k (leOfHom h) ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]

-- The naturality square of the structure morphisms `G(k, Γ(E, U)) ⟶ U`.
private lemma grassmannianChartMap_toSpec_isoSpec_inv {U V : X.affineOpens} (h : V.val ≤ U.val) :
    grassmannianChartMap E k h ≫ Module.Grassmannian.toSpec Γ(X, U.val) Γ(E, U.val) k ≫
        U.property.isoSpec.inv =
      (Module.Grassmannian.toSpec Γ(X, V.val) Γ(E, V.val) k ≫ V.property.isoSpec.inv) ≫
        X.homOfLE h := by
  rw [grassmannianChartMap_toSpec_assoc,
    IsAffineOpen.SpecMap_presheaf_map_comp_isoSpec_inv U.property V.property h, Category.assoc]

-- The relative gluing datum of the Grassmannian: the Grassmannians `G(k, Γ(E, U))` over the
-- affine opens `U ≅ Spec Γ(X, U)` of `X`, with the comparison morphisms for `V ≤ U`, which identify
-- `G(k, Γ(E, V))` with the part of `G(k, Γ(E, U))` over `V`. In `naturality` and `equifibered`,
-- the functor `X.directedAffineCover.functorOfLocallyDirected` sends `V ≤ U` to `X.homOfLE`
-- between the affine opens and `grassmannianFunctor` sends it to `grassmannianChartMap`, both by
-- definition, so the stated squares are the required ones.
private noncomputable def grassmannianGluingData : X.directedAffineCover.RelativeGluingData where
  functor := grassmannianFunctor E k
  natTrans :=
    { app (U : X.affineOpens) :=
        Module.Grassmannian.toSpec Γ(X, U.val) Γ(E, U.val) k ≫ U.property.isoSpec.inv
      naturality _ _ h := grassmannianChartMap_toSpec_isoSpec_inv E k (leOfHom h) }
  equifibered V U h :=
    (isPullback_grassmannianChartMap E k (leOfHom h)).paste_vert
      (IsAffineOpen.isPullback_SpecMap_presheaf_map_isoSpec_inv U.property V.property (leOfHom h))

-- The functor of the gluing datum sends `V ≤ U` to `grassmannianChartMap`, by definition of
-- `grassmannianFunctor`.
private lemma grassmannianGluingData_functor_map {U V : X.affineOpens} (h : V.val ≤ U.val) :
    (grassmannianGluingData E k).functor.map (homOfLE h) = grassmannianChartMap E k h :=
  rfl

-- The structure morphisms of the gluing datum are `G(k, Γ(E, U)) ⟶ Spec Γ(X, U) ≅ U`, by
-- definition.
private lemma grassmannianGluingData_natTrans_app (U : X.affineOpens) :
    (grassmannianGluingData E k).natTrans.app U =
      Module.Grassmannian.toSpec Γ(X, U.val) Γ(E, U.val) k ≫ U.property.isoSpec.inv :=
  rfl

-- The directed affine cover of `X` maps the affine open `U` to `X` by its inclusion, by
-- definition of `Scheme.directedAffineCover`.
private lemma directedAffineCover_f (U : X.affineOpens) : X.directedAffineCover.f U = U.val.ι :=
  rfl

/-- The **relative Grassmannian** of a quasi-coherent `𝒪_X`-module `E`: the scheme over `X` glued
from the Grassmannians `G(k, Γ(E, U))` over the affine opens `U ≅ Spec Γ(X, U)` of `X`. Its part
over an affine open `U` is `G(k, Γ(E, U))`
(`AlgebraicGeometry.Scheme.Modules.isPullback_grassmannianι_fromSpec`). -/
noncomputable def grassmannian : Scheme.{u} :=
  (grassmannianGluingData E k).glued

/-- The structure morphism of the relative Grassmannian to `X`. -/
noncomputable def grassmannianToBase : grassmannian E k ⟶ X :=
  (grassmannianGluingData E k).toBase

/-- The inclusion of the Grassmannian `G(k, Γ(E, U))` of the sections over an affine open `U` into
the relative Grassmannian, as the part over `U`. -/
noncomputable def grassmannianι (U : X.affineOpens) :
    grassmannianChart E k U ⟶ grassmannian E k :=
  colimit.ι (grassmannianGluingData E k).functor U

/-- On the part over an affine open `U`, the structure morphism of the relative Grassmannian is the
structure morphism of `G(k, Γ(E, U))` followed by `Spec Γ(X, U) ≅ U ⟶ X`. -/
@[reassoc (attr := simp)]
theorem grassmannianι_toBase (U : X.affineOpens) :
    grassmannianι E k U ≫ grassmannianToBase E k =
      Module.Grassmannian.toSpec Γ(X, U.val) Γ(E, U.val) k ≫ U.property.fromSpec := by
  have h := (grassmannianGluingData E k).ι_toBase U
  rw [grassmannianGluingData_natTrans_app, directedAffineCover_f] at h
  have h' : (Module.Grassmannian.toSpec Γ(X, U.val) Γ(E, U.val) k ≫ U.property.isoSpec.inv) ≫
      U.val.ι = Module.Grassmannian.toSpec Γ(X, U.val) Γ(E, U.val) k ≫ U.property.fromSpec :=
    (Category.assoc _ _ _).trans (congrArg _ (IsAffineOpen.isoSpec_inv_ι U.property))
  exact h.trans h'

/-- For affine opens `V ≤ U`, the inclusion of the part over `V` factors through the inclusion of
the part over `U`. -/
@[reassoc (attr := simp)]
theorem grassmannianChartMap_grassmannianι {U V : X.affineOpens} (h : V.val ≤ U.val) :
    grassmannianChartMap E k h ≫ grassmannianι E k U = grassmannianι E k V := by
  rw [← grassmannianGluingData_functor_map, grassmannianι, grassmannianι]
  exact colimit.w (grassmannianGluingData E k).functor (homOfLE h)

/-- **Extensionality for the relative Grassmannian.** Two morphisms out of the relative
Grassmannian are equal if they agree on the part `G(k, Γ(E, U))` over every affine open `U`. -/
@[ext]
theorem grassmannian_hom_ext {Y : Scheme.{u}} {f g : grassmannian E k ⟶ Y}
    (h : ∀ U : X.affineOpens, grassmannianι E k U ≫ f = grassmannianι E k U ≫ g) : f = g :=
  colimit.hom_ext h

/-- The relative Grassmannian as the colimit of the Grassmannians `G(k, Γ(E, U))` over the affine
opens `U` of `X`: the colimit cocone of `grassmannianFunctor`, with vertex `grassmannian E k`
(`AlgebraicGeometry.Scheme.Modules.grassmannianCocone_pt`) and legs `grassmannianι E k U`
(`AlgebraicGeometry.Scheme.Modules.grassmannianCocone_ι_app`). -/
noncomputable def grassmannianCocone : Cocone (grassmannianFunctor E k) :=
  colimit.cocone (grassmannianGluingData E k).functor

/-- `grassmannianCocone` is a colimit cocone: morphisms out of the relative Grassmannian are
determined by, and can be assembled from, compatible morphisms out of the `G(k, Γ(E, U))`. -/
noncomputable def isColimitGrassmannianCocone : IsColimit (grassmannianCocone E k) :=
  colimit.isColimit (grassmannianGluingData E k).functor

/-- **The universal property of the relative Grassmannian.** Morphisms out of the
`G(k, Γ(E, U))`, for `U` ranging over the affine opens of `X`, compatible with the comparison
morphisms `grassmannianChartMap`, glue to a morphism out of the relative Grassmannian
(`AlgebraicGeometry.Scheme.Modules.grassmannianι_grassmannianDesc`). -/
noncomputable def grassmannianDesc {Y : Scheme.{u}}
    (f : ∀ U : X.affineOpens, grassmannianChart E k U ⟶ Y)
    (hf : ∀ {U V : X.affineOpens} (h : V.val ≤ U.val), grassmannianChartMap E k h ≫ f U = f V) :
    grassmannian E k ⟶ Y :=
  (isColimitGrassmannianCocone E k).desc
    { pt := Y
      ι :=
        { app := f
          -- `grassmannianFunctor` sends `h : V ⟶ U` to `grassmannianChartMap`, by definition
          naturality := fun _ U h ↦
            (congrArg (· ≫ f U) (grassmannianGluingData_functor_map E k (leOfHom h))).trans
              ((hf (leOfHom h)).trans (Category.comp_id _).symm) } }

/-- `grassmannianDesc` restricts to the given morphism on the part over each affine open. -/
@[reassoc (attr := simp)]
theorem grassmannianι_grassmannianDesc {Y : Scheme.{u}}
    (f : ∀ U : X.affineOpens, grassmannianChart E k U ⟶ Y)
    (hf : ∀ {U V : X.affineOpens} (h : V.val ≤ U.val), grassmannianChartMap E k h ≫ f U = f V)
    (U : X.affineOpens) : grassmannianι E k U ≫ grassmannianDesc E k f hf = f U :=
  -- the legs of `grassmannianCocone` are the `grassmannianι`, by definition
  (isColimitGrassmannianCocone E k).fac _ U

/-- The vertex of `grassmannianCocone` is the relative Grassmannian. -/
theorem grassmannianCocone_pt : (grassmannianCocone E k).pt = grassmannian E k :=
  (rfl)

/-- The legs of `grassmannianCocone` are the inclusions `grassmannianι`, up to the
identifications `grassmannianFunctor_obj` and `grassmannianCocone_pt`. -/
theorem grassmannianCocone_ι_app (U : X.directedAffineCover.I₀) :
    (grassmannianCocone E k).ι.app U = eqToHom (grassmannianFunctor_obj E k U) ≫
      grassmannianι E k U ≫ eqToHom (grassmannianCocone_pt E k).symm := by
  -- by definition the legs of the colimit cocone are the inclusions `grassmannianι`, and the two
  -- `eqToHom` are identities because both identifications hold by definition
  change grassmannianι E k U = 𝟙 _ ≫ grassmannianι E k U ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]

/-- **The relative Grassmannian over an affine open.** For an affine open `U` of `X`, the part of
the relative Grassmannian over `U` is `G(k, Γ(E, U))`: the square formed by the inclusion of
`U ≅ Spec Γ(X, U)` and the structure morphisms is a pullback square. -/
theorem isPullback_grassmannianι (U : X.affineOpens) :
    IsPullback (Module.Grassmannian.toSpec Γ(X, U.val) Γ(E, U.val) k ≫ U.property.isoSpec.inv)
      (grassmannianι E k U) U.val.ι (grassmannianToBase E k) := by
  rw [← grassmannianGluingData_natTrans_app, ← directedAffineCover_f]
  exact (grassmannianGluingData E k).isPullback_natTrans_ι_toBase U

/-- The inclusion `grassmannianι E k U` of the part of the relative Grassmannian over an affine
open `U` is an open immersion, as the base change of the open immersion `U ⟶ X`. -/
instance (U : X.affineOpens) : IsOpenImmersion (grassmannianι E k U) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_grassmannianι E k U)
    inferInstance

/-- **The relative Grassmannian over an affine open**, with base `Spec Γ(X, U)`: the square formed
by `Spec Γ(X, U) ⟶ X` and the structure morphisms is a pullback square. -/
theorem isPullback_grassmannianι_fromSpec (U : X.affineOpens) :
    IsPullback (Module.Grassmannian.toSpec Γ(X, U.val) Γ(E, U.val) k) (grassmannianι E k U)
      U.property.fromSpec (grassmannianToBase E k) :=
  (isPullback_grassmannianι E k U).of_iso (Iso.refl _) U.property.isoSpec (Iso.refl _) (Iso.refl _)
    (by simp) (by simp)
    (by rw [Iso.refl_hom, Category.comp_id]; exact (IsAffineOpen.isoSpec_hom_fromSpec _).symm)
    (by simp)

/-- Every point of the relative Grassmannian lies in the part over some affine open. -/
theorem exists_grassmannianι_eq (x : grassmannian E k) :
    ∃ (U : X.affineOpens) (y : grassmannianChart E k U), grassmannianι E k U y = x :=
  (grassmannianGluingData E k).cover.exists_eq x

/-- The open cover of the relative Grassmannian by its parts `G(k, Γ(E, U))` over the affine opens
`U` of `X`, with maps `grassmannianι`. -/
@[expose]
noncomputable def grassmannianOpenCover : (grassmannian E k).OpenCover :=
  .mkOfCovers X.affineOpens (grassmannianChart E k) (grassmannianι E k)
    (exists_grassmannianι_eq E k)

/-- The parts of `grassmannianOpenCover` are the `G(k, Γ(E, U))`. -/
@[simp]
theorem grassmannianOpenCover_X (U : X.affineOpens) :
    (grassmannianOpenCover E k).X U = grassmannianChart E k U :=
  rfl

/-- The maps of `grassmannianOpenCover` are the inclusions `grassmannianι`. -/
@[simp]
theorem grassmannianOpenCover_f (U : X.affineOpens) :
    (grassmannianOpenCover E k).f U = grassmannianι E k U :=
  rfl

end AlgebraicGeometry.Scheme.Modules
