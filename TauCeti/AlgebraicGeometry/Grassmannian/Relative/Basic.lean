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
  the colimit of the `G(k, Γ(E, U))`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isPullback_grassmannianChartMap`: for affine opens `V ≤ U`,
  `G(k, Γ(E, V))` is the part of `G(k, Γ(E, U))` over `V`; in particular `grassmannianChartMap`
  is an open immersion.
* `AlgebraicGeometry.Scheme.Modules.grassmannianChartMap_comp`: the comparison morphisms compose.
* `AlgebraicGeometry.Scheme.Modules.isPullback_grassmannianι_fromSpec`: over an affine open `U`,
  the relative Grassmannian is `G(k, Γ(E, U))` over `Spec Γ(X, U)`.
* `AlgebraicGeometry.Scheme.Modules.isIso_grassmannianι_top`: over an affine scheme `X`, the part
  over `⊤` is the whole relative Grassmannian.

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
        X.presheaf.map (homOfLE (hWV.trans hVU)).op r := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
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
-- `G(k, Γ(E, V))` with the part of `G(k, Γ(E, U))` over `V`.
private noncomputable def grassmannianGluingData : X.directedAffineCover.RelativeGluingData where
  functor := grassmannianFunctor E k
  natTrans :=
    { app (U : X.affineOpens) :=
        Module.Grassmannian.toSpec Γ(X, U.val) Γ(E, U.val) k ≫ U.property.isoSpec.inv
      naturality _ _ h := grassmannianChartMap_toSpec_isoSpec_inv E k (leOfHom h) }
  equifibered V U h :=
    (isPullback_grassmannianChartMap E k (leOfHom h)).paste_vert
      (IsAffineOpen.isPullback_SpecMap_presheaf_map_isoSpec_inv U.property V.property (leOfHom h))

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
  exact ((grassmannianGluingData E k).ι_toBase U).trans (Category.assoc _ _ _)

/-- For affine opens `V ≤ U`, the inclusion of the part over `V` factors through the inclusion of
the part over `U`. -/
@[reassoc (attr := simp)]
theorem grassmannianChartMap_grassmannianι {U V : X.affineOpens} (h : V.val ≤ U.val) :
    grassmannianChartMap E k h ≫ grassmannianι E k U = grassmannianι E k V :=
  colimit.w (grassmannianGluingData E k).functor (homOfLE h)

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
      (grassmannianι E k U) U.val.ι (grassmannianToBase E k) :=
  (grassmannianGluingData E k).isPullback_natTrans_ι_toBase U

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

/-- Over an affine scheme `X`, the part of the relative Grassmannian over the affine open `⊤` is
all of it, because `Spec Γ(X, ⊤) ⟶ X` is an isomorphism. -/
instance isIso_grassmannianι_top [IsAffine X] :
    IsIso (grassmannianι E k ⟨⊤, isAffineOpen_top X⟩) := by
  have : IsIso (isAffineOpen_top X).fromSpec := by
    rw [IsAffineOpen.fromSpec_top]
    infer_instance
  exact (isPullback_grassmannianι_fromSpec E k ⟨⊤, isAffineOpen_top X⟩).isIso_snd_of_isIso

end AlgebraicGeometry.Scheme.Modules
