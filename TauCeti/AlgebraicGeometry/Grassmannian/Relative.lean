/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.RelativeGluing
public import TauCeti.AlgebraicGeometry.Grassmannian.IsBaseChange
public import TauCeti.AlgebraicGeometry.Modules.AffineRestriction

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
(`Module.Grassmannian.isPullback_isBaseChangeHom`). These comparison morphisms
`AlgebraicGeometry.Scheme.Modules.grassmannianChartMap` compose, so they form a relative gluing
datum over the directed cover of `X` by its affine opens
(`AlgebraicGeometry.Scheme.Cover.RelativeGluingData`), whose glued scheme is the relative
Grassmannian.

The construction applies to every quasi-coherent `E`. The roadmap's relative Grassmannian of a
finite locally free `E` is the case where each `Γ(E, U)` is finite projective; the universal
quotient over the glued scheme and its universal property over arbitrary `X`-schemes are not
treated here.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.grassmannianChartMap E k h`: for affine opens `V ≤ U`, the
  morphism `G(k, Γ(E, V)) ⟶ G(k, Γ(E, U))` over the restriction `Spec Γ(X, V) ⟶ Spec Γ(X, U)`.
* `AlgebraicGeometry.Scheme.Modules.grassmannianGluingData E k`: the relative gluing datum.
* `AlgebraicGeometry.Scheme.Modules.grassmannian E k`: the relative Grassmannian.
* `AlgebraicGeometry.Scheme.Modules.grassmannianToBase E k`: its structure morphism to `X`.
* `AlgebraicGeometry.Scheme.Modules.grassmannianι E k U`: the inclusion of `G(k, Γ(E, U))` as the
  part over the affine open `U`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isPullback_grassmannianChartMap`: for affine opens `V ≤ U`,
  `G(k, Γ(E, V))` is the part of `G(k, Γ(E, U))` over `V`.
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

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] (k : ℕ)

/-- The Grassmannian `G(k, Γ(E, U))` of the sections of `E` over an affine open `U`, a scheme over
`Spec Γ(X, U)`. -/
noncomputable abbrev grassmannianChart (U : X.affineOpens) : Scheme.{u} :=
  Module.Grassmannian.scheme Γ(X, U.val) Γ(E, U.val) k

/-- For affine opens `V ≤ U`, the morphism `G(k, Γ(E, V)) ⟶ G(k, Γ(E, U))` over the restriction
`Spec Γ(X, V) ⟶ Spec Γ(X, U)`: `Γ(E, V)` is the base change of `Γ(E, U)` along restriction of
functions, and this is `Module.Grassmannian.isBaseChangeHom` for that base change. It identifies
`G(k, Γ(E, V))` with the part of `G(k, Γ(E, U))` over `V`
(`AlgebraicGeometry.Scheme.Modules.isPullback_grassmannianChartMap`). -/
noncomputable def grassmannianChartMap {U V : X.affineOpens} (h : V.val ≤ U.val) :
    grassmannianChart E k V ⟶ grassmannianChart E k U :=
  letI := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  letI : Module Γ(X, U.val) Γ(E, V.val) := Module.compHom _ (algebraMap Γ(X, U.val) Γ(X, V.val))
  haveI : IsScalarTower Γ(X, U.val) Γ(X, V.val) Γ(E, V.val) := .of_algebraMap_smul fun _ _ ↦ rfl
  Module.Grassmannian.isBaseChangeHom
    (E.isBaseChange_sectionsRestrictionLinearMap U.property V.property h fun _ ↦ rfl) k

/-- `grassmannianChartMap` lies over the restriction `Spec Γ(X, V) ⟶ Spec Γ(X, U)`. -/
@[reassoc (attr := simp)]
theorem grassmannianChartMap_toSpec {U V : X.affineOpens} (h : V.val ≤ U.val) :
    grassmannianChartMap E k h ≫ Module.Grassmannian.toSpec Γ(X, U.val) Γ(E, U.val) k =
      Module.Grassmannian.toSpec Γ(X, V.val) Γ(E, V.val) k ≫
        Spec.map (X.presheaf.map (homOfLE h).op) :=
  letI := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  letI : Module Γ(X, U.val) Γ(E, V.val) := Module.compHom _ (algebraMap Γ(X, U.val) Γ(X, V.val))
  haveI : IsScalarTower Γ(X, U.val) Γ(X, V.val) Γ(E, V.val) := .of_algebraMap_smul fun _ _ ↦ rfl
  Module.Grassmannian.isBaseChangeHom_toSpec _ k

/-- **The Grassmannian over a smaller affine open.** For affine opens `V ≤ U`, the Grassmannian
`G(k, Γ(E, V))` is the fibre product `Spec Γ(X, V) ×_{Spec Γ(X, U)} G(k, Γ(E, U))`, with
projections `grassmannianChartMap` and the structure morphism. -/
theorem isPullback_grassmannianChartMap {U V : X.affineOpens} (h : V.val ≤ U.val) :
    IsPullback (grassmannianChartMap E k h) (Module.Grassmannian.toSpec Γ(X, V.val) Γ(E, V.val) k)
      (Module.Grassmannian.toSpec Γ(X, U.val) Γ(E, U.val) k)
      (Spec.map (X.presheaf.map (homOfLE h).op)) :=
  letI := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  letI : Module Γ(X, U.val) Γ(E, V.val) := Module.compHom _ (algebraMap Γ(X, U.val) Γ(X, V.val))
  haveI : IsScalarTower Γ(X, U.val) Γ(X, V.val) Γ(E, V.val) := .of_algebraMap_smul fun _ _ ↦ rfl
  Module.Grassmannian.isPullback_isBaseChangeHom _ k

/-- **The comparison morphisms compose.** For affine opens `W ≤ V ≤ U`, the morphisms
`G(k, Γ(E, W)) ⟶ G(k, Γ(E, V)) ⟶ G(k, Γ(E, U))` compose to the morphism for `W ≤ U`. -/
@[reassoc (attr := simp)]
theorem grassmannianChartMap_comp {U V W : X.affineOpens} (hWV : W.val ≤ V.val)
    (hVU : V.val ≤ U.val) :
    grassmannianChartMap E k hWV ≫ grassmannianChartMap E k hVU =
      grassmannianChartMap E k (hWV.trans hVU) := by
  let _ : Algebra Γ(X, U.val) Γ(X, V.val) := (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
  let _ : Algebra Γ(X, V.val) Γ(X, W.val) := (X.presheaf.map (homOfLE hWV).op).hom.toAlgebra
  let _ : Algebra Γ(X, U.val) Γ(X, W.val) :=
    (X.presheaf.map (homOfLE (hWV.trans hVU)).op).hom.toAlgebra
  let _ : Module Γ(X, U.val) Γ(E, V.val) := Module.compHom _ (algebraMap Γ(X, U.val) Γ(X, V.val))
  let _ : Module Γ(X, V.val) Γ(E, W.val) := Module.compHom _ (algebraMap Γ(X, V.val) Γ(X, W.val))
  let _ : Module Γ(X, U.val) Γ(E, W.val) := Module.compHom _ (algebraMap Γ(X, U.val) Γ(X, W.val))
  have _ : IsScalarTower Γ(X, U.val) Γ(X, V.val) Γ(E, V.val) := .of_algebraMap_smul fun _ _ ↦ rfl
  have _ : IsScalarTower Γ(X, V.val) Γ(X, W.val) Γ(E, W.val) := .of_algebraMap_smul fun _ _ ↦ rfl
  have _ : IsScalarTower Γ(X, U.val) Γ(X, W.val) Γ(E, W.val) := .of_algebraMap_smul fun _ _ ↦ rfl
  -- restriction of functions from `U` to `W` factors through `V`
  have hres (r : Γ(X, U.val)) :
      algebraMap Γ(X, V.val) Γ(X, W.val) (algebraMap Γ(X, U.val) Γ(X, V.val) r) =
        algebraMap Γ(X, U.val) Γ(X, W.val) r := by
    change (X.presheaf.map (homOfLE hVU).op ≫ X.presheaf.map (homOfLE hWV).op) r = _
    rw [← Functor.map_comp]
    rfl
  have _ : IsScalarTower Γ(X, U.val) Γ(X, V.val) Γ(X, W.val) :=
    .of_algebraMap_eq fun r ↦ (hres r).symm
  have _ : IsScalarTower Γ(X, U.val) Γ(X, V.val) Γ(E, W.val) := ⟨fun r s m ↦ by
    change algebraMap Γ(X, V.val) Γ(X, W.val) (r • s) • m =
      algebraMap Γ(X, U.val) Γ(X, W.val) r • algebraMap Γ(X, V.val) Γ(X, W.val) s • m
    rw [Algebra.smul_def, map_mul, mul_smul, hres]⟩
  have hf := E.isBaseChange_sectionsRestrictionLinearMap U.property V.property hVU fun _ ↦ rfl
  have hg := E.isBaseChange_sectionsRestrictionLinearMap V.property W.property hWV fun _ ↦ rfl
  change Module.Grassmannian.isBaseChangeHom hg k ≫ Module.Grassmannian.isBaseChangeHom hf k =
    Module.Grassmannian.isBaseChangeHom
      (E.isBaseChange_sectionsRestrictionLinearMap U.property W.property (hWV.trans hVU)
        fun _ ↦ rfl) k
  rw [Module.Grassmannian.isBaseChangeHom_comp hf hg (hf.comp hg)]
  refine Module.Grassmannian.isBaseChangeHom_congr _ k _ (LinearMap.ext fun s ↦ ?_)
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    sectionsRestrictionLinearMap_apply]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- For an affine open `U`, the comparison morphism of `G(k, Γ(E, U))` with itself is the
identity. -/
@[simp]
theorem grassmannianChartMap_self (U : X.affineOpens) :
    grassmannianChartMap E k (le_refl U.val) = 𝟙 _ := by
  -- the morphism is an idempotent isomorphism, as the base change of the identity
  have : IsIso (Spec.map (X.presheaf.map (homOfLE (le_refl U.val)).op)) := by
    rw [show homOfLE (le_refl U.val) = 𝟙 _ from rfl]
    simp only [op_id, CategoryTheory.Functor.map_id]
    infer_instance
  have := (isPullback_grassmannianChartMap E k (le_refl U.val)).isIso_fst_of_isIso
  rw [← cancel_mono (grassmannianChartMap E k (le_refl U.val)), grassmannianChartMap_comp,
    Category.id_comp]

/-- The Grassmannians `G(k, Γ(E, U))` of the sections of `E` over the affine opens `U` of `X`, as
a functor on the directed cover of `X` by its affine opens. -/
@[expose, simps]
noncomputable def grassmannianFunctor : X.directedAffineCover.I₀ ⥤ Scheme.{u} where
  obj U := grassmannianChart E k U
  map h := grassmannianChartMap E k (leOfHom h)
  map_id U := grassmannianChartMap_self E k U
  map_comp h h' := (grassmannianChartMap_comp E k (leOfHom h) (leOfHom h')).symm

-- On an affine open `U`, the isomorphism `U ≅ Spec Γ(X, U)` is compatible with restriction to a
-- smaller affine open `V`.
private lemma specMap_isoSpec_inv {U V : X.affineOpens} (h : V.val ≤ U.val) :
    Spec.map (X.presheaf.map (homOfLE h).op) ≫ U.property.isoSpec.inv =
      V.property.isoSpec.inv ≫ X.homOfLE h := by
  rw [← cancel_mono U.val.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι]
  exact IsAffineOpen.map_fromSpec U.property V.property (homOfLE h).op

-- The square relating restriction `Spec Γ(X, V) ⟶ Spec Γ(X, U)` to the inclusion `V ⟶ U` is a
-- pullback square, as its vertical sides are isomorphisms.
private lemma isPullback_specMap_isoSpec_inv {U V : X.affineOpens} (h : V.val ≤ U.val) :
    IsPullback (Spec.map (X.presheaf.map (homOfLE h).op)) V.property.isoSpec.inv
      U.property.isoSpec.inv (X.homOfLE h) :=
  IsPullback.of_vert_isIso ⟨specMap_isoSpec_inv h⟩

-- The naturality square of the structure morphisms `G(k, Γ(E, U)) ⟶ U`.
private lemma grassmannianChartMap_toSpec_isoSpec_inv {U V : X.affineOpens} (h : V.val ≤ U.val) :
    grassmannianChartMap E k h ≫ Module.Grassmannian.toSpec Γ(X, U.val) Γ(E, U.val) k ≫
        U.property.isoSpec.inv =
      (Module.Grassmannian.toSpec Γ(X, V.val) Γ(E, V.val) k ≫ V.property.isoSpec.inv) ≫
        X.homOfLE h := by
  rw [grassmannianChartMap_toSpec_assoc, specMap_isoSpec_inv, Category.assoc]

/-- The **relative gluing datum of the Grassmannian**: the Grassmannians `G(k, Γ(E, U))` over the
affine opens `U ≅ Spec Γ(X, U)` of `X`, with the comparison morphisms for `V ≤ U`, which identify
`G(k, Γ(E, V))` with the part of `G(k, Γ(E, U))` over `V`. -/
noncomputable def grassmannianGluingData : X.directedAffineCover.RelativeGluingData where
  functor := grassmannianFunctor E k
  natTrans :=
    { app (U : X.affineOpens) :=
        Module.Grassmannian.toSpec Γ(X, U.val) Γ(E, U.val) k ≫ U.property.isoSpec.inv
      naturality _ _ h := grassmannianChartMap_toSpec_isoSpec_inv E k (leOfHom h) }
  equifibered _ _ h :=
    (isPullback_grassmannianChartMap E k (leOfHom h)).paste_vert
      (isPullback_specMap_isoSpec_inv (leOfHom h))

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

/-- **The relative Grassmannian over an affine open.** For an affine open `U` of `X`, the part of
the relative Grassmannian over `U` is `G(k, Γ(E, U))`: the square formed by the inclusion of
`U ≅ Spec Γ(X, U)` and the structure morphisms is a pullback square. -/
theorem isPullback_grassmannianι (U : X.affineOpens) :
    IsPullback (Module.Grassmannian.toSpec Γ(X, U.val) Γ(E, U.val) k ≫ U.property.isoSpec.inv)
      (grassmannianι E k U) U.val.ι (grassmannianToBase E k) :=
  (grassmannianGluingData E k).isPullback_natTrans_ι_toBase U

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

end AlgebraicGeometry.Scheme.Modules
