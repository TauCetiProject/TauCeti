/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.SpanSingleton
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# The forgetful functor on modules is corepresentable

For a ring `R` that is `v`-small, the forgetful functor `ModuleCat.{v} R ⥤ Type v` is
corepresented by `R` itself, shrunk to `Type v`: a linear map out of `R` is determined by the
image of `1`. This is the module analogue of Mathlib's
`AddCommGrpCat.forget_isCorepresentable`.

Since corepresentable functors preserve all limits that exist, of any size
(`CategoryTheory.Functor.IsCorepresentable`), the forgetful functor on `R`-modules preserves
limits indexed by large categories as well. For instance, it preserves the limits expressing the
sheaf condition on a large site such as the small étale site of a scheme, so a sheaf of
`R`-modules there has an underlying sheaf of sets
(`CategoryTheory.GrothendieckTopology.HasSheafCompose`).
Mathlib's `ModuleCat.forget_preservesLimitsOfSize` only covers limits whose index category is
no larger than the universe of the modules.

Evaluation at the shrunk unit is also an additive natural isomorphism
(`TauCeti.moduleCatPreadditiveCoyonedaShrinkRingIso`). When the universes agree, it gives
evaluation at one as an isomorphism to the underlying abelian-group functor
(`TauCeti.moduleCatPreadditiveCoyonedaRingIso`). Its inverse sends an element `m` to the map
`r ↦ r • m`.
-/

public section

universe v u

open CategoryTheory Opposite

namespace ModuleCat

variable (R : Type u) [Ring R] [Small.{v} R]

/-- A linear map out of `R`, shrunk to `Type v`, is determined by the image of `1`. -/
noncomputable def shrinkHomEquiv (M : ModuleCat.{v} R) : (of R (Shrink.{v} R) ⟶ M) ≃ M :=
  homEquiv.trans <| ((Shrink.linearEquiv R R).congrLeft M ℕ).toEquiv.trans
    (LinearMap.ringLmapEquivSelf R ℕ M).toEquiv

/-- `shrinkHomEquiv` evaluates a linear map at the shrunk unit. -/
@[simp]
lemma shrinkHomEquiv_apply (M : ModuleCat.{v} R) (f : of R (Shrink.{v} R) ⟶ M) :
    shrinkHomEquiv R M f = f (equivShrink R 1) := by
  simp [shrinkHomEquiv, homEquiv]

/-- The inverse of `shrinkHomEquiv` sends `m` to the linear map `r ↦ r • m`. -/
@[simp]
lemma shrinkHomEquiv_symm_apply (M : ModuleCat.{v} R) (m : M) :
    (shrinkHomEquiv R M).symm m =
      ofHom ((LinearMap.toSpanSingleton R M m).comp (Shrink.linearEquiv R R).toLinearMap) := by
  ext; simp [shrinkHomEquiv, homEquiv]

/-- The forgetful functor `ModuleCat.{v} R ⥤ Type v` is corepresented by `R`, shrunk to
`Type v`. -/
noncomputable def coyonedaObjIsoForget :
    coyoneda.obj (op (of R (Shrink.{v} R))) ≅ forget (ModuleCat.{v} R) :=
  NatIso.ofComponents fun M ↦ (shrinkHomEquiv R M).toIso

@[simp]
lemma coyonedaObjIsoForget_hom_app (M : ModuleCat.{v} R) (f : of R (Shrink.{v} R) ⟶ M) :
    dsimp% (coyonedaObjIsoForget R).hom.app M f = shrinkHomEquiv R M f := by
  simp [coyonedaObjIsoForget]

@[simp]
lemma coyonedaObjIsoForget_inv_app (M : ModuleCat.{v} R) (m : M) :
    dsimp% (coyonedaObjIsoForget R).inv.app M m = (shrinkHomEquiv R M).symm m := by
  simp [coyonedaObjIsoForget]

instance forget_isCorepresentable : (forget (ModuleCat.{v} R)).IsCorepresentable :=
  Functor.IsCorepresentable.mk' (coyonedaObjIsoForget R)

end ModuleCat

namespace TauCeti

/-- Evaluation at the shrunk unit identifies additive Hom from the regular module with
its underlying abelian-group functor, for any universe in which the ring is small. -/
noncomputable def moduleCatPreadditiveCoyonedaShrinkRingIso
    (R : Type u) [Ring R] [Small.{v} R] :
    preadditiveCoyoneda.obj (op (ModuleCat.of R (Shrink.{v} R))) ≅
      forget₂ (ModuleCat.{v} R) AddCommGrpCat :=
  NatIso.ofComponents (fun M ↦
    (AddEquiv.mk' (ModuleCat.shrinkHomEquiv R M)
      (by intros; simp)).toAddCommGrpIso)
    (fun f ↦ by
      ext g
      -- The bundled additive Hom object hides the morphism type needed by the evaluation rule.
      change ModuleCat.of R (Shrink.{v} R) ⟶ _ at g
      change ModuleCat.shrinkHomEquiv R _ (g ≫ f) =
        f (ModuleCat.shrinkHomEquiv R _ g)
      simp only [ModuleCat.shrinkHomEquiv_apply, ConcreteCategory.comp_apply])

end TauCeti

namespace ModuleCat

/-- The additive comparison for the shrunk regular module evaluates at the shrunk unit. -/
@[simp]
lemma moduleCatPreadditiveCoyonedaShrinkRingIso_hom_app_apply
    {R : Type u} [Ring R] [Small.{v} R]
    (M : ModuleCat.{v} R) (f : of R (Shrink.{v} R) ⟶ M) :
    DFunLike.coe (F := (of R (Shrink.{v} R) ⟶ M) →+ M)
      ((TauCeti.moduleCatPreadditiveCoyonedaShrinkRingIso R).hom.app M).hom f =
      f.hom (equivShrink R 1) := (shrinkHomEquiv_apply R M f)

/-- The inverse shrunk comparison sends an element to scalar multiplication by it. -/
@[simp]
lemma moduleCatPreadditiveCoyonedaShrinkRingIso_inv_app_apply
    {R : Type u} [Ring R] [Small.{v} R] (M : ModuleCat.{v} R) (m : M) :
    DFunLike.coe (F := M →+ (of R (Shrink.{v} R) ⟶ M))
      ((TauCeti.moduleCatPreadditiveCoyonedaShrinkRingIso R).inv.app M).hom m =
      ofHom ((LinearMap.toSpanSingleton R M m).comp (Shrink.linearEquiv R R).toLinearMap) :=
  (shrinkHomEquiv_symm_apply R M m)

end ModuleCat

namespace TauCeti

/-- Evaluation at `1` identifies additive Hom from the regular module with the underlying
abelian-group functor, by transporting the comparison for the shrunk regular module. -/
noncomputable def moduleCatPreadditiveCoyonedaRingIso (R : Type u) [Ring R] :
    preadditiveCoyoneda.obj (op (ModuleCat.of R R)) ≅
      forget₂ (ModuleCat.{u} R) AddCommGrpCat :=
  preadditiveCoyoneda.mapIso (Shrink.linearEquiv R R).toModuleIso.op ≪≫
    moduleCatPreadditiveCoyonedaShrinkRingIso R


end TauCeti

namespace ModuleCat

/-- The additive Hom comparison for the regular module is evaluation at `1`. -/
@[simp]
lemma moduleCatPreadditiveCoyonedaRingIso_hom_app_apply {R : Type u} [Ring R]
    (M : ModuleCat.{u} R) (f : of R R ⟶ M) :
    DFunLike.coe (F := (of R R ⟶ M) →+ M)
      ((TauCeti.moduleCatPreadditiveCoyonedaRingIso R).hom.app M).hom f = f.hom 1 :=
  (by
    simp only [TauCeti.moduleCatPreadditiveCoyonedaRingIso, Iso.trans_hom,
      NatTrans.comp_app, AddCommGrpCat.hom_comp]
    -- Expose the component's underlying morphism type, then evaluate the shrunk unit.
    change shrinkHomEquiv R M ((Shrink.linearEquiv R R).toModuleIso.hom ≫ f) = _
    simp [shrinkHomEquiv_apply])

/-- The inverse additive Hom comparison sends an element to the map taking `1` to it. -/
@[simp]
lemma moduleCatPreadditiveCoyonedaRingIso_inv_app_apply {R : Type u} [Ring R]
    (M : ModuleCat.{u} R) (m : M) :
    DFunLike.coe (F := M →+ (of R R ⟶ M))
      ((TauCeti.moduleCatPreadditiveCoyonedaRingIso R).inv.app M).hom m =
      ofHom (LinearMap.toSpanSingleton R M m) :=
  (by
    -- Name the morphism with its explicit type so evaluation rewrites under implicit transparency.
    let f : of R R ⟶ M := DFunLike.coe (F := M →+ (of R R ⟶ M))
      ((TauCeti.moduleCatPreadditiveCoyonedaRingIso R).inv.app M).hom m
    change f = _
    apply (homSelfLinearEquiv ℤ M).injective
    simp only [homSelfLinearEquiv_apply, hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul]
    rw [← moduleCatPreadditiveCoyonedaRingIso_hom_app_apply M f]
    exact ConcreteCategory.congr_hom
      ((TauCeti.moduleCatPreadditiveCoyonedaRingIso R).inv_hom_id_app M) m)

end ModuleCat
