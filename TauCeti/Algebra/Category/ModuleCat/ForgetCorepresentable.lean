/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.LinearAlgebra.Span.Basic

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
