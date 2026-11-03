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
noncomputable def shrinkHomEquiv (M : ModuleCat.{v} R) : (of R (Shrink.{v} R) ⟶ M) ≃ M where
  toFun f := f ((Shrink.linearEquiv R R).symm 1)
  invFun m := ofHom ((LinearMap.toSpanSingleton R M m).comp (Shrink.linearEquiv R R).toLinearMap)
  left_inv f := by
    ext x
    -- Every element of the shrunk ring is a multiple of the shrunk unit.
    have hx : x = Shrink.linearEquiv R R x • (Shrink.linearEquiv R R).symm 1 := by
      rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
    conv_rhs => rw [hx]
    simp
  right_inv m := by simp

/-- The forgetful functor `ModuleCat.{v} R ⥤ Type v` is corepresented by `R`, shrunk to
`Type v`. -/
noncomputable def coyonedaObjIsoForget :
    coyoneda.obj (op (of R (Shrink.{v} R))) ≅ forget (ModuleCat.{v} R) :=
  NatIso.ofComponents fun M ↦ (shrinkHomEquiv R M).toIso

instance forget_isCorepresentable : (forget (ModuleCat.{v} R)).IsCorepresentable :=
  Functor.IsCorepresentable.mk' (coyonedaObjIsoForget R)

end ModuleCat
