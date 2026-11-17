/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# The tensor unit of `ModuleCat R`

The tensor unit `𝟙_ (ModuleCat R)` of the monoidal category of modules over a commutative ring `R`
is `R` itself. This file records the consequences that instance search and `Module.finrank` do
not see through the monoidal structure: the unit is a free, finitely generated `R`-module
(`ModuleCat.free_tensorUnit`, `ModuleCat.finite_tensorUnit`), of rank one when `R` satisfies the
strong rank condition (`ModuleCat.finrank_tensorUnit`).

Coefficients are often taken in the copy `ULift R` of `R`, for instance integral singular homology
with coefficients `ULift ℤ`, and then cross products have coefficients `ULift R ⊗ ULift R`.
`ModuleCat.uliftTensorSelfIso` identifies these with `ULift R` by multiplication.
-/

public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

universe u

namespace ModuleCat

variable (R : Type u) [CommRing R]

/-- The tensor unit of `ModuleCat R`, which is `R` itself, is a free `R`-module. -/
instance free_tensorUnit : Module.Free R (𝟙_ (ModuleCat.{u} R)) :=
  inferInstanceAs (Module.Free R R)

/-- The tensor unit of `ModuleCat R`, which is `R` itself, is a finitely generated `R`-module. -/
instance finite_tensorUnit : Module.Finite R (𝟙_ (ModuleCat.{u} R)) :=
  inferInstanceAs (Module.Finite R R)

/-- The tensor unit of `ModuleCat R`, which is `R` itself, has rank one over `R`. -/
@[simp]
theorem finrank_tensorUnit [StrongRankCondition R] : Module.finrank R (𝟙_ (ModuleCat.{u} R)) = 1 :=
  Module.finrank_self R

/-- The tensor square of the copy `ULift R` of the tensor unit is `ULift R` again, by
`a ⊗ b ↦ a * b`. -/
def uliftTensorSelfIso :
    of R (ULift.{u} R) ⊗ of R (ULift.{u} R) ≅ of R (ULift.{u} R) :=
  tensorIso (ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).toModuleIso
      (ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).toModuleIso ≪≫ λ_ (𝟙_ _) ≪≫
    (ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).toModuleIso.symm

@[simp]
theorem uliftTensorSelfIso_hom_tmul (a b : ULift.{u} R) :
    (uliftTensorSelfIso R).hom (a ⊗ₜ b) = ULift.up (a.down * b.down) := by
  rw [uliftTensorSelfIso, Iso.trans_hom, Iso.trans_hom, comp_apply, comp_apply, tensorIso_hom,
    MonoidalCategory.tensorHom_tmul, MonoidalCategory.leftUnitor_hom_apply, Iso.symm_hom]
  simp only [LinearEquiv.toModuleIso_hom, LinearEquiv.toModuleIso_inv, hom_ofHom,
    LinearEquiv.coe_coe, ULift.moduleEquiv_apply, ULift.moduleEquiv_symm_apply, smul_eq_mul]

end ModuleCat
