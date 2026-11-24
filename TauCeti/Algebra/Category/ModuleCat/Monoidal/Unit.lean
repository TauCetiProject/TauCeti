/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# The tensor unit of `ModuleCat R`

The tensor unit `𝟙_ (ModuleCat R)` of the monoidal category of modules over a commutative ring `R`
is `R` itself. This file records the consequences that instance search and `Module.finrank` do
not see through the monoidal structure: the unit is a free, projective, finitely generated
`R`-module (`ModuleCat.free_tensorUnit`, `ModuleCat.projective_tensorUnit`,
`ModuleCat.finite_tensorUnit`), of rank one when `R` satisfies the
strong rank condition (`ModuleCat.finrank_tensorUnit`). Morphisms out of a module isomorphic to
the unit are determined by their value on the element corresponding to `1`
(`ModuleCat.hom_ext_of_iso_tensorUnit`).

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

/-- The tensor unit of `ModuleCat R`, which is `R` itself, is a projective `R`-module. This follows
from `ModuleCat.free_tensorUnit`, but instance search reaches the low-priority
`Module.Projective.of_free` only after the other projectivity instances, which can time out, for
instance over `ℤ`. -/
instance projective_tensorUnit : Module.Projective R (𝟙_ (ModuleCat.{u} R)) :=
  inferInstanceAs (Module.Projective R R)

/-- The tensor unit of `ModuleCat R`, which is `R` itself, is a finitely generated `R`-module. -/
instance finite_tensorUnit : Module.Finite R (𝟙_ (ModuleCat.{u} R)) :=
  inferInstanceAs (Module.Finite R R)

/-- The tensor unit of `ModuleCat R`, which is `R` itself, has rank one over `R`. -/
@[simp]
theorem finrank_tensorUnit [StrongRankCondition R] : Module.finrank R (𝟙_ (ModuleCat.{u} R)) = 1 :=
  Module.finrank_self R

variable {R} in
/-- Two morphisms out of a module identified with the tensor unit `R` agree as soon as they agree
on the element corresponding to `1`. -/
theorem hom_ext_of_iso_tensorUnit {X P : ModuleCat.{u} R} (ψ : X ≅ 𝟙_ (ModuleCat.{u} R))
    {f g : X ⟶ P} (h : f.hom (ψ.inv.hom (1 : R)) = g.hom (ψ.inv.hom (1 : R))) : f = g :=
  (cancel_epi ψ.inv).1 (ModuleCat.hom_ext (LinearMap.ext_ring h))

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
  -- The Mathlib simp lemmas are instantiated by hand because simp does not unify the carriers of
  -- `of R (ULift R) ⊗ of R (ULift R)` and `𝟙_ (ModuleCat R)` with `ULift R ⊗[R] ULift R` and `R`.
  simp [uliftTensorSelfIso,
    MonoidalCategory.tensorHom_tmul (K := of R (ULift.{u} R)) (M := of R (ULift.{u} R)),
    MonoidalCategory.leftUnitor_hom_apply (M := 𝟙_ (ModuleCat.{u} R))]

@[simp]
theorem uliftTensorSelfIso_inv_apply (a : ULift.{u} R) :
    (uliftTensorSelfIso R).inv a = ULift.up 1 ⊗ₜ a := by
  -- As in `uliftTensorSelfIso_hom_tmul`, the carrier of `𝟙_ (ModuleCat R)` is supplied by hand.
  simp [uliftTensorSelfIso, MonoidalCategory.leftUnitor_inv_apply (M := 𝟙_ (ModuleCat.{u} R))]

end ModuleCat
