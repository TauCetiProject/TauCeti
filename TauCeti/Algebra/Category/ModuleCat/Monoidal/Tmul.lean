/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Evaluating squares of semimodule maps on pure tensors

If a morphism `c` on the target of `E : X ⊗ Y ⟶ Z` in `SemimoduleCat A` intertwines `E` with a
tensor product of two endomorphisms `a ⊗ₘ b`, as a square in `SemimoduleCat A`, then
`c (E (x ⊗ₜ y)) = E (a x ⊗ₜ b y)`
(`SemimoduleCat.apply_tmul_of_comp_eq`).
-/

public section

open CategoryTheory MonoidalCategory TensorProduct

universe u

namespace SemimoduleCat

variable {A : Type u} [CommSemiring A]

/-- A morphism `E : X ⊗ Y ⟶ Z` of semimodules, and a linear map `c` on its target that intertwines
`E` with the tensor product of two linear maps `a` and `b`, as a square of module maps, satisfy
`c (E (x ⊗ₜ y)) = E (a x ⊗ₜ b y)` for the pure tensors `x ⊗ₜ y`. -/
theorem apply_tmul_of_comp_eq {X Y Z : Type u} [AddCommMonoid X] [Module A X]
    [AddCommMonoid Y] [Module A Y] [AddCommMonoid Z] [Module A Z]
    (E : (of A X ⊗ of A Y) ⟶ of A Z) {a : X →ₗ[A] X} {b : Y →ₗ[A] Y} {c : Z →ₗ[A] Z}
    (h : E ≫ ofHom c = (ofHom a ⊗ₘ ofHom b) ≫ E) (x : X) (y : Y) :
    c (E.hom (x ⊗ₜ[A] y)) = E.hom (a x ⊗ₜ[A] b y) := by
  have hlin := congrArg Hom.hom h
  rw [hom_comp, hom_comp, hom_tensorHom] at hlin
  exact LinearMap.congr_fun hlin (x ⊗ₜ[A] y)

end SemimoduleCat
