/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The contragredient homomorphism on linear automorphisms

For any module `M` over a commutative semiring `R`, sending a linear automorphism `e : M ≃ₗ[R] M`
to the dual of its inverse, `e.symm.dualMap`, yields a covariant group homomorphism
`LinearEquiv.contragredientHom R M : (M ≃ₗ[R] M) →* (Module.Dual R M ≃ₗ[R] Module.Dual R M)`.

Because precomposition reverses composition, taking the inverse first makes the assignment
multiplicative. Whenever the evaluation map `Module.Dual.eval R M` into the double dual is
injective — in particular for every projective module `M`, hence every free module and every
vector space of arbitrary (possibly infinite) dimension — this contragredient homomorphism is
injective (`LinearEquiv.contragredientHom_injective`).

## Main definitions

* `LinearEquiv.contragredientHom`: the covariant group homomorphism `e ↦ e.symm.dualMap` from
  `M ≃ₗ[R] M` to `Module.Dual R M ≃ₗ[R] Module.Dual R M`.

## Main results

* `LinearEquiv.contragredientHom_apply`, `LinearEquiv.contragredientHom_apply_apply`: evaluation
  formulas for the contragredient homomorphism.
* `LinearEquiv.contragredientHom_injective_of_eval_injective`: injectivity whenever
  `Module.Dual.eval R M` is injective.
* `LinearEquiv.contragredientHom_injective`: injectivity for any projective module (including
  every vector space, without finite-dimensionality).
-/

public section

namespace LinearEquiv

section Semiring

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The **contragredient homomorphism** `e ↦ e.symm.dualMap`, sending each linear automorphism of
`M` to the covariant dual automorphism `(φ ↦ φ ∘ e⁻¹)` of `Module.Dual R M`. -/
def contragredientHom : (M ≃ₗ[R] M) →* (Module.Dual R M ≃ₗ[R] Module.Dual R M) where
  toFun e := e.symm.dualMap
  map_one' := by ext φ x; simp [← LinearEquiv.coe_inv]
  map_mul' _ _ := by ext φ x; simp [← LinearEquiv.coe_inv, mul_apply_eq_comp]

variable {R M}

/-- The contragredient homomorphism sends `e` to `e.symm.dualMap`. -/
@[simp]
theorem contragredientHom_apply (e : M ≃ₗ[R] M) :
    contragredientHom R M e = e.symm.dualMap :=
  (rfl)

/-- Applying `contragredientHom R M e` to a functional `φ` evaluates `φ` at `e.symm x`. -/
theorem contragredientHom_apply_apply (e : M ≃ₗ[R] M) (φ : Module.Dual R M) (x : M) :
    contragredientHom R M e φ x = φ (e.symm x) :=
  (rfl)

/-- The contragredient homomorphism is injective whenever evaluation into the double dual is
injective. -/
theorem contragredientHom_injective_of_eval_injective
    (h : Function.Injective (Module.Dual.eval R M)) :
    Function.Injective (contragredientHom R M) := by
  intro e₁ e₂ heq
  apply LinearEquiv.symm_bijective.injective
  ext x
  exact h (LinearMap.ext fun φ ↦ congr(($(heq) φ) x))

variable (R M)

/-- For any projective module `M` (in particular any free module or any vector space of arbitrary
dimension), the contragredient homomorphism on linear automorphisms is injective. -/
theorem contragredientHom_injective [Module.Projective R M] :
    Function.Injective (contragredientHom R M) :=
  contragredientHom_injective_of_eval_injective (Module.eval_apply_injective R)

end Semiring

end LinearEquiv
