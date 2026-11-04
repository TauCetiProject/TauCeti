/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Maps out of a polynomial ring

An `A`-algebra homomorphism out of a polynomial ring `A[X_σ]` is determined freely by the images
of the variables: `MvPolynomial.aevalEquiv` identifies such homomorphisms to `S` with the
functions `σ → S`, the points of affine space. So a homomorphism lifts along every surjective
`A`-algebra homomorphism `f : R → S`: send each variable to a preimage under `f` of its image.

## Main results

* `MvPolynomial.aevalEquiv`: evaluation `MvPolynomial.aeval` is a bijection from `σ → S` onto
  `A[X_σ] →ₐ[A] S`, with inverse evaluation at the variables.
* `MvPolynomial.exists_comp_eq_of_surjective`: every `g : A[X_σ] →ₐ[A] S` factors as `f.comp g'`
  through any surjective `f : R →ₐ[A] S`.
-/

public section

namespace MvPolynomial

/-- **Maps out of a polynomial ring are their values on the variables**: `MvPolynomial.aeval` is a
bijection from `σ → S` onto the `A`-algebra homomorphisms `A[X_σ] →ₐ[A] S`, with inverse
evaluation at the variables. -/
noncomputable def aevalEquiv (σ A S : Type*) [CommSemiring A] [CommSemiring S] [Algebra A S] :
    (σ → S) ≃ (MvPolynomial σ A →ₐ[A] S) where
  toFun := aeval
  invFun g i := g (X i)
  left_inv v := funext (aeval_X v)
  right_inv g := (aeval_unique g).symm

@[simp]
theorem aevalEquiv_apply {σ A S : Type*} [CommSemiring A] [CommSemiring S] [Algebra A S]
    (v : σ → S) : aevalEquiv σ A S v = aeval v :=
  (rfl)

@[simp]
theorem aevalEquiv_symm_apply {σ A S : Type*} [CommSemiring A] [CommSemiring S] [Algebra A S]
    (g : MvPolynomial σ A →ₐ[A] S) (i : σ) : (aevalEquiv σ A S).symm g i = g (X i) :=
  (rfl)

/-- **Maps out of a polynomial ring lift along surjections**: every `A`-algebra homomorphism
`g : A[X_σ] →ₐ[A] S` factors as `f.comp g'` through any surjective `f : R →ₐ[A] S`. -/
theorem exists_comp_eq_of_surjective {σ A R S : Type*} [CommSemiring A] [CommSemiring R]
    [CommSemiring S] [Algebra A R] [Algebra A S] {f : R →ₐ[A] S} (hf : Function.Surjective f)
    (g : MvPolynomial σ A →ₐ[A] S) : ∃ g' : MvPolynomial σ A →ₐ[A] R, f.comp g' = g :=
  ⟨aeval (Function.surjInv hf ∘ g ∘ X), algHom_ext fun _ ↦ by simp [Function.surjInv_eq hf]⟩

end MvPolynomial
