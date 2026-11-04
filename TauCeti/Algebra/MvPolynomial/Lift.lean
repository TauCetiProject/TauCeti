/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Lifting maps out of a polynomial ring along surjections

An `A`-algebra homomorphism out of a polynomial ring `A[X_σ]` is determined freely by the images
of the variables, so it lifts along every surjective `A`-algebra homomorphism `f : R → S`: send
each variable to a preimage under `f` of its image.

## Main results

* `MvPolynomial.exists_comp_eq_of_surjective`: every `g : A[X_σ] →ₐ[A] S` factors as `f.comp g'`
  through any surjective `f : R →ₐ[A] S`.
-/

public section

namespace MvPolynomial

/-- **Maps out of a polynomial ring lift along surjections**: every `A`-algebra homomorphism
`g : A[X_σ] →ₐ[A] S` factors as `f.comp g'` through any surjective `f : R →ₐ[A] S`. -/
theorem exists_comp_eq_of_surjective {σ A R S : Type*} [CommSemiring A] [CommSemiring R]
    [CommSemiring S] [Algebra A R] [Algebra A S] {f : R →ₐ[A] S} (hf : Function.Surjective f)
    (g : MvPolynomial σ A →ₐ[A] S) : ∃ g' : MvPolynomial σ A →ₐ[A] R, f.comp g' = g :=
  ⟨aeval (Function.surjInv hf ∘ g ∘ X), algHom_ext fun _ ↦ by simp [Function.surjInv_eq hf]⟩

end MvPolynomial
