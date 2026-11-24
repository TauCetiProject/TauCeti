/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Coeff

/-!
# Ordered monomials in two variables

The monomials `X 1 ^ a * X 0 ^ b` of `MvPolynomial (Fin 2) R`, with all powers of `X 1` to the left
of all powers of `X 0`, are its monomial basis written in ordered form. This file records
induction over ordered monomials and extensionality of linear and bilinear maps on ordered
monomials. These are the forms in which ordered products, such as `TauCeti.affineStar`, are defined
and compared.

## Main results

* `MvPolynomial.induction_on_X_one_pow_mul_X_zero_pow`: induction over ordered monomials.
* `MvPolynomial.linearMap_ext_X_one_pow_mul_X_zero_pow`,
  `MvPolynomial.linearMap_ext₂_X_one_pow_mul_X_zero_pow`: linear and bilinear maps agreeing on
  ordered monomials are equal.
-/

public section

namespace MvPolynomial

variable {S : Type*} [CommSemiring S]

/-- Induction on a polynomial in two variables through scalar multiples and sums of the ordered
monomials `X 1 ^ a * X 0 ^ b`. -/
@[elab_as_elim]
theorem induction_on_X_one_pow_mul_X_zero_pow {P : MvPolynomial (Fin 2) S → Prop}
    (p : MvPolynomial (Fin 2) S) (smul : ∀ (a : S) p, P p → P (a • p))
    (add : ∀ p q, P p → P q → P (p + q)) (X_pow : ∀ a b : ℕ, P (X 1 ^ a * X 0 ^ b)) : P p := by
  induction p using MvPolynomial.induction_on' with
  | monomial s a =>
      rw [monomial_fin_two, mul_assoc, mul_comm (X 0 ^ _), ← smul_eq_C_mul]
      exact smul _ _ (X_pow _ _)
  | add p q hp hq => exact add p q hp hq

/-- Two linear maps out of polynomials in two variables agree once they agree on the ordered
monomials `X 1 ^ a * X 0 ^ b`. -/
theorem linearMap_ext_X_one_pow_mul_X_zero_pow {M : Type*} [AddCommMonoid M]
    [Module S M] {f g : MvPolynomial (Fin 2) S →ₗ[S] M}
    (h : ∀ a b : ℕ, f (X 1 ^ a * X 0 ^ b) = g (X 1 ^ a * X 0 ^ b)) : f = g :=
  (basisMonomials (Fin 2) S).ext fun s ↦ by
    simpa [coe_basisMonomials, monomial_fin_two, mul_comm] using h (s 1) (s 0)

/-- Two bilinear maps out of polynomials in two variables agree once they agree on pairs of
ordered monomials `X 1 ^ a * X 0 ^ b`, `X 1 ^ c * X 0 ^ d`. -/
theorem linearMap_ext₂_X_one_pow_mul_X_zero_pow {M : Type*} [AddCommMonoid M]
    [Module S M] {f g : MvPolynomial (Fin 2) S →ₗ[S] MvPolynomial (Fin 2) S →ₗ[S] M}
    (h : ∀ a b c d : ℕ, f (X 1 ^ a * X 0 ^ b) (X 1 ^ c * X 0 ^ d) =
      g (X 1 ^ a * X 0 ^ b) (X 1 ^ c * X 0 ^ d)) : f = g :=
  linearMap_ext_X_one_pow_mul_X_zero_pow fun a b ↦
    linearMap_ext_X_one_pow_mul_X_zero_pow fun c d ↦ h a b c d

end MvPolynomial
