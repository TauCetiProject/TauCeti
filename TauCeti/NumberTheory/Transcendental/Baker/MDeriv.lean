/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Data.Matrix.Mul
public import TauCeti.Analysis.Complex.MDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Complex.IteratedDeriv

/-!
# Mixed partial derivatives of exponential monomials

The auxiliary functions of the Schneider, Lang, and Baker transcendence methods in several
variables are integer combinations of exponential monomials `z ↦ z^τ e^{w · z}`. Using the
general mixed partial derivative operator `TauCeti.mDeriv` and the separated-product formula
`TauCeti.mDeriv_prod`, this file computes the mixed partial derivatives `D^σ (z ↦ e^{w · z})`
and `D^σ (z ↦ z^τ e^{w · z})` needed for the arithmetic estimates.

## Main results

* `TauCeti.Baker.mDeriv_exp_dotProduct`: `D^σ (z ↦ e^{w · z}) = z ↦ w^σ e^{w · z}`.
* `TauCeti.Baker.mDeriv_monomial_mul_exp`: the Leibniz expansion of `D^σ (z ↦ z^τ e^{w · z})`.

## References

* [M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer, 2000]:
  the notation `D^σ` for derivatives in several variables, and the derivatives of exponential
  monomials computed in §4.4, Lemma 4.9.
-/

public section

open Finset

namespace TauCeti.Baker

variable {n : ℕ}

/-- **Mixed partial derivatives of an exponential.** `D^σ (z ↦ e^{w · z}) = z ↦ w^σ e^{w · z}`,
where `w^σ = ∏ᵢ wᵢ^{σᵢ}`. -/
theorem mDeriv_exp_dotProduct (w : Fin n → ℂ) (σ : Fin n → ℕ) :
    mDeriv σ (fun z ↦ Complex.exp (w ⬝ᵥ z)) =
      fun z ↦ (∏ i, w i ^ σ i) * Complex.exp (w ⬝ᵥ z) := by
  have hexp (z : Fin n → ℂ) : Complex.exp (w ⬝ᵥ z) = ∏ i, Complex.exp (w i * z i) := by
    rw [dotProduct, Complex.exp_sum]
  simp_rw [hexp]
  rw [mDeriv_prod (g := fun i s ↦ Complex.exp (w i * s)) fun i ↦ by fun_prop]
  ext z
  simp [prod_mul_distrib]

/-- **The Leibniz expansion for exponential monomials.** For `τ, σ ∈ ℕⁿ` and `w ∈ ℂⁿ`,

  `D^σ (z ↦ z^τ e^{w · z}) = z ↦ (∏ᵢ ∑_{k ≤ σᵢ} (σᵢ choose k) τᵢ(τᵢ - 1)⋯(τᵢ - k + 1) zᵢ^{τᵢ - k}
    wᵢ^{σᵢ - k}) e^{w · z}`.

The terms with `k > τᵢ` vanish, since then the descending factorial `τᵢ(τᵢ - 1)⋯(τᵢ - k + 1)`
is zero. -/
theorem mDeriv_monomial_mul_exp (τ σ : Fin n → ℕ) (w : Fin n → ℂ) :
    mDeriv σ (fun z ↦ (∏ i, z i ^ τ i) * Complex.exp (w ⬝ᵥ z)) =
      fun z ↦ (∏ i, ∑ k ∈ range (σ i + 1),
        ((σ i).choose k * (τ i).descFactorial k : ℂ) * z i ^ (τ i - k) * w i ^ (σ i - k)) *
        Complex.exp (w ⬝ᵥ z) := by
  have hfun (z : Fin n → ℂ) : (∏ i, z i ^ τ i) * Complex.exp (w ⬝ᵥ z) =
      ∏ i, (z i ^ τ i * Complex.exp (w i * z i)) := by
    rw [dotProduct, Complex.exp_sum, prod_mul_distrib]
  simp_rw [hfun]
  rw [mDeriv_prod (g := fun i s ↦ s ^ τ i * Complex.exp (w i * s)) fun i ↦ by fun_prop]
  ext z
  rw [dotProduct, Complex.exp_sum, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ ↦ ?_
  rw [iteratedDeriv_fun_mul (by fun_prop) (by fun_prop), sum_mul]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [iteratedDeriv_pow, iteratedDeriv_cexp_const_mul]
  ring

end TauCeti.Baker
