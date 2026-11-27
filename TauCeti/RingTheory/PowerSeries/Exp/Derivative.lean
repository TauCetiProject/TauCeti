/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Exp
public import TauCeti.Algebra.Polynomial.ExpDerivFactor
import TauCeti.RingTheory.PowerSeries.Derivative

/-!
# Derivatives of exponential polynomials

Over a commutative `ℚ`-algebra `A`, the exponential polynomial `Q (X) exp (ψ X)`, for a polynomial
`Q` and `ψ ∈ A`, is the formal power series `Q * rescale ψ (exp A)`. Its formal derivative is
`(Q′ + ψ Q) exp (ψ X)`, so its `m`-th formal derivative is `((D + ψ) ^ m Q) (X) exp (ψ X)`, with
`(D + ψ) ^ m` the operator `Polynomial.expDerivFactor ψ m`. This is what makes the derivatives of
the auxiliary functions of Baker's method again exponential polynomials with the same frequencies,
whose polynomial parts are computed by `Polynomial.expDerivFactor`.

The identity only uses that `exp (ψ X)` satisfies `f′ = ψ f`, and it is proved in that form, for
any power series `f` over a commutative semiring.

## Main results

* `PowerSeries.derivative_rescale_exp`: `d/dX exp (ψ X) = ψ exp (ψ X)`.
* `PowerSeries.iterate_derivative_coe_mul_of_derivative_eq_C_mul`: if `f′ = c f`, then the `m`-th
  derivative of `Q f` is `((D + c) ^ m Q) f`.
* `PowerSeries.iterate_derivative_coe_mul_rescale_exp`: the `m`-th derivative of
  `Q (X) exp (ψ X)` is `((D + ψ) ^ m Q) (X) exp (ψ X)`.

## References

* A. Baker, *Transcendental Number Theory*, Cambridge University Press, 1975, Chapter 2.
-/

public section

open scoped Polynomial

namespace PowerSeries

/-- If `f′ = c f`, then `(Q f)′ = (Q′ + c Q) f` for a polynomial `Q`. -/
theorem derivative_coe_mul_of_derivative_eq_C_mul {A : Type*} [CommSemiring A] {f : A⟦X⟧}
    {c : A} (hf : d⁄dX f = C c * f) (Q : A[X]) :
    d⁄dX ((Q : A⟦X⟧) * f) = ((Polynomial.expDerivFactor c 1 Q : A[X]) : A⟦X⟧) * f := by
  rw [Polynomial.expDerivFactor_one, Derivation.leibniz, hf, derivative_coe, smul_eq_mul,
    smul_eq_mul, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C]
  ring

/-- If `f′ = c f`, then the `m`-th derivative of `Q f` is `((D + c) ^ m Q) f` for a polynomial
`Q`. -/
theorem iterate_derivative_coe_mul_of_derivative_eq_C_mul {A : Type*} [CommSemiring A]
    {f : A⟦X⟧} {c : A} (hf : d⁄dX f = C c * f) (Q : A[X]) (m : ℕ) :
    (d⁄dX)^[m] ((Q : A⟦X⟧) * f) = ((Polynomial.expDerivFactor c m Q : A[X]) : A⟦X⟧) * f := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, derivative_coe_mul_of_derivative_eq_C_mul hf,
      ← Polynomial.expDerivFactor_add, add_comm]

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- The derivative of `exp (ψ X)` is `ψ exp (ψ X)`. -/
@[simp]
theorem derivative_rescale_exp (ψ : A) :
    d⁄dX (rescale ψ (exp A)) = C ψ * rescale ψ (exp A) := by
  rw [derivative_rescale, derivative_exp]

/-- **The derivatives of an exponential polynomial.** The `m`-th derivative of `Q (X) exp (ψ X)`
is `((D + ψ) ^ m Q) (X) exp (ψ X)`. -/
theorem iterate_derivative_coe_mul_rescale_exp (Q : A[X]) (ψ : A) (m : ℕ) :
    (d⁄dX)^[m] ((Q : A⟦X⟧) * rescale ψ (exp A)) =
      ((Polynomial.expDerivFactor ψ m Q : A[X]) : A⟦X⟧) * rescale ψ (exp A) :=
  iterate_derivative_coe_mul_of_derivative_eq_C_mul (derivative_rescale_exp ψ) Q m

end PowerSeries
