/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Ideal.Operations
import TauCeti.RingTheory.Derivation.Ideal

/-!
# Partial derivatives of products of multivariate polynomials in ideal powers

For a variable `s` and a point `a`, if every iterated partial derivative `(pderiv s)^[k]` of order
at most `K` of each of `n` multivariate polynomials evaluates into an ideal `J` at `a`, then so
does every such derivative of their product, times an arbitrary cofactor, into `J ^ n`. This is
the instance of `Derivation.iterate_mul_prod_mem_ideal_pow` for `pderiv s` and evaluation at `a`;
the univariate forms are in `TauCeti.RingTheory.Polynomial.DerivativeIdealPow`.

## Main results

* `MvPolynomial.pderiv_prod_mem_ideal_pow`: iterated partial derivatives of multivariate
  polynomials, in an arbitrary variable.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, Lemma 11.14 and (11.22), p. 283, prove
  the analogue for Hasse derivatives of univariate polynomials; the argument here adapts it to
  iterated partial derivatives.
-/

public section

namespace MvPolynomial

variable {R σ ι : Type*} [CommSemiring R]

/-- **Partial derivatives of a product in an ideal power**: for a variable `s` and a point
`a : σ → R`, if every iterated partial derivative `(pderiv s)^[k]` of order at most `K` of each of
the `card ι` factors `f i` evaluates into `J` at `a`, so does every such derivative of the product
with an arbitrary cofactor `g`, into `J ^ card ι`. The bivariate form is `σ = Fin 2`. -/
theorem pderiv_prod_mem_ideal_pow [Fintype ι] (s : σ) (f : ι → MvPolynomial σ R)
    (g : MvPolynomial σ R) (a : σ → R) (J : Ideal R) (K : ℕ)
    (hf : ∀ i, ∀ k ≤ K, eval a ((pderiv s)^[k] (f i)) ∈ J) :
    ∀ k ≤ K, eval a ((pderiv s)^[k] (g * ∏ i, f i)) ∈ J ^ Fintype.card ι :=
  (pderiv s).iterate_mul_prod_mem_ideal_pow (eval a) f g J K hf

end MvPolynomial
