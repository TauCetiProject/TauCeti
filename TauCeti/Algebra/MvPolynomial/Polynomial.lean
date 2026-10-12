/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Evaluating a multivariate polynomial at univariate polynomials

Substituting univariate polynomials `fᵢ ∈ S[T]` for the variables of `p ∈ R[X_σ]` and then
evaluating at `t ∈ S` is the same as substituting the values `fᵢ(t)`. This is the form in which a
polynomial identity along a line `T ↦ (f₀(T), …)` is evaluated pointwise.

## Main results

* `MvPolynomial.polynomial_eval_aeval`: `(p(f))(t) = p(f(t))`.
-/

public section

namespace MvPolynomial

variable {R S σ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- Evaluating at `t` the substitution of univariate polynomials `fᵢ` into `p` is substituting the
values `fᵢ(t)`. -/
theorem polynomial_eval_aeval (f : σ → Polynomial S) (t : S) (p : MvPolynomial σ R) :
    (aeval f p).eval t = aeval (fun i ↦ (f i).eval t) p := by
  simpa using comp_aeval_apply ((Polynomial.aeval t).restrictScalars R) p (f := f)

end MvPolynomial
