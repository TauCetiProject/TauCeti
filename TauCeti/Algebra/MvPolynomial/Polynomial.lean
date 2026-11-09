/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Evaluating a polynomial in a multivariate polynomial

A one-variable polynomial `r : K[X]` can be applied to a multivariate polynomial `p` with
`Polynomial.aeval p r`. Evaluating the result at `f` is `r` evaluated at the value of `p` at `f`.

## Main results

* `MvPolynomial.eval_polynomial_aeval`: `eval f (Polynomial.aeval p r) = r.eval (eval f p)`.
-/

public section

namespace MvPolynomial

variable {K σ : Type*} [CommSemiring K]

/-- Evaluating a one-variable polynomial `r` applied to a multivariate polynomial `p` is `r`
evaluated at the value of `p`. -/
@[simp] theorem eval_polynomial_aeval (f : σ → K) (p : MvPolynomial σ K)
    (r : Polynomial K) : eval f (Polynomial.aeval p r) = r.eval (eval f p) := by
  rw [← aeval_eq_eval, ← Polynomial.aeval_algHom_apply, Polynomial.coe_aeval_eq_eval]

end MvPolynomial
