/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Continuity of algebra evaluation of multivariate polynomials

For a commutative semiring `k`, a topological commutative `k`-algebra `R` whose ring operations
are continuous, and a polynomial `p` in variables indexed by an arbitrary type `σ` with
coefficients in `k`, the function `v ↦ aeval v p` on `σ → R` is continuous. This is the
multivariate, algebra-valued form of Mathlib's `Polynomial.continuous_aeval`; Mathlib's
`MvPolynomial.continuous_eval` treats only polynomials with coefficients in `R` itself.
-/

public section

namespace MvPolynomial

variable {k R σ : Type*} [CommSemiring k] [CommSemiring R] [Algebra k R] [TopologicalSpace R]
  [IsTopologicalSemiring R]

/-- Evaluating a polynomial with coefficients in `k` at points of a topological `k`-algebra `R`
with continuous ring operations is continuous, for any set of variables. -/
@[continuity, fun_prop]
theorem continuous_aeval (p : MvPolynomial σ k) : Continuous fun v : σ → R ↦ aeval v p := by
  simpa only [aeval_def, eval_map] using (p.map (algebraMap k R)).continuous_eval

end MvPolynomial
