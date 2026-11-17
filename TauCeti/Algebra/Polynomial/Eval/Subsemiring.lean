/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic

/-!
# Polynomial evaluation inside subsemirings

Univariate analogues of Mathlib's `MvPolynomial.eval₂_mem` and `MvPolynomial.eval_mem`: if a
subsemiring-like substructure `s` (e.g., `Subsemiring`, `Subring`, `Subalgebra`, `Subfield`, or
`IntermediateField`) contains `x` and `f (p.coeff i)` for all `i ∈ p.support`, then
`p.eval₂ f x ∈ s`.

## Main results

* `Polynomial.eval₂_mem`, `Polynomial.eval_mem`: closure of subsemirings under evaluation.
-/

public section

namespace Polynomial

/-- If a subsemiring-like substructure `s` contains `x` and `f (p.coeff i)` for every `i` in
`p.support`, then `p.eval₂ f x ∈ s`. -/
theorem eval₂_mem {R S subS : Type*} [Semiring R] [Semiring S] [SetLike subS S]
    [SubsemiringClass subS S] {f : R →+* S} {p : R[X]} {s : subS}
    (hs : ∀ i ∈ p.support, f (p.coeff i) ∈ s) {x : S} (hx : x ∈ s) : p.eval₂ f x ∈ s := by
  rw [eval₂_eq_sum, Polynomial.sum]
  exact sum_mem fun i hi ↦ mul_mem (hs i hi) (pow_mem hx i)

/-- If a subsemiring-like substructure `s` contains `x` and `p.coeff i` for every `i` in
`p.support`, then `p.eval x ∈ s`. -/
theorem eval_mem {R subR : Type*} [Semiring R] [SetLike subR R] [SubsemiringClass subR R]
    {p : R[X]} {s : subR} (hs : ∀ i ∈ p.support, p.coeff i ∈ s) {x : R} (hx : x ∈ s) :
    p.eval x ∈ s :=
  eval₂_mem hs hx

end Polynomial
