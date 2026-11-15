/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# Infinite-sum representations of polynomial evaluation

Because a polynomial `P : R[X]` has only finitely many nonzero coefficients, the `ℕ`-indexed family
of its monomial terms has finite support and therefore converges (`HasSum`) in any topological space
on the target semiring, without requiring continuity of addition or multiplication.

## Main results

* `Polynomial.hasSum_eval₂`: `fun n ↦ f (P.coeff n) * x ^ n` sums to `P.eval₂ f x`.
* `Polynomial.hasSum_eval`: `fun n ↦ P.coeff n * x ^ n` sums to `P.eval x`.
* `Polynomial.hasSum_eval_sub_coeff_zero`: over a ring, the positive-degree monomial terms
  `fun k ↦ P.coeff (k + 1) * x ^ (k + 1)` sum to `P.eval x - P.coeff 0`.
-/

public section

namespace Polynomial

/-- For a polynomial `P : R[X]` and a ring homomorphism `f : R →+* S` into a semiring `S` equipped
with a topology, the monomial terms `f (P.coeff n) * x ^ n` have finite support and sum to
`P.eval₂ f x`. -/
theorem hasSum_eval₂ {R S : Type*} [Semiring R] [Semiring S] [TopologicalSpace S]
    (P : R[X]) (f : R →+* S) (x : S) :
    HasSum (fun n : ℕ ↦ f (P.coeff n) * x ^ n) (P.eval₂ f x) := by
  rw [P.eval₂_eq_sum, P.sum_def]
  refine hasSum_sum_of_ne_finset_zero fun n hn ↦ ?_
  rw [mem_support_iff, not_not] at hn
  rw [hn, map_zero, zero_mul]

/-- For a polynomial `P : R[X]` over a semiring `R` equipped with a topology, the monomial terms
`P.coeff n * x ^ n` have finite support and sum to `P.eval x`. -/
theorem hasSum_eval {R : Type*} [Semiring R] [TopologicalSpace R] (P : R[X]) (x : R) :
    HasSum (fun n : ℕ ↦ P.coeff n * x ^ n) (P.eval x) :=
  P.hasSum_eval₂ (RingHom.id R) x

/-- For a polynomial `P : R[X]` over a ring `R` equipped with a topology, the positive-degree
monomial terms `P.coeff (k + 1) * x ^ (k + 1)` have finite support and sum to
`P.eval x - P.coeff 0`. -/
theorem hasSum_eval_sub_coeff_zero {R : Type*} [Ring R] [TopologicalSpace R]
    (P : R[X]) (x : R) :
    HasSum (fun k : ℕ ↦ P.coeff (k + 1) * x ^ (k + 1)) (P.eval x - P.coeff 0) := by
  have h := (P - C (P.coeff 0)).hasSum_eval x
  rw [eval_sub, eval_C] at h
  have h0 : ∀ n ∉ Set.range (· + 1 : ℕ → ℕ), (P - C (P.coeff 0)).coeff n * x ^ n = 0 := by
    rintro (_ | n) hn
    · simp
    · exact absurd ⟨n, rfl⟩ hn
  simpa [Function.comp_def] using ((add_left_injective 1).hasSum_iff h0).2 h

end Polynomial
