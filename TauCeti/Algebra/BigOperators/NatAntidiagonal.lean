/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Sums over the antidiagonals of `ℕ × ℕ`

Two identities for sums over `Finset.antidiagonal k`, the pairs `(i, j)` with `i + j = k`.

The first splits a sum over `i + j = k + 1`, weighted by `k + 1 = i + j`, into the parts weighted
by `i` and by `j`, each reindexed over `i + j = k`. It is the step that turns a recursion
`(k + 1) T (k + 1) = D (T k)` for the degree-`k` terms of a formal product, in which the
derivation `D` acts on one factor at a time, into a recursion for the degree-`k` terms of a
double product, as in generating-function arguments.

The second rewrites the sum over all antidiagonals `i + j = k` with `k < N` as the sum over the
triangle `i < N`, `j < N - i`, so that the inner sum can be evaluated for each fixed `i`.

## Main results

* `Finset.Nat.natCast_add_one_smul_sum_antidiagonal_succ`: the weighted split of a sum over
  `i + j = k + 1`.
* `Finset.Nat.sum_range_sum_antidiagonal`: the sum over the antidiagonals below `N` as a sum over a
  triangle.
-/

public section

namespace Finset.Nat

variable {M : Type*}

/-- Weighting the terms `f (i, j)` with `i + j = k + 1` by `k + 1 = i + j` splits their sum into
the parts weighted by `i` and by `j`, reindexed over `i + j = k`:
`(k + 1) ∑_{i + j = k + 1} f (i, j) = ∑_{i + j = k} ((i + 1) f (i + 1, j) + (j + 1) f (i, j + 1))`.
-/
theorem natCast_add_one_smul_sum_antidiagonal_succ {R : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] (f : ℕ × ℕ → M) (k : ℕ) :
    ((k : R) + 1) • ∑ p ∈ antidiagonal (k + 1), f p =
      ∑ p ∈ antidiagonal k, ((p.1 : R) + 1) • f (p.1 + 1, p.2) +
        ∑ p ∈ antidiagonal k, ((p.2 : R) + 1) • f (p.1, p.2 + 1) := by
  have h : ((k : R) + 1) • ∑ p ∈ antidiagonal (k + 1), f p =
      ∑ p ∈ antidiagonal (k + 1), (p.1 : R) • f p +
        ∑ p ∈ antidiagonal (k + 1), (p.2 : R) • f p := by
    rw [smul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun p hp ↦ ?_
    rw [← add_smul, ← Nat.cast_add, mem_antidiagonal.1 hp, Nat.cast_add_one]
  rw [h, sum_antidiagonal_succ, sum_antidiagonal_succ']
  simp

/-- The sum over the antidiagonals `i + j = k` with `k < N` is the sum over the triangle
`i < N`, `j < N - i`. -/
theorem sum_range_sum_antidiagonal [AddCommMonoid M] (g : ℕ → ℕ → M) (N : ℕ) :
    ∑ k ∈ range N, ∑ p ∈ antidiagonal k, g p.1 p.2 =
      ∑ i ∈ range N, ∑ j ∈ range (N - i), g i j := by
  simp_rw [sum_antidiagonal_eq_sum_range_succ g]
  exact sum_range_diag_flip N g

end Finset.Nat
