/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Module

import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Ring
import TauCeti.Algebra.Order.BigOperators.Sum.ByParts

/-!
# A strict majorization criterion for staircase sequences

This file identifies an integer sequence from three numerical properties: it is antitone, it is
majorized by the finite staircase `N - 1, ..., 0`, and it has the same value as that staircase
under a particular quadratic weighted sum.

The criterion is intended for uniqueness arguments in which prefix inequalities alone leave many
possible sequences, but equality of a strictly convex statistic forces the extremal staircase.
Its integer-valued statement applies directly to occupation-number tuples after passing between
finite indices and natural-number ranges.

## Main result

* `TauCeti.eq_staircase_of_antitone_of_prefix_sum_le_of_sum_eq_of_casimir_eq`: an antitone
  integer sequence satisfying the staircase prefix, total, and quadratic-sum conditions agrees
  with the staircase throughout the prescribed range.

## References

* G. H. Hardy, J. E. Littlewood, G. Pólya, *Inequalities*, Cambridge University Press (1952),
  Chapter 2, for majorization and summation by parts.
-/

public section

namespace TauCeti

open scoped BigOperators

/-- **A sequence majorized by the finite staircase and having its quadratic sum is that
staircase.**

Let `a : ℕ → ℤ` be weakly decreasing through the first `N` entries. Suppose every proper
initial sum of `a` is at most that of `i ↦ N - (i + 1)`, and suppose their total sums agree. If
they also have the same value under

`a ↦ ∑ i < N, a i * (a i + N - 2i)`,

then their first `N` entries agree. No sign condition on `a` is needed. -/
theorem eq_staircase_of_antitone_of_prefix_sum_le_of_sum_eq_of_casimir_eq
    {N : ℕ} (a : ℕ → ℤ) (ha : ∀ i, i + 1 < N → a (i + 1) ≤ a i)
    (hmajor : ∀ (k : ℕ), k < N →
      (∑ i ∈ Finset.range k, a i) ≤
        ∑ i ∈ Finset.range k, ((N - (i + 1) : ℕ) : ℤ))
    (hsum : (∑ i ∈ Finset.range N, a i) =
      ∑ i ∈ Finset.range N, ((N - (i + 1) : ℕ) : ℤ))
    (hcasimir :
      (∑ i ∈ Finset.range N, a i * (a i + (N : ℤ) - 2 * i)) =
      ∑ i ∈ Finset.range N, ((N - (i + 1) : ℕ) : ℤ) *
        (((N - (i + 1) : ℕ) : ℤ) + (N : ℤ) - 2 * i)) :
    ∀ i, i < N → a i = ((N - (i + 1) : ℕ) : ℤ) := by
  have hpartial := sum_range_eq_zero_of_sum_smul_eq_zero
    (d := fun i => ((N - (i + 1) : ℕ) : ℤ) - a i)
    (w := fun i => ((N - (i + 1) : ℕ) : ℤ) + a i + N - 2 * i)
    (fun k hk => by rw [Finset.sum_sub_distrib]; exact sub_nonneg.mpr (hmajor k hk))
    (by rw [Finset.sum_sub_distrib, hsum, sub_self])
    (fun k hk => by have := ha k hk; omega)
    (by
      simp only [smul_eq_mul]
      rw [← sub_eq_zero.mpr hcasimir.symm, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
  intro i hi
  have hsucc := hpartial (i + 1) hi
  rw [Finset.sum_range_succ, hpartial i hi.le, zero_add, sub_eq_zero] at hsucc
  exact hsucc.symm

end TauCeti
