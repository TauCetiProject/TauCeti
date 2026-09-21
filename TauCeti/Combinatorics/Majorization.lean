/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Module

import Mathlib.Tactic

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
  let t : ℕ → ℤ := fun i => ((N - (i + 1) : ℕ) : ℤ)
  let d : ℕ → ℤ := fun i => t i - a i
  let q : ℕ → ℤ := fun i => t i + a i + N - 2 * i
  have hsum_range : (∑ i ∈ Finset.range N, d i) = 0 := by
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    exact hsum.symm
  have hdq (i : ℕ) :
      d i * q i = t i * (t i + N - 2 * i) - a i * (a i + N - 2 * i) := by
    simp only [d, q]
    ring
  have hcasimir_range : (∑ i ∈ Finset.range N, d i * q i) = 0 := by
    calc
      _ = ∑ i ∈ Finset.range N,
          (t i * (t i + N - 2 * i) - a i * (a i + N - 2 * i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hdq i
      _ = (∑ i ∈ Finset.range N, t i * (t i + N - 2 * i)) -
          ∑ i ∈ Finset.range N, a i * (a i + N - 2 * i) :=
        by rw [Finset.sum_sub_distrib]
      _ = 0 := sub_eq_zero.mpr hcasimir.symm
  have hpartial_nonneg (k : ℕ) (hk : k < N) :
      0 ≤ ∑ i ∈ Finset.range k, d i := by
    rw [Finset.sum_sub_distrib]
    exact sub_nonneg.mpr (hmajor k hk)
  have hqdiff (k : ℕ) (hk : k + 1 < N) : 0 < q k - q (k + 1) := by
    have hak := ha k hk
    simp only [q, t]
    omega
  have hparts := Finset.sum_range_by_parts q d N
  simp only [smul_eq_mul] at hparts
  have hdecomp :
      (∑ k ∈ Finset.range (N - 1), (∑ i ∈ Finset.range (k + 1), d i) *
        (q k - q (k + 1))) = 0 := by
    calc
      _ = -(∑ k ∈ Finset.range (N - 1),
          (q (k + 1) - q k) * (∑ i ∈ Finset.range (k + 1), d i)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = q (N - 1) * (∑ i ∈ Finset.range N, d i) -
          ∑ k ∈ Finset.range (N - 1),
            (q (k + 1) - q k) * (∑ i ∈ Finset.range (k + 1), d i) := by
        rw [hsum_range, mul_zero, zero_sub]
      _ = ∑ i ∈ Finset.range N, q i * d i := hparts.symm
      _ = ∑ i ∈ Finset.range N, d i * q i := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := hcasimir_range
  have hterms_nonneg : ∀ k ∈ Finset.range (N - 1),
      0 ≤ (∑ i ∈ Finset.range (k + 1), d i) * (q k - q (k + 1)) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have hkN : k + 1 < N := by omega
    exact mul_nonneg (hpartial_nonneg (k + 1) hkN) (le_of_lt (hqdiff k hkN))
  have hterm_zero : ∀ k ∈ Finset.range (N - 1),
      (∑ i ∈ Finset.range (k + 1), d i) * (q k - q (k + 1)) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hterms_nonneg).mp hdecomp
  have hpartial_zero (k : ℕ) (hk : k ≤ N) :
      (∑ i ∈ Finset.range k, d i) = 0 := by
    rcases eq_or_lt_of_le hk with rfl | hkN
    · exact hsum_range
    rcases k with _ | k
    · simp
    · have hprod := hterm_zero k (by simp only [Finset.mem_range]; omega)
      exact (mul_eq_zero.mp hprod).resolve_right (ne_of_gt (hqdiff k (by omega)))
  intro i hiN
  have hdi : d i = 0 := by
    have hnext := hpartial_zero (i + 1) (by omega)
    rw [Finset.sum_range_succ, hpartial_zero i (by omega), zero_add] at hnext
    exact hnext
  have hti : t i - a i = 0 := by simpa only [d] using hdi
  simpa only [t] using (sub_eq_zero.mp hti).symm

end TauCeti
