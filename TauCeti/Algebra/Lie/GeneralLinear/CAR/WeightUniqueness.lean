/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Casimir

import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic

/-!
# Uniqueness of the staircase occupation weight

The half-integral weights arising from the CAR model have the form `a i + 1 / 2`, where `a` is a
tuple of natural-number occupation counts. This file isolates the finite inequality which
identifies `a`: if it is antitone, is majorized by the reverse-index tuple, has the same total sum,
and gives the same trace-form Casimir polynomial, then it is the reverse-index tuple.

The proof uses discrete summation by parts. For the target `t i = N - (i + 1)`, put

`D k = ∑ i < k, (t i - a i)` and `q i = t i + a i + N - 2i`.

The total-sum hypothesis says `D N = 0`, while the Casimir equality and summation by parts give

`0 = ∑ k < N - 1, D (k + 1) * (q k - q (k + 1))`.

Majorization makes every `D (k + 1)` nonnegative. Antitonicity of `a` makes every other factor
positive, since `q k - q (k + 1) = 3 + a k - a (k + 1)`. Thus all partial deficits vanish, which
recovers every coordinate of `a`.

## Main result

* `TauCeti.eq_fin_rev_of_antitone_of_prefix_sum_le_of_sum_eq_of_casimir_eq`: the reverse-index
  tuple is uniquely determined by dominance, its prefix sums, its total sum, and the trace-form
  Casimir polynomial.

## References

* G. H. Hardy, J. E. Littlewood, G. Pólya, *Inequalities*, Cambridge University Press (1952),
  Chapter 2, for majorization and summation by parts.
* D. Panyushev, *The exterior algebra and "spin" of an orthogonal g-module*, Transform. Groups 6
  (2001), 371–396, Proposition 2.4 and Example 2.5(1), for the CAR staircase-weight application.
-/

public section

namespace TauCeti

open scoped BigOperators

/-- Discrete summation by parts, written using initial sums of `d`.

The separate final term makes the statement valid without assuming that the total sum of `d`
vanishes. This is the algebraic identity used in the staircase uniqueness proof below. -/
private theorem sum_range_mul_eq_sum_range_partialSum_mul_sub_add
    (d q : ℕ → ℤ) : ∀ n : ℕ,
    (∑ i ∈ Finset.range n, d i * q i) =
      (∑ k ∈ Finset.range (n - 1), (∑ i ∈ Finset.range (k + 1), d i) *
        (q k - q (k + 1))) + (∑ i ∈ Finset.range n, d i) * q (n - 1) := by
  intro n
  have h := Finset.sum_range_by_parts q d n
  simp only [smul_eq_mul] at h
  calc
    _ = ∑ i ∈ Finset.range n, q i * d i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = q (n - 1) * (∑ i ∈ Finset.range n, d i) -
        ∑ k ∈ Finset.range (n - 1),
          (q (k + 1) - q k) * (∑ i ∈ Finset.range (k + 1), d i) := h
    _ = _ := by
      have hneg : -(∑ k ∈ Finset.range (n - 1),
          (q (k + 1) - q k) * (∑ i ∈ Finset.range (k + 1), d i)) =
          ∑ k ∈ Finset.range (n - 1),
            (∑ i ∈ Finset.range (k + 1), d i) * (q k - q (k + 1)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [sub_eq_add_neg, hneg]
      ring

/-- The natural-number sequence form of staircase uniqueness.

This form lets the proof use ordinary range sums. The public `Fin N` statement below is the API
for callers. -/
private theorem eq_staircase_of_antitone_of_prefix_sum_le_of_sum_eq_of_casimir_eq
    {N : ℕ} (a : ℕ → ℕ) (ha : ∀ i, i + 1 < N → a (i + 1) ≤ a i)
    (hmajor : ∀ (k : ℕ), k < N →
      (∑ i ∈ Finset.range k, (a i : ℤ)) ≤
        ∑ i ∈ Finset.range k, ((N - (i + 1) : ℕ) : ℤ))
    (hsum : (∑ i ∈ Finset.range N, (a i : ℤ)) =
      ∑ i ∈ Finset.range N, ((N - (i + 1) : ℕ) : ℤ))
    (hcasimir :
      (∑ i ∈ Finset.range N,
        (a i : ℤ) * ((a i : ℤ) + (N : ℤ) - 2 * i)) =
      ∑ i ∈ Finset.range N, ((N - (i + 1) : ℕ) : ℤ) *
        (((N - (i + 1) : ℕ) : ℤ) + (N : ℤ) - 2 * i)) :
    ∀ i, i < N → a i = N - (i + 1) := by
  let t : ℕ → ℤ := fun i => ((N - (i + 1) : ℕ) : ℤ)
  let d : ℕ → ℤ := fun i => t i - a i
  let q : ℕ → ℤ := fun i => t i + a i + N - 2 * i
  have hsum_range : (∑ i ∈ Finset.range N, d i) = 0 := by
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    exact hsum.symm
  have hcasimir_range : (∑ i ∈ Finset.range N, d i * q i) = 0 := by
    rw [show (∑ i ∈ Finset.range N, d i * q i) =
        (∑ i ∈ Finset.range N,
          (t i * (t i + N - 2 * i) - (a i : ℤ) * ((a i : ℤ) + N - 2 * i))) by
      apply Finset.sum_congr rfl
      intro i _
      simp only [d, q]
      ring]
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    exact hcasimir.symm
  have hpartial_nonneg (k : ℕ) (hk : k < N) :
      0 ≤ ∑ i ∈ Finset.range k, d i := by
    rw [Finset.sum_sub_distrib]
    exact sub_nonneg.mpr (hmajor k hk)
  have hqdiff (k : ℕ) (hk : k + 1 < N) : 0 < q k - q (k + 1) := by
    have hak := ha k hk
    simp only [q, t]
    push_cast at hak ⊢
    omega
  have hdecomp := sum_range_mul_eq_sum_range_partialSum_mul_sub_add d q N
  rw [hcasimir_range, hsum_range, zero_mul, add_zero] at hdecomp
  have hterms_nonneg : ∀ k ∈ Finset.range (N - 1),
      0 ≤ (∑ i ∈ Finset.range (k + 1), d i) * (q k - q (k + 1)) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have hkN : k + 1 < N := by omega
    exact mul_nonneg (hpartial_nonneg (k + 1) hkN) (le_of_lt (hqdiff k hkN))
  have hterm_zero : ∀ k ∈ Finset.range (N - 1),
      (∑ i ∈ Finset.range (k + 1), d i) * (q k - q (k + 1)) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hterms_nonneg).mp hdecomp.symm
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
  have hz : ((a i : ℕ) : ℤ) = ((N - (i + 1) : ℕ) : ℤ) := by
    change t i - (a i : ℤ) = 0 at hdi
    simpa only [t] using (sub_eq_zero.mp hdi).symm
  exact_mod_cast hz

/-- **A majorized occupation weight with the staircase Casimir value is the staircase.**

Let `a : Fin N → ℕ` be weakly decreasing. Suppose every initial sum of `a` is at most the
corresponding initial sum of the reverse-index tuple `i ↦ N - 1 - i`, and suppose the total sums
are equal. If the two tuples also have the same value under the integral form

`a ↦ ∑ i, a i * (a i + N - 2i)`

of the trace-form `gl_N` Casimir polynomial after a common half-unit shift, then `a` is the
reverse-index tuple. The prefix inequalities and total equality are the majorization condition;
the Casimir equality makes it strict enough to determine every coordinate. -/
theorem eq_fin_rev_of_antitone_of_prefix_sum_le_of_sum_eq_of_casimir_eq
    {N : ℕ} (a : Fin N → ℕ) (ha : Antitone a)
    (hmajor : ∀ (k : ℕ) (hk : k < N),
      (∑ i : Fin k, (a (Fin.castLE hk.le i) : ℤ)) ≤
        ∑ i : Fin k, ((Fin.rev (Fin.castLE hk.le i) : ℕ) : ℤ))
    (hsum : (∑ i : Fin N, (a i : ℤ)) =
      ∑ i : Fin N, ((Fin.rev i : ℕ) : ℤ))
    (hcasimir :
      (∑ i : Fin N, (a i : ℤ) * ((a i : ℤ) + (N : ℤ) - 2 * (i : ℕ))) =
        ∑ i : Fin N, ((Fin.rev i : ℕ) : ℤ) *
          (((Fin.rev i : ℕ) : ℤ) + (N : ℤ) - 2 * (i : ℕ))) :
    a = fun i => (Fin.rev i : ℕ) := by
  let aN : ℕ → ℕ := fun i => if hi : i < N then a ⟨i, hi⟩ else 0
  have haN : ∀ i, i + 1 < N → aN (i + 1) ≤ aN i := by
    intro i hi
    have hi' : i < N := by omega
    simpa only [aN, dite_eq_left hi, dite_eq_left hi'] using
      ha (Fin.mk_le_mk.mpr (Nat.le_succ i) : (⟨i, hi'⟩ : Fin N) ≤ ⟨i + 1, hi⟩)
  have hmajorN : ∀ (k : ℕ), k < N →
      (∑ i ∈ Finset.range k, (aN i : ℤ)) ≤
        ∑ i ∈ Finset.range k, ((N - (i + 1) : ℕ) : ℤ) := by
    intro k hk
    rw [← Fin.sum_univ_eq_sum_range (fun i => (aN i : ℤ)) k,
      ← Fin.sum_univ_eq_sum_range (fun i => ((N - (i + 1) : ℕ) : ℤ)) k]
    convert hmajor k hk using 1 <;> apply Finset.sum_congr rfl <;> intro i hi
    · have hiN : i < N := lt_trans i.isLt hk
      simp only [aN, dite_eq_left hiN]
      congr 1
    · rfl
  have hsumN : (∑ i ∈ Finset.range N, (aN i : ℤ)) =
      ∑ i ∈ Finset.range N, ((N - (i + 1) : ℕ) : ℤ) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => (aN i : ℤ)) N,
      ← Fin.sum_univ_eq_sum_range (fun i => ((N - (i + 1) : ℕ) : ℤ)) N]
    convert hsum using 1 <;> apply Finset.sum_congr rfl <;> intro i hi
    · simp [aN, i.isLt]
    · rfl
  have hcasimirN :
      (∑ i ∈ Finset.range N,
        (aN i : ℤ) * ((aN i : ℤ) + (N : ℤ) - 2 * i)) =
      ∑ i ∈ Finset.range N, ((N - (i + 1) : ℕ) : ℤ) *
        (((N - (i + 1) : ℕ) : ℤ) + (N : ℤ) - 2 * i) := by
    rw [← Fin.sum_univ_eq_sum_range
        (fun i => (aN i : ℤ) * ((aN i : ℤ) + (N : ℤ) - 2 * i)) N,
      ← Fin.sum_univ_eq_sum_range
        (fun i => ((N - (i + 1) : ℕ) : ℤ) *
          (((N - (i + 1) : ℕ) : ℤ) + (N : ℤ) - 2 * i)) N]
    convert hcasimir using 1 <;> apply Finset.sum_congr rfl <;> intro i hi
    · simp [aN, i.isLt]
    · rfl
  funext i
  have h := eq_staircase_of_antitone_of_prefix_sum_le_of_sum_eq_of_casimir_eq
    aN haN hmajorN hsumN hcasimirN i i.isLt
  simpa [aN, i.isLt, Fin.rev] using h

end TauCeti
