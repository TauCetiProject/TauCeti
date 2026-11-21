/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SetFamily.LYM
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# The Littlewood–Offord counting bound

If real coefficients have absolute value at least `r > 0`, at most the central binomial
coefficient of their signed sums belong to any half-open interval of length `2 * r`.
Signs are indexed by subsets, with membership meaning a positive sign. Multiplicities of
coincident sums are retained. This is the combinatorial input to small-ball estimates for
independent Rademacher sums. Nonpositive radii are also allowed: their intervals are empty.

The proof is Erdős's antichain argument: first make the coefficients positive by reversing
the corresponding signs, then apply Sperner's theorem.

## References

* P. Erdős, *On a lemma of Littlewood and Offord*, Bull. Amer. Math. Soc. 51 (1945), 898–902.
-/

public section

open Finset
open scoped symmDiff

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- With coefficients at least `r > 0`, the subsets whose signed sums lie in a half-open
interval of length `2 * r` form an antichain. -/
theorem isAntichain_signedSum_mem_Ico {a : ι → ℝ} {r : ℝ}
    (ha : ∀ i, r ≤ a i) (x : ℝ) :
    IsAntichain (· ⊆ ·) {s : Finset ι |
      (∑ i, if i ∈ s then a i else -a i) ∈ Set.Ico x (x + 2 * r)} := by
  intro s hs t ht hst hsub
  have hr : 0 < r := by linarith [hs.1, hs.2]
  obtain ⟨j, hjt, hjs⟩ := not_subset.1 (fun hts ↦ hst (Subset.antisymm hsub hts))
  have hdiff : 2 * r ≤
      (∑ i, if i ∈ t then a i else -a i) -
        (∑ i, if i ∈ s then a i else -a i) := by
    rw [← sum_sub_distrib]
    calc
      2 * r ≤ (if j ∈ t then a j else -a j) -
          (if j ∈ s then a j else -a j) := by simp [hjt, hjs]; linarith [ha j]
      _ ≤ ∑ i, ((if i ∈ t then a i else -a i) -
          (if i ∈ s then a i else -a i)) := by
        apply single_le_sum (fun i _ ↦ ?_) (mem_univ j)
        by_cases his : i ∈ s
        · simp [his, hsub his]
        · by_cases hit : i ∈ t <;> simp [his, hit]
          linarith [ha i]
  exact (not_le_of_gt (by linarith [hs.1, ht.2])) hdiff

/-- **Littlewood–Offord counting bound.** At most `n.choose (n / 2)` signed sums of `n` real
coefficients of absolute value at least `r > 0` belong to a half-open interval of length `2r`.
The empty family is allowed. -/
theorem card_filter_signedSum_mem_Ico_le {a : ι → ℝ} {r : ℝ}
    (ha : ∀ i, r ≤ |a i|) (x : ℝ) :
    #{s : Finset ι | (∑ i, if i ∈ s then a i else -a i) ∈ Set.Ico x (x + 2 * r)} ≤
      (Fintype.card ι).choose (Fintype.card ι / 2) := by
  let neg : Finset ι := univ.filter fun i ↦ a i < 0
  have hsum (s : Finset ι) :
      (∑ i, if i ∈ s ∆ neg then |a i| else -|a i|) =
        ∑ i, if i ∈ s then a i else -a i := by
    apply sum_congr rfl
    intro i _
    by_cases hi : a i < 0 <;> by_cases his : i ∈ s <;>
      simp [neg, mem_symmDiff, hi, his, abs_of_neg, abs_of_nonneg, le_of_not_gt]
  have hcard :
      #{s : Finset ι | (∑ i, if i ∈ s then a i else -a i) ∈ Set.Ico x (x + 2 * r)} =
      #{s : Finset ι | (∑ i, if i ∈ s then |a i| else -|a i|) ∈ Set.Ico x (x + 2 * r)} := by
    apply card_bijective (fun s : Finset ι ↦ s ∆ neg)
      (Function.Involutive.bijective (fun s ↦ symmDiff_symmDiff_cancel_right neg s))
    intro s
    simp only [mem_filter, mem_univ, true_and, hsum]
  rw [hcard]
  exact ((isAntichain_signedSum_mem_Ico ha x).subset
    (fun s hs ↦ (mem_filter.1 hs).2)).sperner

end TauCeti
