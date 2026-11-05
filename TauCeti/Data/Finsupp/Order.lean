/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Order

/-!
# Order decompositions and vanishing criteria for finitely supported functions

If a nonnegative finitely supported function into an ordered cancellative additive monoid has total
sum equal to its value at a single index, then all off-index values vanish
(`Finsupp.eq_zero_of_sum_eq_apply_of_nonneg`).

On a linearly ordered index type, a finitely supported function splits into its coordinates below a
chosen index, its value at that index, and its coordinates above it. A natural-valued finitely
supported function with an index below `l` in its support splits as `single i 1 + g`, where `i < l`
and every index in the support of `g` is at least `i`. This decomposition supports induction on
ordered monomials by removing one occurrence of their least variable.
-/

public section

namespace Finsupp

/-- If a finitely supported function into an ordered cancellative additive commutative monoid is
nonnegative and its sum equals its value at `a`, then it vanishes away from `a`. -/
theorem eq_zero_of_sum_eq_apply_of_nonneg {ι M : Type*} [AddCommMonoid M] [PartialOrder M]
    [IsOrderedCancelAddMonoid M] {f : ι →₀ M} (hf : 0 ≤ f) {a b : ι}
    (hsum : (f.sum fun _ c ↦ c) = f a) (hba : b ≠ a) : f b = 0 := by
  classical
  have hle : f a + f b ≤ f a + 0 :=
    calc f a + f b
        ≤ ∑ k ∈ insert a (insert b f.support), f k :=
          Finset.add_le_sum (fun i _ ↦ hf i) (Finset.mem_insert_self _ _)
            (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) hba.symm
      _ = f.sum fun _ c ↦ c :=
          (sum_of_support_subset f
            (s := insert a (insert b f.support))
            (fun _ h ↦ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
            (fun _ c ↦ c) (fun _ _ ↦ rfl)).symm
      _ = f a + 0 := by rw [hsum, add_zero]
  exact le_antisymm (le_of_add_le_add_left hle) (hf b)

variable {ι : Type*} [LinearOrder ι]

/-- A finitely supported function splits into its values before `i`, at `i`, and after `i`. -/
theorem filter_lt_add_single_add_filter_gt {M : Type*} [AddZeroClass M] (f : ι →₀ M) (i : ι) :
    f.filter (· < i) + single i (f i) + f.filter (i < ·) = f := by
  ext j
  rcases lt_trichotomy j i with hj | rfl | hj
  · simp [hj, hj.not_gt, single_eq_of_ne hj.ne]
  · simp
  · simp [hj, hj.not_gt, single_eq_of_ne hj.ne']

/-- If the support of `f` is not bounded below by `l`, split off one occurrence of its least
index `i < l`. Every index in the remaining support is at least `i`. -/
theorem exists_eq_single_add_of_not_forall_le (f : ι →₀ ℕ) {l : ι}
    (h : ¬ ∀ i ∈ f.support, l ≤ i) :
    ∃ (i : ι) (g : ι →₀ ℕ), i < l ∧ (∀ j ∈ g.support, i ≤ j) ∧ f = single i 1 + g := by
  simp only [not_forall, not_le] at h
  obtain ⟨j, hj, hjl⟩ := h
  have hne : f.support.Nonempty := ⟨j, hj⟩
  let i := f.support.min' hne
  have hi : i ∈ f.support := f.support.min'_mem hne
  refine ⟨i, f - single i 1, (f.support.min'_le j hj).trans_lt hjl, fun k hk ↦ ?_, ?_⟩
  · exact f.support.min'_le k (support_tsub hk)
  · simpa only [add_comm] using (sub_add_single_one_cancel (mem_support_iff.1 hi)).symm

end Finsupp
