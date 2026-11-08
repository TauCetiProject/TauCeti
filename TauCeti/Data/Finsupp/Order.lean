/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Order

/-!
# Decompositions of finitely supported functions on linear orders

A finitely supported function splits into its coordinates below a chosen index, its value at
that index, and its coordinates above it.

A natural-valued finitely supported function with an index below `l` in its support splits as
`single i 1 + g`, where `i < l` and every index in the support of `g` is at least `i`.
This decomposition supports induction on ordered monomials by removing one occurrence of
their least variable.

It also contains the residual step of the staircase argument: two nonnegative finitely supported
functions of equal mass lose their smaller matched weight, leaving smaller supports.
-/

public section

namespace Finsupp

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

section Residual

open Finset

variable {α β R : Type*} [AddCommMonoid R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
  [Sub R] [OrderedSub R] [ExistsAddOfLE R]

/-- A nonnegative finitely supported function of total mass zero vanishes. -/
theorem eq_zero_of_sum_eq_zero_of_nonneg {ι M : Type*} [AddCommMonoid M] [LinearOrder M]
    [IsOrderedCancelAddMonoid M] {f : ι →₀ M} (hf : 0 ≤ f)
    (h : f.sum (fun _ r => r) = 0) : f = 0 := by
  by_contra hne
  exact (ne_of_gt (f.sum_pos (g := fun _ r => r) (fun i hi => lt_of_le_of_ne (hf i)
    (mem_support_iff.mp hi).symm) hne)) h

/-- Subtracting the smaller of the weights at `a` and `b` from both marginals leaves nonnegative
residuals with smaller supports, and equal masses. -/
theorem exists_residual_marginals (f : α →₀ R) (g : β →₀ R) (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hmass : f.sum (fun _ r => r) = g.sum (fun _ r => r)) {a : α} {b : β}
    (ha : a ∈ f.support) (hb : b ∈ g.support) :
    ∃ (c : R) (f' : α →₀ R) (g' : β →₀ R), 0 ≤ c ∧ 0 ≤ f' ∧ 0 ≤ g' ∧
      f'.support ⊆ f.support ∧ g'.support ⊆ g.support ∧
      f'.support.card + g'.support.card < f.support.card + g.support.card ∧
      f'.sum (fun _ r => r) = g'.sum (fun _ r => r) ∧
      single a c + f' = f ∧ single b c + g' = g := by
  classical
  let c := min (f a) (g b)
  let f' := f.update a (f a - c)
  let g' := g.update b (g b - c)
  have hf' : 0 ≤ f' := by
    intro i
    by_cases hi : i = a
    · subst i
      simpa [f'] using (le_tsub_iff_right (min_le_left (f a) (g b))).mpr (by simp)
    · simpa [f', update_apply, hi] using hf i
  have hg' : 0 ≤ g' := by
    intro i
    by_cases hi : i = b
    · subst i
      simpa [g'] using (le_tsub_iff_right (min_le_right (f a) (g b))).mpr (by simp)
    · simpa [g', update_apply, hi] using hg i
  have hfs : f'.support ⊆ f.support := by
    simpa [ha] using support_update_subset f a (b := f a - c)
  have hgs : g'.support ⊆ g.support := by
    simpa [hb] using support_update_subset g b (b := g b - c)
  have hcard : f'.support.card + g'.support.card < f.support.card + g.support.card := by
    have hfcard := card_le_card hfs
    have hgcard := card_le_card hgs
    rcases le_total (f a) (g b) with hle | hle
    · have hna : a ∉ f'.support := by
        simp [f', c, min_eq_left hle, tsub_eq_of_eq_add (zero_add (f a)).symm]
      have hlt := card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨hfs, fun h => hna (h.symm ▸ ha)⟩)
      omega
    · have hnb : b ∉ g'.support := by
        simp [g', c, min_eq_right hle, tsub_eq_of_eq_add (zero_add (g b)).symm]
      have hlt := card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨hgs, fun h => hnb (h.symm ▸ hb)⟩)
      omega
  have hfr : single a c + f' = f := by
    ext i
    by_cases hi : i = a
    · subst i; simp [f', c]
    · simp [f', hi]
  have hgr : single b c + g' = g := by
    ext i
    by_cases hi : i = b
    · subst i; simp [g', c]
    · simp [g', hi]
  refine ⟨c, f', g', le_min (hf a) (hg b), hf', hg', hfs, hgs, hcard, ?_, hfr, hgr⟩
  rw [← hfr, ← hgr] at hmass
  simpa [sum_add_index] using hmass

end Residual

end Finsupp
