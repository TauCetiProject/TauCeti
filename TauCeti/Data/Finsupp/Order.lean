/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Order

/-!
# Order decompositions and vanishing criteria for finitely supported functions

A nonnegative finitely supported function into an ordered additive monoid has total sum zero
exactly when it vanishes (`Finsupp.sum_eq_zero_iff_of_nonneg`). If the monoid is moreover
cancellative, its total sum equals its value at a single index exactly when all off-index values
vanish (`Finsupp.sum_eq_apply_iff_of_nonneg`).

On a linearly ordered index type, a finitely supported function splits into its coordinates below a
chosen index, its value at that index, and its coordinates above it. A natural-valued finitely
supported function with an index below `l` in its support splits as `single i 1 + g`, where `i < l`
and every index in the support of `g` is at least `i`. This decomposition supports induction on
ordered monomials by removing one occurrence of their least variable.

It also contains the residual step of the staircase argument: two nonnegative finitely supported
functions of equal mass lose their smaller matched weight, leaving smaller supports; and the
support characterization `Finsupp.single_one_add_single_one_le_iff` of division by a squarefree
quadratic monomial `single u 1 + single v 1` (`u ≠ v`).
-/

public section

namespace Finsupp

/-- For a natural-valued finitely supported function `f`, `single u 1 ≤ f` holds if and only if
`u ∈ f.support`. -/
theorem single_one_le_iff {σ : Type*} {f : σ →₀ ℕ} {u : σ} :
    single u 1 ≤ f ↔ u ∈ f.support := by
  rw [single_le_iff, Nat.one_le_iff_ne_zero, mem_support_iff]

/-- For distinct indices `u ≠ v`, a natural-valued finitely supported function `f` bounds
`single u 1 + single v 1` if and only if both `u` and `v` lie in `f.support`. -/
theorem single_one_add_single_one_le_iff {σ : Type*} {f : σ →₀ ℕ} {u v : σ} (huv : u ≠ v) :
    single u 1 + single v 1 ≤ f ↔ u ∈ f.support ∧ v ∈ f.support := by
  classical
  rw [le_iff, support_single_add_single huv one_ne_zero one_ne_zero]
  simp [huv, huv.symm, Nat.one_le_iff_ne_zero]

/-- Mapping values along a strictly monotone zero-preserving map reflects and preserves the
pointwise `≤` order on finitely supported functions. -/
theorem mapRange_le_mapRange_iff {ι α β : Type*} [Zero α] [Zero β] [LinearOrder α] [Preorder β]
    {f : α → β} (hf : StrictMono f) (hf₀ : f 0 = 0) {g₁ g₂ : ι →₀ α} :
    g₁.mapRange f hf₀ ≤ g₂.mapRange f hf₀ ↔ g₁ ≤ g₂ := by
  simp [Finsupp.le_def, hf.le_iff_le]

/-- Mapping values along a strictly monotone zero-preserving map reflects and preserves the
pointwise `<` order on finitely supported functions. -/
theorem mapRange_lt_mapRange_iff {ι α β : Type*} [Zero α] [Zero β] [LinearOrder α] [Preorder β]
    {f : α → β} (hf : StrictMono f) (hf₀ : f 0 = 0) {g₁ g₂ : ι →₀ α} :
    g₁.mapRange f hf₀ < g₂.mapRange f hf₀ ↔ g₁ < g₂ := by
  simp [lt_iff_le_not_ge, mapRange_le_mapRange_iff hf hf₀]

/-- A nonnegative finitely supported function has total mass zero if and only if it vanishes. -/
theorem sum_eq_zero_iff_of_nonneg {ι M : Type*} [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M] {f : ι →₀ M} (hf : 0 ≤ f) :
    f.sum (fun _ r ↦ r) = 0 ↔ f = 0 := by
  rw [Finsupp.sum, Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hf i]
  simp [Finsupp.ext_iff]

/-- A nonnegative finitely supported function into a cancellative ordered additive commutative
monoid has total sum equal to its value at `a` if and only if it vanishes away from `a`. -/
theorem sum_eq_apply_iff_of_nonneg {ι M : Type*} [AddCommMonoid M] [IsLeftCancelAdd M]
    [PartialOrder M] [IsOrderedAddMonoid M] {f : ι →₀ M} (hf : 0 ≤ f) {a : ι} :
    (f.sum fun _ c ↦ c) = f a ↔ ∀ b ≠ a, f b = 0 := by
  classical
  have herase : 0 ≤ f.erase a := fun i ↦ by
    rw [erase_apply]; split_ifs; exacts [le_rfl, hf i]
  rw [← add_sum_erase' f a _ fun _ ↦ rfl, add_eq_left, sum_eq_zero_iff_of_nonneg herase,
    Finsupp.ext_iff]
  refine forall_congr' fun b ↦ ?_
  by_cases hb : b = a <;> simp [hb]

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
  [ExistsAddOfLE R]

/-- Removing the smaller of the weights at `a` and `b` from both marginals leaves nonnegative
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
  -- The residual weights `d` at `a` and `e` at `b` left after removing `c`.
  obtain ⟨d, hd⟩ : ∃ d, f a = c + d := exists_add_of_le (min_le_left (f a) (g b))
  obtain ⟨e, he⟩ : ∃ e, g b = c + e := exists_add_of_le (min_le_right (f a) (g b))
  let f' := f.update a d
  let g' := g.update b e
  have hf' : 0 ≤ f' := by
    intro i
    by_cases hi : i = a
    · subst i
      simpa [f'] using (le_add_iff_nonneg_right c).1 (hd ▸ min_le_left (f a) (g b))
    · simpa [f', update_apply, hi] using hf i
  have hg' : 0 ≤ g' := by
    intro i
    by_cases hi : i = b
    · subst i
      simpa [g'] using (le_add_iff_nonneg_right c).1 (he ▸ min_le_right (f a) (g b))
    · simpa [g', update_apply, hi] using hg i
  have hfs : f'.support ⊆ f.support :=
    (support_update_subset _ _).trans (insert_eq_of_mem ha).subset
  have hgs : g'.support ⊆ g.support :=
    (support_update_subset _ _).trans (insert_eq_of_mem hb).subset
  have hcard : f'.support.card + g'.support.card < f.support.card + g.support.card := by
    have hfcard := card_le_card hfs
    have hgcard := card_le_card hgs
    rcases le_total (f a) (g b) with hle | hle
    · have hna : a ∉ f'.support := by
        simpa [f', c, min_eq_left hle] using hd
      have hlt := card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨hfs, fun h => hna (h.symm ▸ ha)⟩)
      omega
    · have hnb : b ∉ g'.support := by
        simpa [g', c, min_eq_right hle] using he
      have hlt := card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨hgs, fun h => hnb (h.symm ▸ hb)⟩)
      omega
  -- Adding the removed weight `c` back recovers the original marginals.
  have hfr : single a c + f' = f := by
    ext i
    by_cases hi : i = a <;> simp [f', hi, ← hd]
  have hgr : single b c + g' = g := by
    ext i
    by_cases hi : i = b <;> simp [g', hi, ← he]
  refine ⟨c, f', g', le_min (hf a) (hg b), hf', hg', hfs, hgs, hcard, ?_, hfr, hgr⟩
  rw [← hfr, ← hgr] at hmass
  simpa [sum_add_index] using hmass

end Residual

end Finsupp
