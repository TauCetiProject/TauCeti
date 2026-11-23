/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Order.Preorder.Finite

/-!
# Unitriangular changes of a family

Let `x` and `z` be families of vectors indexed by a preorder, such that every `z j` is `x j` plus
a combination of the earlier `x l`. Such corrections occur when a basis is improved one vector at
a time, as in Evertse's lemma. Then `z` is linearly independent when `x` is
(`LinearIndependent.of_sub_mem_span`), over any ring: in a relation among the `z j`, the
coefficient of `x m` for a maximal index `m` of its support is the coefficient of `z m`. When the
order is well founded, `z` also spans what `x` spans
(`Submodule.span_range_eq_span_range_of_sub_mem_span`).
-/

public section

open Submodule

variable {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M] [Preorder ι] {x z : ι → M}

/-- A family in which every `z j` is `x j` plus a combination of the earlier `x l` is linearly
independent when `x` is. -/
theorem LinearIndependent.of_sub_mem_span (hx : LinearIndependent R x)
    (h : ∀ j, z j - x j ∈ span R (x '' Set.Iio j)) : LinearIndependent R z := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  by_contra hne
  obtain ⟨m, hm, hmax⟩ := (s.filter (g · ≠ 0)).exists_maximal ⟨i, Finset.mem_filter.2 ⟨hi, hne⟩⟩
  rw [Finset.mem_filter] at hm
  -- No index of the relation lies above `m`, so the corrections avoid `x m`.
  have hsub (j : ι) (hj : j ∈ s) (hgj : g j ≠ 0) : x '' Set.Iio j ⊆ x '' (Set.univ \ {m}) :=
    Set.image_mono fun l (hl : l < j) ↦ Set.mem_sdiff_singleton.2 ⟨trivial, fun hlm ↦
      (hlm ▸ hl).not_ge (hmax (Finset.mem_filter.2 ⟨hj, hgj⟩) (hlm ▸ hl).le)⟩
  have hz : ∑ j ∈ s, g j • z j =
      ∑ j ∈ s, g j • (z j - x j) + (g m • x m + ∑ j ∈ s.erase m, g j • x j) := by
    rw [Finset.add_sum_erase s (fun j ↦ g j • x j) hm.1, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [← smul_add, sub_add_cancel]
  rw [hg, add_left_comm] at hz
  refine hm.2 (hx.eq_zero_of_smul_mem_span m (g m) ?_)
  rw [eq_neg_of_add_eq_zero_left hz.symm]
  refine neg_mem (add_mem (sum_mem fun j hj ↦ ?_) (sum_mem fun j hj ↦ smul_mem _ _ <|
    subset_span ⟨j, Set.mem_sdiff_singleton.2 ⟨trivial, Finset.ne_of_mem_erase hj⟩, rfl⟩))
  by_cases hgj : g j = 0
  · simp [hgj]
  · exact smul_mem _ _ (span_mono (hsub j hj hgj) (h j))
