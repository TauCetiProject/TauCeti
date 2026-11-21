/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Order.Preorder.Finite

/-!
# Linear independence under a unitriangular change

Let `x` be a family indexed by a preorder, and let every `z j` be `x j` plus a combination of the
earlier `x l`. If `x` is linearly independent, then so is `z`. The family `x` need not span the
ambient module, and neither the index type nor the ring is restricted: in a vanishing combination
of the `z l`, a maximal index with a nonzero coefficient would give a nontrivial vanishing
combination of the `x l`.

## Main results

* `LinearIndependent.of_sub_mem_span_image_Iio`: a unitriangular change of a linearly independent
  family is linearly independent.

## Attribution

The statement and proof are those of the unmerged Tau Ceti pull request 34591.
-/

public section

open Submodule

variable {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M] [Preorder ι]

/-- **A unitriangular change of a linearly independent family is linearly independent.** Let `x`
be a family indexed by a preorder and let every `z j` be `x j` plus a combination of the earlier
`x l`. If `x` is linearly independent, then so is `z`. -/
theorem LinearIndependent.of_sub_mem_span_image_Iio {x z : ι → M}
    (hx : LinearIndependent R x) (h : ∀ j, z j - x j ∈ span R (x '' Set.Iio j)) :
    LinearIndependent R z := by
  classical
  refine linearIndependent_iff'.2 fun s g hg i hi ↦ by_contra fun hgi ↦ ?_
  -- A maximal index `j` of `s` with a nonzero coefficient.
  obtain ⟨j, hjmax⟩ :=
    (s.filter (g · ≠ 0)).exists_maximal ⟨i, Finset.mem_filter.2 ⟨hi, hgi⟩⟩
  obtain ⟨hjs, hj⟩ := Finset.mem_filter.1 hjmax.prop
  -- The other terms lie in the span of the `x l` with `l ≠ j`, hence so does `g j • x j`.
  have hrest : ∑ l ∈ s.erase j, g l • z l ∈ span R (x '' {j}ᶜ) := by
    refine sum_mem fun l hl ↦ ?_
    by_cases hgl : g l = 0
    · simp [hgl]
    have hjl : ¬j < l :=
      hjmax.not_gt (Finset.mem_filter.2 ⟨Finset.mem_of_mem_erase hl, hgl⟩)
    have hle := span_mono (Set.image_mono (show Set.Iio l ⊆ {j}ᶜ from
      fun m (hm : m < l) (hmj : m = j) ↦ hjl (hmj ▸ hm))) (h l)
    exact smul_mem _ _
      (by simpa using add_mem hle (subset_span ⟨l, Finset.ne_of_mem_erase hl, rfl⟩))
  rw [← Finset.add_sum_erase _ _ hjs] at hg
  have hmem := sub_mem (neg_mem hrest) (smul_mem _ (g j)
    (span_mono (Set.image_mono (show Set.Iio j ⊆ {j}ᶜ from fun _ hm ↦ ne_of_lt hm)) (h j)))
  rw [← eq_neg_of_add_eq_zero_left hg, smul_sub, sub_sub_cancel] at hmem
  have hx0 : g j • x j = 0 :=
    disjoint_def.1 (hx.disjoint_span_image disjoint_compl_left) _ hmem
      (by simpa using smul_mem _ (g j) (mem_span_singleton_self (x j)))
  exact hj (hx.smul_left_injective j (by simpa using hx0))
