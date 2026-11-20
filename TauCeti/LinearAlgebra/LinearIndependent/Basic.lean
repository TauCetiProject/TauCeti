/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Order.Preorder.Finite

/-!
# Linear independence on the image of an injective reindexing

A family `v` is linearly independent on the image `f '' s` of a set under a map injective on `s`
exactly when `v ∘ f` is linearly independent on `s`. This is the linear counterpart of Mathlib's
`affineIndepOn_image_iff`, combining `LinearIndepOn.comp_of_image` and
`LinearIndepOn.image_of_comp`.

A unitriangular change of a linearly independent family indexed by a preorder, where each `z j`
is `x j` plus a combination of the `x l` with `l < j`, is again linearly independent.

## Main results

* `TauCeti.linearIndepOn_image_iff`: linear independence on `f '' s` versus of `v ∘ f` on `s`.
* `LinearIndependent.of_sub_mem_span_image_Iio`: unitriangular changes preserve linear
  independence.
-/

public section

namespace TauCeti

variable {ι ι' R M : Type*}

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- A family `v` is linearly independent on `f '' s` exactly when `v ∘ f` is linearly independent
on `s`, for `f` injective on `s`. -/
theorem linearIndepOn_image_iff {s : Set ι} {f : ι → ι'} (v : ι' → M) (hf : Set.InjOn f s) :
    LinearIndepOn R v (f '' s) ↔ LinearIndepOn R (v ∘ f) s :=
  ⟨fun h ↦ h.comp_of_image hf, fun h ↦ h.image_of_comp f v⟩

end Semiring

section Unitriangular

open Submodule

variable [Ring R] [AddCommGroup M] [Module R M] [Preorder ι]

/-- A unitriangular change of a linearly independent family, where every `z j` is `x j` plus a
combination of the earlier `x l`, is linearly independent. -/
theorem _root_.LinearIndependent.of_sub_mem_span_image_Iio {x z : ι → M}
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

end Unitriangular

end TauCeti
