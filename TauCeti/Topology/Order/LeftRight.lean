/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.LeftRightNhds
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# Right-continuous functions on dense subsets

A function `g` that is right-continuous at every point before `T` exceeds a level `a` at some
time `t ≤ T` only if it already exceeds `a` at `T` or at some point of a given dense set below `T`.
So the supremum of `g` over `(-∞, T]` is its supremum over `{T} ∪ (D ∩ (-∞, T])`; with `D`
countable, this replaces a supremum over uncountably many times by a countable one.

## Main declarations

* `Dense.exists_mem_insert_inter_Iic_lt`: a value of `g` above `a` at a time `t ≤ T` is matched
  by a value above `a` at `T` or at a point of `D ∩ (-∞, T]`.
* `TopologicalSpace.exists_countable_subset_Iic_exists_mem_lt`: in a separable space, one
  countable set of times `≤ T` serves for every function right-continuous before `T`.
* `eventually_nhdsGT_pos_and_mul_abs_lt`: as `h → 0⁺`, eventually `0 < h` and `c * |h| < r`.
-/

public section

open Set

variable {ι α : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι]
  [LinearOrder α] [TopologicalSpace α] [ClosedIicTopology α]

/-- If `g` is right-continuous at every time before `T` and `a < g t` for some `t ≤ T`, then
`a < g s` for some `s` in `{T} ∪ (D ∩ (-∞, T])`, for any dense set `D`. -/
theorem Dense.exists_mem_insert_inter_Iic_lt {D : Set ι} (hD : Dense D) {g : ι → α} {T t : ι}
    (hg : ∀ t < T, ContinuousWithinAt g (Ioi t) t) (htT : t ≤ T) {a : α} (ha : a < g t) :
    ∃ s ∈ insert T (D ∩ Iic T), a < g s := by
  rcases htT.lt_or_eq with htT | rfl
  · obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' htT).1
      ((hg t htT).preimage_mem_nhdsWithin (Ioi_mem_nhds ha))
    obtain ⟨s, hsD, hs⟩ := hD.exists_between (lt_min hu htT)
    exact ⟨s, Or.inr ⟨hsD, hs.2.le.trans (min_le_right _ _)⟩,
      hsub ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩⟩
  · exact ⟨t, mem_insert _ _, ha⟩

/-- In a separable space, every `T` has a countable set `S` of points `≤ T` such that whenever `g`
is right-continuous at every point before `T` and `a < g t` for some `t ≤ T`, also `a < g s` for
some `s ∈ S`. One may take `S = {T} ∪ (D ∩ (-∞, T])` for a countable dense set `D`. -/
theorem TopologicalSpace.exists_countable_subset_Iic_exists_mem_lt [SeparableSpace ι] (T : ι) :
    ∃ S : Set ι, S.Countable ∧ S ⊆ Iic T ∧ ∀ ⦃g : ι → α⦄,
      (∀ t < T, ContinuousWithinAt g (Ioi t) t) →
        ∀ ⦃t⦄, t ≤ T → ∀ ⦃a⦄, a < g t → ∃ s ∈ S, a < g s :=
  let ⟨D, hDc, hD⟩ := exists_countable_dense ι
  ⟨insert T (D ∩ Iic T), (hDc.mono inter_subset_left).insert T,
    insert_subset_iff.2 ⟨le_rfl, inter_subset_right⟩,
    fun _ hg _ htT _ ha ↦ hD.exists_mem_insert_inter_Iic_lt hg htT ha⟩

open Filter Topology in
/-- Along `h → 0⁺`, eventually `0 < h` and `c * |h| < r`, for any `c` and positive `r`. -/
theorem eventually_nhdsGT_pos_and_mul_abs_lt (c : ℝ) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h ∧ c * |h| < r := by
  have hlt : ∀ᶠ h : ℝ in 𝓝 (0 : ℝ), c * |h| < r := by
    have : Continuous fun h : ℝ ↦ c * |h| := continuous_const.mul continuous_abs
    exact this.continuousAt.eventually_lt continuousAt_const (by simpa using hr)
  exact (eventually_mem_nhdsWithin.and (hlt.filter_mono nhdsWithin_le_nhds)).mono fun h hh ↦
    ⟨hh.1, hh.2⟩
