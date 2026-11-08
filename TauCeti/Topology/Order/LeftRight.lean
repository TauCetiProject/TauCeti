/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.LeftRightNhds

/-!
# Right-continuous functions on dense subsets

A function `g` that is right-continuous at every point before `T` exceeds a level `a` at some
time `t ≤ T` only if it already exceeds `a` at `T`, at some point of a given dense set `D` below
`T`, or at some point below `T` isolated on the right. So the supremum of `g` over `(-∞, T]` is
its supremum over `{T} ∪ ((D ∪ C) ∩ (-∞, T])`, where `C` is the set of points isolated on the
right. In a second countable space `D` may be taken countable and `C` is countable, so this
replaces a supremum over uncountably many times by a countable one.

## Main declarations

* `Dense.exists_mem_insert_inter_Iic_lt`: a value of `g` above `a` at a time `t ≤ T` is matched
  by a value above `a` at `T` or at a point of `(D ∪ C) ∩ (-∞, T]`.
* `TopologicalSpace.exists_countable_subset_Iic_exists_mem_lt`: in a second countable space,
  one countable set of times `≤ T` serves for every function right-continuous before `T`.
* `TauCeti.le_of_forall_rat_add_le`: a function right-continuous at `t + h` that does not
  increase along rational increments from `t` does not increase along the real increment `h`.
-/

public section

open Set

variable {ι α : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [LinearOrder α] [TopologicalSpace α] [ClosedIicTopology α]

/-- If `g` is right-continuous at every time before `T` and `a < g t` for some `t ≤ T`, then
`a < g s` for some `s` in `{T} ∪ ((D ∪ C) ∩ (-∞, T])`, for any dense set `D`, where `C` is the
set of points isolated on the right, that is, covered by some point. -/
theorem Dense.exists_mem_insert_inter_Iic_lt {D : Set ι} (hD : Dense D) {g : ι → α} {T t : ι}
    (hg : ∀ t < T, ContinuousWithinAt g (Ioi t) t) (htT : t ≤ T) {a : α} (ha : a < g t) :
    ∃ s ∈ insert T ((D ∪ {x | ∃ y, x ⋖ y}) ∩ Iic T), a < g s := by
  rcases htT.lt_or_eq with htT | rfl
  · obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' htT).1
      ((hg t htT).preimage_mem_nhdsWithin (Ioi_mem_nhds ha))
    by_cases hne : (Ioo t (min u T)).Nonempty
    · obtain ⟨s, hs, hsD⟩ := hD.inter_open_nonempty _ isOpen_Ioo hne
      exact ⟨s, Or.inr ⟨Or.inl hsD, hs.2.le.trans (min_le_right _ _)⟩,
        hsub ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩⟩
    · exact ⟨t, Or.inr ⟨Or.inr ⟨_, covBy_iff_Ioo_eq.2
        ⟨lt_min hu htT, not_nonempty_iff_eq_empty.1 hne⟩⟩, htT.le⟩, ha⟩
  · exact ⟨t, mem_insert _ _, ha⟩

/-- In a second countable space, every `T` has a countable set `S` of points `≤ T` such that
whenever `g` is right-continuous at every point before `T` and `a < g t` for some `t ≤ T`, also
`a < g s` for some `s ∈ S`. One may take `S = {T} ∪ ((D ∪ C) ∩ (-∞, T])` for a countable dense
set `D` and the countable set `C` of points isolated on the right. -/
theorem TopologicalSpace.exists_countable_subset_Iic_exists_mem_lt [SecondCountableTopology ι]
    (T : ι) :
    ∃ S : Set ι, S.Countable ∧ S ⊆ Iic T ∧ ∀ ⦃g : ι → α⦄,
      (∀ t < T, ContinuousWithinAt g (Ioi t) t) →
        ∀ ⦃t⦄, t ≤ T → ∀ ⦃a⦄, a < g t → ∃ s ∈ S, a < g s :=
  let ⟨D, hDc, hD⟩ := exists_countable_dense ι
  ⟨insert T ((D ∪ {x | ∃ y, x ⋖ y}) ∩ Iic T),
    ((hDc.union countable_setOfPred_covBy_right).mono inter_subset_left).insert T,
    insert_subset_iff.2 ⟨le_rfl, inter_subset_right⟩,
    fun _ hg _ htT _ ha ↦ hD.exists_mem_insert_inter_Iic_lt hg htT ha⟩

section Rational

open Filter
open scoped Topology

/-- A function that is right-continuous at `t + h` and does not increase along rational
increments from `t` does not increase along the real increment `h ≥ 0`. -/
theorem TauCeti.le_of_forall_rat_add_le {β : Type*} [Preorder β] [TopologicalSpace β]
    [ClosedIicTopology β] {G : ℝ → β} {t h : ℝ} (hh : 0 ≤ h)
    (hG : Tendsto G (𝓝[>] (t + h)) (𝓝 (G (t + h))))
    (hanti : ∀ q : ℚ, 0 ≤ q → G (t + q) ≤ G t) : G (t + h) ≤ G t := by
  obtain ⟨r, -, hr, hid⟩ := Real.exists_seq_rat_strictAnti_tendsto h
  have hshift : Tendsto (fun n => t + (r n : ℝ)) atTop (𝓝[>] (t + h)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_const_nhds.add hid) (Eventually.of_forall fun n => ?_)
    exact mem_Ioi.2 (by linarith [hr n])
  refine le_of_tendsto (hG.comp hshift) (Eventually.of_forall fun n => ?_)
  exact hanti (r n) (by exact_mod_cast (hh.trans (hr n).le))

end Rational
