/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Order.IsLUB
public import TauCeti.Topology.Order.Interval

/-!
# Nested partitions recovering total variation

Every function on a compact real interval admits nested finite partitions with arbitrarily
small gaps whose variation sums converge to its full extended variation. No continuity or
bounded-variation hypothesis is needed, and the limit may be infinite. The sequence is chosen
depending on the function; convergence along every fine partition sequence is not asserted.

Partitions are represented by finite sets containing both endpoints. Their variation sums are
`eVariationOn f` on those finite sets: Mathlib's `eVariationOn.image_range_of_monotone`
identifies these with sums of successive distances in an increasing enumeration. Refinement
increases these sums by `eVariationOn.mono`.

We use the native supremum-sequence selection `IsLUB.exists_seq_monotone_tendsto`, then
adjoin finite ball covers and all earlier partition points. These partitions provide pathwise
approximations for finite-variation integration.
-/

public section

open Set Filter Topology

namespace eVariationOn

variable {α E : Type*} [LinearOrder α] [TopologicalSpace E] [WeakPseudoEMetricSpace E]

/-- Total variation is the supremum of the variation sums over finite subsets. -/
theorem eq_iSup_finset (f : α → E) (s : Set α) :
    eVariationOn f s =
      ⨆ p : {p : Finset α // (p : Set α) ⊆ s}, eVariationOn f (p : Set α) := by
  classical
  apply le_antisymm
  · refine iSup_le ?_
    rintro ⟨n, u, hu, hus⟩
    let p := (Finset.range (n + 1)).image u
    have hp : (p : Set α) ⊆ s := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact hus i
    refine (sum_le_of_monotoneOn_Iic (hu.monotoneOn _) ?_).trans
      (le_iSup (fun p : {p : Finset α // (p : Set α) ⊆ s} =>
        eVariationOn f (p : Set α)) ⟨p, hp⟩)
    intro i hi
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
  · exact iSup_le fun p => mono f p.property

/-- Finite variation sums approaching total variation can be chosen nested and containing
any prescribed sequence of finite subsets. This includes infinite total variation. -/
theorem exists_monotone_finset_tendsto (f : α → E) (s : Set α)
    (q : ℕ → Finset α) (hq : ∀ n, (q n : Set α) ⊆ s) :
    ∃ p : ℕ → Finset α, Monotone p ∧ (∀ n, (p n : Set α) ⊆ s) ∧
      (∀ n, q n ⊆ p n) ∧
      Tendsto (fun n => eVariationOn f (p n : Set α)) atTop (𝓝 (eVariationOn f s)) := by
  classical
  let v (p : {p : Finset α // (p : Set α) ⊆ s}) := eVariationOn f (p : Set α)
  have hsup : IsLUB (range v) (eVariationOn f s) := by
    rw [eq_iSup_finset]
    exact isLUB_iSup
  obtain ⟨w, -, -, hw, hwr⟩ := hsup.exists_seq_monotone_tendsto
    ⟨v ⟨∅, by simp⟩, mem_range_self _⟩
  choose u hu using hwr
  let p (n : ℕ) := (Finset.range (n + 1)).biUnion (fun i => (u i).val ∪ q i)
  have hsub (n) : (p n : Set α) ⊆ s := by
    intro x hx
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hx
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (u i).property hi
    · exact hq i hi
  have hu_le (n) : (u n).val ⊆ p n := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨n, by simp, Finset.mem_union_left _ hx⟩
  refine ⟨p, ?_, hsub, ?_, ?_⟩
  · intro m n hmn
    exact Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.range_mono (by omega))
  · intro n x hx
    exact Finset.mem_biUnion.mpr ⟨n, by simp, Finset.mem_union_right _ hx⟩
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le hw tendsto_const_nhds
    · intro n
      rw [← hu n]
      exact mono f (hu_le n)
    · intro n
      exact mono f (hsub n)

end eVariationOn

namespace TauCeti

/-- For every function on `[a,b]`, choose nested finite partitions with gaps at most
`1 / (n + 1)` whose successive-distance sums tend to the full extended variation.
No regularity is required of the function, and infinite variation is included. -/
theorem exists_nested_partitions_tendsto_eVariationOn
    {E : Type*} [TopologicalSpace E] [WeakPseudoEMetricSpace E]
    (f : ℝ → E) {a b : ℝ} (hab : a ≤ b) :
    ∃ p : ℕ → Finset ℝ, Monotone p ∧
      (∀ n, (p n : Set ℝ) ⊆ Icc a b ∧ a ∈ p n ∧ b ∈ p n) ∧
      (∀ n, ∀ x ∈ p n, ∀ y ∈ p n, x < y →
        (∀ z ∈ p n, x < z → y ≤ z) → y - x ≤ 1 / (n + 1 : ℝ)) ∧
      Tendsto (fun n => eVariationOn f (p n : Set ℝ)) atTop
        (𝓝 (eVariationOn f (Icc a b))) := by
  classical
  choose q hq hqa hqb hqgap using fun n : ℕ =>
    exists_finset_Icc_gap_le (ε := 1 / (n + 1 : ℝ)) hab (by positivity)
  obtain ⟨p, hp, hps, hqp, hlim⟩ :=
    eVariationOn.exists_monotone_finset_tendsto f (Icc a b) q hq
  refine ⟨p, hp, fun n => ⟨hps n, hqp n (hqa n), hqp n (hqb n)⟩, ?_, hlim⟩
  intro n x hx y hy hxy hgap
  -- Locate the cell of the coarser finite cover containing this refined gap.
  let l := (q n).filter (fun z => z ≤ x)
  have hl : l.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨hqa n, (hps n hx).1⟩⟩
  let r := (q n).filter (fun z => y ≤ z)
  have hr : r.Nonempty := ⟨b, Finset.mem_filter.mpr ⟨hqb n, (hps n hy).2⟩⟩
  have hlmem := Finset.mem_filter.mp (Finset.max'_mem l hl)
  have hrmem := Finset.mem_filter.mp (Finset.min'_mem r hr)
  have hcell : ∀ z ∈ q n, l.max' hl < z → r.min' hr ≤ z := by
    intro z hz hlz
    have hxz : x < z := by
      by_contra h
      have := Finset.le_max' l z (Finset.mem_filter.mpr ⟨hz, le_of_not_gt h⟩)
      exact (not_lt_of_ge this) hlz
    exact Finset.min'_le r z (Finset.mem_filter.mpr ⟨hz, hgap z (hqp n hz) hxz⟩)
  have hbound := hqgap n _ hlmem.1 _ hrmem.1 (by linarith [hlmem.2, hrmem.2]) hcell
  linarith [hlmem.2, hrmem.2]

end TauCeti
