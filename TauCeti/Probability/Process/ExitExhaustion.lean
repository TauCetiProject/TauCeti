/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.Order.WithTop

/-!
# Exhaustion of first exits from expanding open domains

A continuous path remains in one member of an increasing open cover on each compact time
interval. Consequently, its native `MeasureTheory.hittingAfter` times for the complements
eventually exceed every finite horizon. This is the pathwise exhaustion step in localization
arguments; it asserts neither measurability nor a stopping-time property of the exits.

The proof uses `IsCompact.elim_directed_cover`, applied to the image of a compact time interval.
-/

public section

open Filter MeasureTheory Set Topology
open scoped NNReal

namespace Continuous

variable {E Ω : Type*} [TopologicalSpace E] {X : ℝ≥0 → Ω → E} {ω : Ω}

/-- First exits of a continuous path from an increasing open cover eventually lie strictly
beyond every finite horizon. The sets need only cover this path, not the entire state space. -/
theorem eventually_lt_hittingAfter_compl (hX : Continuous (X · ω))
    {U : ℕ → Set E} (hU : ∀ n, IsOpen (U n)) (hmono : Monotone U)
    (hcover : ∀ t, ∃ n, X t ω ∈ U n) (T : ℝ≥0) :
    ∀ᶠ n in atTop, (T : WithTop ℝ≥0) < hittingAfter X (U n)ᶜ 0 ω := by
  obtain ⟨N, hN⟩ := (isCompact_Icc.image hX).elim_directed_cover U hU
    (by rintro _ ⟨t, _, rfl⟩; exact mem_iUnion.mpr (hcover t)) hmono.directed_le
  filter_upwards [eventually_ge_atTop N] with n hn
  have hbound : ((T + 1 : ℝ≥0) : WithTop ℝ≥0) ≤ hittingAfter X (U n)ᶜ 0 ω := by
    rw [← not_lt, hittingAfter_lt_iff]
    rintro ⟨t, ht, hnot⟩
    exact hnot (hmono hn (hN ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩))
  exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (lt_add_one T)) hbound

/-- First exits of a continuous path from an increasing open cover tend to infinity.
No probabilistic or filtration assumptions are needed. -/
theorem tendsto_hittingAfter_compl (hX : Continuous (X · ω))
    {U : ℕ → Set E} (hU : ∀ n, IsOpen (U n)) (hmono : Monotone U)
    (hcover : ∀ t, ∃ n, X t ω ∈ U n) :
    Tendsto (fun n ↦ hittingAfter X (U n)ᶜ 0 ω) atTop (𝓝 ⊤) := by
  exact (WithTop.tendsto_nhds_top_iff _).mpr fun T ↦
    hX.eventually_lt_hittingAfter_compl hU hmono hcover T

end Continuous
