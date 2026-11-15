/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.IsLUB
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Sequences approaching the infimum of an image

For a function `f : X → β` into a first-countable conditionally complete linear order that is
bounded below on a nonempty set `s`, `Mathlib.Topology.Order.IsLUB.exists_seq_tendsto_sInf`
constructs an antitone sequence in `f '' s` converging to `sInf (f '' s)`. Lifting its terms back
to `s` yields a sequence `u : ℕ → X` in `s` with antitone values converging to `sInf (f '' s)`
(`TauCeti.exists_seq_forall_mem_and_tendsto_sInf`). For real-valued functions, one can also obtain
the quantitative bound `f (u n) < sInf (f '' s) + 1 / (n + 1)`
(`TauCeti.exists_seq_forall_mem_and_lt_sInf_add_one_div`).
-/

public section

open Filter Set Topology

namespace TauCeti

/-- On a nonempty set where `f` is bounded below in a first-countable conditionally complete
linear order, there exists a sequence in `s` with antitone values converging to
`sInf (f '' s)`. -/
theorem exists_seq_forall_mem_and_tendsto_sInf {X β : Type*}
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    [FirstCountableTopology β] {f : X → β} {s : Set X}
    (hne : s.Nonempty) (hbdd : BddBelow (f '' s)) :
    ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧ Antitone (f ∘ u) ∧
      Tendsto (fun n ↦ f (u n)) atTop (𝓝 (sInf (f '' s))) := by
  obtain ⟨y, hy_anti, hy_lim, hy_mem⟩ := exists_seq_tendsto_sInf (hne.image f) hbdd
  choose u hu hfu using hy_mem
  refine ⟨u, hu, fun i j hij ↦ ?_, by simpa only [hfu] using hy_lim⟩
  simpa only [Function.comp_apply, hfu] using hy_anti hij

/-- On a nonempty set where a real-valued function `f` is bounded below, there exists a sequence
`u` in `s` satisfying the quantitative bound `f (u n) < sInf (f '' s) + 1 / (n + 1)` and
converging in value to `sInf (f '' s)`. -/
theorem exists_seq_forall_mem_and_lt_sInf_add_one_div {X : Type*} {f : X → ℝ} {s : Set X}
    (hne : s.Nonempty) (hbdd : BddBelow (f '' s)) :
    ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧ (∀ n, f (u n) < sInf (f '' s) + 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n ↦ f (u n)) atTop (𝓝 (sInf (f '' s))) := by
  have hex (n : ℕ) : ∃ u ∈ s, f u < sInf (f '' s) + 1 / ((n : ℝ) + 1) := by
    have hlt : sInf (f '' s) < sInf (f '' s) + 1 / ((n : ℝ) + 1) :=
      lt_add_of_pos_right _ (by positivity)
    obtain ⟨_, ⟨u, hu, rfl⟩, hu_lt⟩ := exists_lt_of_csInf_lt (hne.image f) hlt
    exact ⟨u, hu, hu_lt⟩
  choose u hu hfu using hex
  refine ⟨u, hu, hfu, ?_⟩
  have hupper : Tendsto (fun n : ℕ ↦ sInf (f '' s) + 1 / ((n : ℝ) + 1)) atTop
      (𝓝 (sInf (f '' s))) := by
    simpa only [add_zero] using
      tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n ↦ csInf_le hbdd (mem_image_of_mem f (hu n))) fun n ↦ (hfu n).le

end TauCeti
