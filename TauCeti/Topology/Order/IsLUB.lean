/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.IsLUB
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Minimizing sequences for infima of images

A function bounded below on a nonempty set admits a sequence in the set whose values decrease
monotonely to `sInf (f '' s)` (`TauCeti.exists_seq_antitone_tendsto_sInf_image`), obtained by
pulling back `exists_seq_tendsto_sInf` from the image. For real-valued functions, one can choose a
minimizing sequence satisfying the quantitative bound `f (u n) < sInf (f '' s) + 1 / (n + 1)`
(`TauCeti.exists_seq_lt_sInf_image_add_one_div`).
-/

public section

open Filter Set Topology

namespace TauCeti

/-- A function bounded below on a nonempty set admits a minimizing sequence whose values decrease
monotonely to the infimum. -/
theorem exists_seq_antitone_tendsto_sInf_image {α β : Type*}
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    [FirstCountableTopology β] {f : α → β} {s : Set α}
    (hs : s.Nonempty) (hbdd : BddBelow (f '' s)) :
    ∃ u : ℕ → α, (∀ n, u n ∈ s) ∧ Antitone (f ∘ u) ∧
      Tendsto (f ∘ u) atTop (𝓝 (sInf (f '' s))) := by
  obtain ⟨r, hr_anti, hr_lim, hr_mem⟩ := exists_seq_tendsto_sInf (hs.image f) hbdd
  choose u hus hfu using hr_mem
  exact ⟨u, hus, by simpa only [Function.comp_def, hfu] using hr_anti,
    by simpa only [Function.comp_def, hfu] using hr_lim⟩

/-- A real-valued function bounded below on a nonempty set admits a minimizing sequence satisfying
`f (u n) < sInf (f '' s) + 1 / (n + 1)` for every `n`. -/
theorem exists_seq_lt_sInf_image_add_one_div {α : Type*} {f : α → ℝ} {s : Set α}
    (hs : s.Nonempty) (hbdd : BddBelow (f '' s)) :
    ∃ u : ℕ → α, (∀ n, u n ∈ s) ∧
      (∀ n, f (u n) < sInf (f '' s) + 1 / ((n : ℝ) + 1)) ∧
      Tendsto (f ∘ u) atTop (𝓝 (sInf (f '' s))) := by
  have hstep (n : ℕ) : ∃ x ∈ s, f x < sInf (f '' s) + 1 / ((n : ℝ) + 1) := by
    obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (hs.image f)
      (lt_add_of_pos_right (sInf (f '' s)) (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)))
    exact ⟨x, hx, hlt⟩
  choose u hu hlt using hstep
  refine ⟨u, hu, hlt, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun n ↦ csInf_le hbdd (mem_image_of_mem f (hu n))) (fun n ↦ (hlt n).le)⟩
  simpa only [add_zero] using
    tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end TauCeti
