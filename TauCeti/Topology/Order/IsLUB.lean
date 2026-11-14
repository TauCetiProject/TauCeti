/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.IsLUB
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Minimizing sequences for functions bounded below

For a function `f : X → α` whose image on a nonempty set `s` is bounded below, this file lifts
`exists_seq_tendsto_sInf` from the value set `f '' s` to an admissible sequence `u : ℕ → X` in `s`
with nonincreasing values converging to `sInf (f '' s)`. For real-valued functions it also
constructs an admissible sequence with `f (u n) < sInf (f '' s) + 1 / (n + 1)`.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- On a nonempty set where `f` is bounded below, there is a sequence in the set along which `f` is
antitone and converges to `sInf (f '' s)`. -/
theorem exists_seq_antitone_tendsto_sInf_image {X α : Type*} [ConditionallyCompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [FirstCountableTopology α] {f : X → α} {s : Set X}
    (hs : s.Nonempty) (hbdd : BddBelow (f '' s)) :
    ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧ Antitone (f ∘ u) ∧
      Tendsto (fun n ↦ f (u n)) atTop (𝓝 (sInf (f '' s))) := by
  obtain ⟨y, hy_anti, hy_lim, hy_mem⟩ := exists_seq_tendsto_sInf (hs.image f) hbdd
  choose u hus hfu using hy_mem
  refine ⟨u, hus, fun m n hmn ↦ ?_, ?_⟩
  · simpa only [Function.comp_apply, hfu] using hy_anti hmn
  · simpa only [hfu] using hy_lim

/-- On a nonempty set where a real-valued function `f` is bounded below, there is a sequence in
the set satisfying `f (u n) < sInf (f '' s) + 1 / (n + 1)` and converging in value to
`sInf (f '' s)`. -/
theorem exists_seq_lt_sInf_image_add_one_div {X : Type*} {f : X → ℝ} {s : Set X}
    (hs : s.Nonempty) (hbdd : BddBelow (f '' s)) :
    ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧
      (∀ n : ℕ, f (u n) < sInf (f '' s) + 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n ↦ f (u n)) atTop (𝓝 (sInf (f '' s))) := by
  have hlt (n : ℕ) : ∃ x ∈ s, f x < sInf (f '' s) + 1 / ((n : ℝ) + 1) := by
    obtain ⟨_, ⟨x, hx, rfl⟩, hfx⟩ := exists_lt_of_csInf_lt (hs.image f)
      (lt_add_of_pos_right _ (one_div_pos.2 (Nat.cast_add_one_pos n)))
    exact ⟨x, hx, hfx⟩
  choose u hus hfu using hlt
  refine ⟨u, hus, hfu, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun n ↦ csInf_le hbdd (mem_image_of_mem f (hus n))) (fun n ↦ (hfu n).le)
  simpa only [add_zero] using
    tendsto_one_div_add_atTop_nhds_zero_nat.const_add (sInf (f '' s))

end TauCeti
