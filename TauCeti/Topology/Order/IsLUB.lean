/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.IsLUB

/-!
# Sequences approaching the infimum of an image

For a function `f : X → β` into a first-countable conditionally complete linear order that is
bounded below on a nonempty set `s`, `Mathlib.Topology.Order.IsLUB.exists_seq_tendsto_sInf`
constructs an antitone sequence in `f '' s` converging to `sInf (f '' s)`. Lifting its terms back
to `s` yields a sequence `u : ℕ → X` in `s` with antitone values converging to `sInf (f '' s)`
(`TauCeti.exists_seq_forall_mem_and_tendsto_sInf`).
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

end TauCeti
