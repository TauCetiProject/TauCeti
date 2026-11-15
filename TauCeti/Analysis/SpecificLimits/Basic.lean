/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Quantitative minimizing sequences for real infima

When a real-valued function `f` on `X` is bounded below on `s : Set X` (`BddBelow (f '' s)`), any
sequence in `s` whose values exceed `sInf (f '' s)` by at most `ε n → 0` converges to
`sInf (f '' s)` (`TauCeti.tendsto_csInf_of_le_csInf_add`), and when `s` is also nonempty there
exists a minimizing sequence `u` in `s` satisfying `f (u n) < sInf (f '' s) + 1 / (n + 1)`
(`TauCeti.exists_seq_lt_csInf_add_one_div`).

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, §4.2.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- If a real-valued function `f` is bounded below on `s`, any sequence in `s` whose values exceed
`sInf (f '' s)` by at most `ε n → 0` satisfies `f (u n) → sInf (f '' s)`. -/
theorem tendsto_csInf_of_le_csInf_add {X : Type*} {f : X → ℝ} {s : Set X}
    (hbdd : BddBelow (f '' s)) {u : ℕ → X} (hu : ∀ n, u n ∈ s) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hle : ∀ n, f (u n) ≤ sInf (f '' s) + ε n) :
    Tendsto (fun n ↦ f (u n)) atTop (𝓝 (sInf (f '' s))) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun n ↦ csInf_le hbdd (mem_image_of_mem f (hu n))) hle
  simpa only [add_zero] using tendsto_const_nhds.add hε

/-- Every nonempty set on which a real-valued function is bounded below admits a minimizing
sequence `u n ∈ s` with `f (u n) < sInf (f '' s) + 1 / (n + 1)` and `f (u n) → sInf (f '' s)`. -/
theorem exists_seq_lt_csInf_add_one_div {X : Type*} {f : X → ℝ} {s : Set X}
    (hne : s.Nonempty) (hbdd : BddBelow (f '' s)) :
    ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧
      (∀ n, f (u n) < sInf (f '' s) + 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n ↦ f (u n)) atTop (𝓝 (sInf (f '' s))) := by
  have hex (n : ℕ) : ∃ x ∈ s, f x < sInf (f '' s) + 1 / ((n : ℝ) + 1) := by
    obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ :=
      exists_lt_of_csInf_lt (hne.image f) (lt_add_of_pos_right _ (one_div_pos.2 n.cast_add_one_pos))
    exact ⟨x, hx, hlt⟩
  choose u hu hlt using hex
  exact ⟨u, hu, hlt, tendsto_csInf_of_le_csInf_add hbdd hu
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) fun n ↦ (hlt n).le⟩

end TauCeti
