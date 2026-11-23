/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Specific limits for real sequences

This module extends `Mathlib.Analysis.SpecificLimits.Basic` with asymptotic divergence for real
sequences under eventual multiplicative step growth.

## Main results

* `TauCeti.tendsto_atTop_of_eventually_geom_le`: if `1 < c`, `c * v m ≤ v (m + 1)` eventually,
  and `0 < v m` frequently, then `v n → +∞`.
-/

public section

open Filter

namespace TauCeti

/-- If `1 < c`, `c * v m ≤ v (m + 1)` eventually, and `0 < v m` frequently, then `v n → +∞` as
`n → ∞`. -/
theorem tendsto_atTop_of_eventually_geom_le {v : ℕ → ℝ} {c : ℝ} (hc : 1 < c)
    (hstep : ∀ᶠ m in atTop, c * v m ≤ v (m + 1)) (hne : ∃ᶠ m in atTop, 0 < v m) :
    Tendsto v atTop atTop := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hstep
  obtain ⟨M, hpos, _⟩ := (hne.and_eventually (eventually_ge_atTop M₀)).exists
  exact (tendsto_add_atTop_iff_nat M).1 <|
    tendsto_atTop_of_geom_le (v := fun n ↦ v (n + M)) (by simpa using hpos) hc
      fun n ↦ by simpa only [Nat.add_right_comm] using hM₀ (n + M) (by omega)

end TauCeti
