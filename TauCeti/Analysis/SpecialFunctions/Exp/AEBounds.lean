/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Almost-everywhere bounds under exponential substitution

`TauCeti.exists_ae_le_exp_of_eventually_le_rpow` transports an eventual power bound to an
almost-everywhere exponential bound on a right ray by substituting `x = exp u`.
-/

public section

open Filter MeasureTheory Set

namespace TauCeti

/-- Substituting `x = exp u` turns an eventual bound `f x ≤ C * x ^ θ` into an almost-everywhere
bound `f (exp u) ≤ C * exp (θ * u)` on a ray. -/
theorem exists_ae_le_exp_of_eventually_le_rpow {f : ℝ → ℝ} {θ C : ℝ}
    (h : ∀ᶠ x in atTop, f x ≤ C * x ^ θ) :
    ∃ u₀, ∀ᵐ u ∂volume.restrict (Ioi u₀), f (Real.exp u) ≤ C * Real.exp (θ * u) := by
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.mp (Real.tendsto_exp_atTop.eventually h)
  refine ⟨u₀, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [mul_comm θ u, Real.exp_mul]
  exact hu₀ u (le_of_lt hu)

end TauCeti
