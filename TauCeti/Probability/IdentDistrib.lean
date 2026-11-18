/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.IdentDistrib
public import TauCeti.MeasureTheory.Function.LpSeminorm.Truncation

/-!
# Identically distributed variables and norm cut-offs

Two identically distributed variables, possibly defined on different spaces, have equal
integrals after each is kept only where its norm is at most a common real level `R`
(`ProbabilityTheory.IdentDistrib.integral_indicator_setOf_norm_le_eq`). In particular, truncated
variables recentred by their integrals use the same centring constant whenever the original
variables have the same law.
-/

public section

open MeasureTheory

namespace ProbabilityTheory.IdentDistrib

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure α} {ν : Measure β} {f : α → E} {g : β → E}

/-- Identically distributed variables have equal integrals after cutting off the values of
norm greater than `R`. -/
theorem integral_indicator_setOf_norm_le_eq (h : IdentDistrib f g μ ν) (R : ℝ) :
    ∫ x, {x | ‖f x‖ ≤ R}.indicator f x ∂μ = ∫ x, {x | ‖g x‖ ≤ R}.indicator g x ∂ν := by
  simpa only [Function.comp_def, Set.indicator_apply, Set.mem_ofPred_eq, id_eq] using
    (h.comp (measurable_id.indicator_setOf_norm_le R)).integral_eq

end ProbabilityTheory.IdentDistrib
