/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.IdentDistrib
public import TauCeti.MeasureTheory.Function.LpSeminorm.Truncation

/-!
# Identically distributed random variables

If every member of a countable family of random variables is identically distributed with a
random variable that is almost surely equal to a constant, then almost surely every member of the
family equals that constant, on one event for all indices at once.

Two identically distributed variables, possibly defined on different spaces, have equal
integrals after each is kept only where its norm is at most a common real level `R`. In
particular, truncated variables recentred by their integrals use the same centring constant
whenever the original variables have the same law.

## Main results

* `TauCeti.Probability.ae_forall_eq_of_identDistrib` — a countable family of random variables,
  each identically distributed with an almost surely constant random variable, is almost surely
  equal to that constant at every index simultaneously.
* `ProbabilityTheory.IdentDistrib.integral_indicator_setOf_norm_le_eq` — identically distributed
  variables have equal integrals after cutting off the values of norm greater than `R`.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- **Random variables identically distributed with an almost surely constant one are almost surely
constant simultaneously.** If each `T i` of a countable family has the same law as `X`, and `X`
equals `c` almost surely, then almost surely all of the `T i` equal `c`. The family and `X` may live
on different measure spaces. -/
theorem ae_forall_eq_of_identDistrib {ι : Sort*} [Countable ι] {Ω Ω' Z : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {P : Measure Ω} {Q : Measure Ω'} {T : ι → Ω → Z} {X : Ω' → Z}
    (hid : ∀ i, IdentDistrib (T i) X P Q) {c : Z} (h : X =ᵐ[Q] fun _ ↦ c) :
    ∀ᵐ ω ∂P, ∀ i, T i ω = c :=
  ae_all_iff.2 fun i ↦ (hid i).symm.ae_mem_snd (measurableSet_singleton c) h

end TauCeti.Probability

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
