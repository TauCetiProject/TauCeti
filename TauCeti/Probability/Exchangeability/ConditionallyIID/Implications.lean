/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic
public import TauCeti.Probability.Exchangeability.Family
-- Non-public: the mixture-side bridges `MixedIIDWith.exchangeable` and `MixedIIDWith.contractable`
-- are used only inside the proofs below.
import TauCeti.Probability.Exchangeability.MixedIID.Implications

/-!
# Basic implications from conditional i.i.d.-ness

A conditionally i.i.d. sequence is exchangeable and contractable, and a conditionally i.i.d.
family over any index type is an exchangeable family. These are the easy directions of de Finetti's
theorem and of its Ryll-Nardzewski extension to contractable sequences: conditional independence
given a directing measure forces every finite selection of
coordinates to have the same law, whatever indices are chosen and in whatever order. Each holds
both for a named directing measure and in the existential form.

## Main results

* `ConditionallyIIDWith.exchangeable`, `ConditionallyIIDWith.contractable` — at a named directing
  measure.
* `ConditionallyIID.exchangeable`, `ConditionallyIID.contractable` — their existential corollaries.
* `ConditionallyIIDWith.exchangeableFamily`, `ConditionallyIID.exchangeableFamily` — the same
  implication for families over an arbitrary index type.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- A sequence with a named directing measure is exchangeable. -/
theorem ConditionallyIIDWith.exchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : ConditionallyIIDWith μ X ν) : Exchangeable μ X :=
  (mixedIIDWith_of_conditionallyIIDWith h).exchangeable

/-- A conditionally i.i.d. sequence is exchangeable. -/
theorem ConditionallyIID.exchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : ConditionallyIID μ X) : Exchangeable μ X :=
  let ⟨_, hν⟩ := h.exists_directing
  hν.exchangeable

/-- A sequence with a named directing measure is contractable. -/
theorem ConditionallyIIDWith.contractable {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : ConditionallyIIDWith μ X ν) : Contractable μ X :=
  (mixedIIDWith_of_conditionallyIIDWith h).contractable

/-- A conditionally i.i.d. sequence is contractable. -/
theorem ConditionallyIID.contractable {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : ConditionallyIID μ X) : Contractable μ X :=
  let ⟨_, hν⟩ := h.exists_directing
  hν.contractable

/-- A conditionally i.i.d. family with a named directing measure is exchangeable. -/
theorem ConditionallyIIDWith.exchangeableFamily
    {μ : Measure Ω} {X : ι → Ω → α} {ν : Ω → ProbabilityMeasure α}
    (h : ConditionallyIIDWith μ X ν) : ExchangeableFamily μ X :=
  (mixedIIDWith_of_conditionallyIIDWith h).exchangeableFamily

/-- A conditionally i.i.d. family is exchangeable. -/
theorem ConditionallyIID.exchangeableFamily
    {μ : Measure Ω} {X : ι → Ω → α} (h : ConditionallyIID μ X) :
    ExchangeableFamily μ X :=
  let ⟨_, hν⟩ := h.exists_directing
  hν.exchangeableFamily

end Probability

end TauCeti
