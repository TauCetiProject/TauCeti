/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Recurrence.RowExchangeable
public import TauCeti.Probability.Exchangeability.MarkovExchangeable.Conditioning

/-!
# Conditional Diaconis--Freedman representation at an initial state

The Diaconis--Freedman representation for a recurrent Markov exchangeable process is available
when its initial state is fixed. Conditioning on a measurable initial-state event preserves
recurrence and gives that fixed-start hypothesis. This provides the conditional pieces needed to
represent a process with a random initial state.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115--130.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  {μ : Measure Ω} {X : ℕ → Ω → α} {a : α}

/-- **The conditional Diaconis--Freedman representation at an initial state.** Each
positive-probability initial state of a recurrent Markov exchangeable process yields a mixture of
Markov chains under the conditional law. The full random-start representation requires combining
these state-indexed mixtures. -/
theorem MarkovExchangeable.mixedMarkovChain_cond_initial [IsProbabilityMeasure μ]
    (h : MarkovExchangeable μ X) (hrec : Recurrent μ X)
    (hs : MeasurableSet {ω | X 0 ω = a}) (ha : μ {ω | X 0 ω = a} ≠ 0) :
    MixedMarkovChain (μ[|{ω | X 0 ω = a}]) X := by
  let _ : IsProbabilityMeasure (μ[|{ω | X 0 ω = a}]) :=
    cond_isProbabilityMeasure ha
  have hrec' : Recurrent (μ[|{ω | X 0 ω = a}]) X := by
    rw [recurrent_def] at hrec ⊢
    exact hrec.filter_mono cond_absolutelyContinuous.ae_le
  exact (h.cond_initial hs).mixedMarkovChain hrec' (ae_cond_mem hs)

end TauCeti.Probability

end

end
