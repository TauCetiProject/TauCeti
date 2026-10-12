/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Recurrence.RowExchangeable
public import TauCeti.Probability.Exchangeability.MarkovExchangeable.Conditioning

/-!
# The Diaconis--Freedman representation with a random initial state

The Diaconis--Freedman representation for a recurrent Markov exchangeable process is first
available when its initial state is fixed
(`TauCeti.Probability.MarkovExchangeable.mixedMarkovChain_of_ae_initial_eq`). Conditioning on an
initial state of positive probability preserves recurrence and Markov exchangeability and gives
that fixed-start hypothesis, so the process is a mixture of Markov chains under each such
conditional law. The state space is countable, so these conditional mixtures glue along the
partition by the initial state (`TauCeti.Probability.mixedMarkovChain_of_forall_cond`) into a
single mixture of Markov chains under the original law.

Together with the easy direction `TauCeti.Probability.MixedMarkovChain.markovExchangeable`, this is
the theorem of Diaconis and Freedman: a recurrent process is Markov exchangeable if and only if it
is a mixture of Markov chains.

## Main results

* `TauCeti.Probability.MarkovExchangeable.mixedMarkovChain_cond_initial`: the conditional
  representation at a positive-probability initial state.
* `TauCeti.Probability.MarkovExchangeable.mixedMarkovChain`: **the Diaconis--Freedman
  representation theorem**, a recurrent Markov exchangeable process is a mixture of Markov chains.
* `TauCeti.Probability.markovExchangeable_iff_mixedMarkovChain`: for a recurrent process, Markov
  exchangeability and being a mixture of Markov chains are equivalent.

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
Markov chains under the conditional law. -/
theorem MarkovExchangeable.mixedMarkovChain_cond_initial [IsFiniteMeasure μ]
    (h : MarkovExchangeable μ X) (hrec : Recurrent μ X) (ha : μ {ω | X 0 ω = a} ≠ 0) :
    MixedMarkovChain (μ[|{ω | X 0 ω = a}]) X := by
  have := h.measurableSingletonClass
  have hs : NullMeasurableSet {ω | X 0 ω = a} μ :=
    (h.aemeasurable 0).nullMeasurableSet_preimage (measurableSet_singleton a)
  let _ : IsProbabilityMeasure (μ[|{ω | X 0 ω = a}]) :=
    cond_isProbabilityMeasure ha
  have hrec' : Recurrent (μ[|{ω | X 0 ω = a}]) X := by
    rw [recurrent_def] at hrec ⊢
    exact hrec.filter_mono cond_absolutelyContinuous.ae_le
  exact h.cond_initial.mixedMarkovChain_of_ae_initial_eq hrec' (ae_cond_mem₀ hs)

/-- **The Diaconis--Freedman representation theorem.** A recurrent Markov exchangeable process is a
mixture of Markov chains. The initial state may be random: the representations conditional on the
individual initial states are glued into a single pair of mixing witnesses. The measure is finite
and nonzero, as in the gluing theorem `TauCeti.Probability.mixedMarkovChain_of_forall_cond`. -/
theorem MarkovExchangeable.mixedMarkovChain [IsFiniteMeasure μ] [NeZero μ]
    (h : MarkovExchangeable μ X) (hrec : Recurrent μ X) : MixedMarkovChain μ X := by
  have := h.countable
  have := h.measurableSingletonClass
  have hX0 := h.aemeasurable 0
  -- glue along the fibres of a measurable version of the initial state
  refine mixedMarkovChain_of_forall_cond hX0.measurable_mk fun a ha => ?_
  -- each fibre is a.e. the event that the process starts at `a`
  have hfib : hX0.mk (X 0) ⁻¹' {a} =ᵐ[μ] {ω | X 0 ω = a} := by
    filter_upwards [hX0.ae_eq_mk] with ω hω
    simp [hω]
  have hcond : μ[|hX0.mk (X 0) ⁻¹' {a}] = μ[|{ω | X 0 ω = a}] := by
    unfold ProbabilityTheory.cond
    rw [measure_congr hfib, Measure.restrict_congr_set hfib]
  rw [hcond]
  exact h.mixedMarkovChain_cond_initial hrec (by rwa [← measure_congr hfib])

/-- **The Diaconis--Freedman theorem.** A recurrent process is Markov exchangeable if and only if it
is a mixture of Markov chains. -/
theorem markovExchangeable_iff_mixedMarkovChain [IsFiniteMeasure μ] [NeZero μ]
    (hrec : Recurrent μ X) :
    MarkovExchangeable μ X ↔ MixedMarkovChain μ X :=
  ⟨fun h => h.mixedMarkovChain hrec, MixedMarkovChain.markovExchangeable⟩

end TauCeti.Probability

end

end
