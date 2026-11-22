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

The Diaconis--Freedman theorem concerns a Markov exchangeable process that almost surely returns to
its initial state infinitely often. Its representation as a mixture of Markov chains is first
available when the initial state is fixed
(`TauCeti.Probability.MarkovExchangeable.mixedMarkovChain_of_ae_initial_eq`). Conditioning on an
initial state of positive probability preserves Markov exchangeability, turns the returns to the
initial state into returns to that fixed state, and gives the fixed start, so the process is a
mixture of Markov chains under each such conditional law. The state space is countable, so these
conditional mixtures glue along the partition by the initial state
(`TauCeti.Probability.mixedMarkovChain_of_forall_cond`) into a single mixture of Markov chains
under the original law.

Together with the easy direction `TauCeti.Probability.MixedMarkovChain.markovExchangeable`, this is
the theorem of Diaconis and Freedman: a process that returns to its initial state infinitely often
is Markov exchangeable if and only if it is a mixture of Markov chains.

The return hypothesis is the case `k = 0` of `TauCeti.Probability.Recurrent`, which asks every
visited state to be visited infinitely often; for a Markov exchangeable process under a finite
measure, started at a fixed state, the two agree
(`TauCeti.Probability.MarkovExchangeable.recurrent_of_ae_initial_eq`).

## Main results

* `TauCeti.Probability.MarkovExchangeable.mixedMarkovChain_cond_initial`: the conditional
  representation at a positive-probability initial state.
* `TauCeti.Probability.MarkovExchangeable.mixedMarkovChain`: **the Diaconis--Freedman
  representation theorem**, a Markov exchangeable process that returns to its initial state
  infinitely often is a mixture of Markov chains.
* `TauCeti.Probability.markovExchangeable_iff_mixedMarkovChain`: for a process that returns to its
  initial state infinitely often, Markov exchangeability and being a mixture of Markov chains are
  equivalent.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115--130.
* N. Halberstam and T. Hutchcroft, "Proof of the Diaconis--Freedman conjecture on
  partially-exchangeable processes", arXiv:2405.20276 (2024), §1, which restates the
  Diaconis--Freedman theorem with recurrence meaning return to the starting state infinitely often.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  {μ : Measure Ω} {X : ℕ → Ω → α} {a : α}

/-- **The conditional Diaconis--Freedman representation at an initial state.** If a Markov
exchangeable process almost surely returns to its initial state infinitely often, then each
positive-probability initial state yields a mixture of Markov chains under the conditional law. -/
theorem MarkovExchangeable.mixedMarkovChain_cond_initial [IsFiniteMeasure μ]
    (h : MarkovExchangeable μ X) (hret : ∀ᵐ ω ∂μ, ∃ᶠ n in atTop, X n ω = X 0 ω)
    (ha : μ {ω | X 0 ω = a} ≠ 0) :
    MixedMarkovChain (μ[|{ω | X 0 ω = a}]) X := by
  have := h.measurableSingletonClass
  have hs : NullMeasurableSet {ω | X 0 ω = a} μ :=
    (h.aemeasurable 0).nullMeasurableSet_preimage (measurableSet_singleton a)
  let _ : IsProbabilityMeasure (μ[|{ω | X 0 ω = a}]) :=
    cond_isProbabilityMeasure ha
  have h0 : ∀ᵐ ω ∂μ[|{ω | X 0 ω = a}], X 0 ω = a := ae_cond_mem₀ hs
  -- Under the conditional law the process starts at `a`, so its returns are returns to `a`.
  have hret' : ∀ᵐ ω ∂μ[|{ω | X 0 ω = a}], {n | X n ω = a}.Infinite := by
    filter_upwards [cond_absolutelyContinuous.ae_le hret, h0] with ω hω hω0
    rw [← hω0]
    exact Nat.frequently_atTop_iff_infinite.1 hω
  exact h.cond_initial.mixedMarkovChain_of_ae_initial_eq hret' h0

/-- **The Diaconis--Freedman representation theorem.** A Markov exchangeable process that almost
surely returns to its initial state infinitely often is a mixture of Markov chains. The initial
state may be random: the representations conditional on the individual initial states are glued
into a single pair of mixing witnesses. The measure is assumed finite.

The return hypothesis is the case `k = 0` of `TauCeti.Probability.Recurrent`, so every recurrent
Markov exchangeable process is covered. -/
theorem MarkovExchangeable.mixedMarkovChain [IsFiniteMeasure μ]
    (h : MarkovExchangeable μ X) (hret : ∀ᵐ ω ∂μ, ∃ᶠ n in atTop, X n ω = X 0 ω) :
    MixedMarkovChain μ X := by
  have := h.countable
  have := h.measurableSingletonClass
  rcases eq_zero_or_neZero μ with rfl | _
  · -- Under the zero measure every finite-path mass and every mixing integral vanish, so any
    -- measurable witnesses represent the process.
    have hzero (ν : Ω → ProbabilityMeasure α) (κ : Ω → α → ProbabilityMeasure α)
        (hν : Measurable ν) (hκ : ∀ a, Measurable fun ω => κ ω a) :
        MixedMarkovChain (0 : Measure Ω) X :=
      .of_witnesses (MixedMarkovChainWith.intro h.aemeasurable hν hκ fun n w => by
        simp [prefixLaw_def, blockLaw_def])
    rcases isEmpty_or_nonempty Ω with _ | ⟨⟨ω₀⟩⟩
    · exact hzero isEmptyElim (fun ω => isEmptyElim ω) Subsingleton.measurable
        fun _ => Subsingleton.measurable
    · exact hzero (fun _ => ⟨Measure.dirac (X 0 ω₀), inferInstance⟩)
        (fun _ a => ⟨Measure.dirac a, inferInstance⟩) measurable_const fun _ => measurable_const
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
  exact h.mixedMarkovChain_cond_initial hret (by rwa [← measure_congr hfib])

/-- **The Diaconis--Freedman theorem.** A process that almost surely returns to its initial state
infinitely often is Markov exchangeable if and only if it is a mixture of Markov chains. -/
theorem markovExchangeable_iff_mixedMarkovChain [IsFiniteMeasure μ]
    (hret : ∀ᵐ ω ∂μ, ∃ᶠ n in atTop, X n ω = X 0 ω) :
    MarkovExchangeable μ X ↔ MixedMarkovChain μ X :=
  ⟨fun h => h.mixedMarkovChain hret, MixedMarkovChain.markovExchangeable⟩

end TauCeti.Probability

end

end
