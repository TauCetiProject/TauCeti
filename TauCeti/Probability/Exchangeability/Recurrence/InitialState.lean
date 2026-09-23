/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Recurrence.RowExchangeable
import Mathlib.Probability.ConditionalProbability

/-!
# Conditioning Markov exchangeability on the initial state

The Diaconis--Freedman representation for a recurrent Markov exchangeable process is available
when its initial state is fixed. Conditioning on a measurable initial-state event preserves both
Markov exchangeability and recurrence, and gives that fixed-start hypothesis. This provides the
conditional pieces needed to represent a process with a random initial state.

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

/-- Conditioning on a measurable initial-state event preserves Markov exchangeability. -/
theorem MarkovExchangeable.cond_initial (h : MarkovExchangeable μ X)
    (hs : MeasurableSet {ω | X 0 ω = a}) :
    MarkovExchangeable (μ[|{ω | X 0 ω = a}]) X := by
  classical
  let _ : Countable α := h.countable
  let _ : MeasurableSingletonClass α := h.measurableSingletonClass
  let s : Set Ω := {ω | X 0 ω = a}
  have hac : μ[|s] ≪ μ := cond_absolutelyContinuous
  have hX : ∀ i, AEMeasurable (X i) μ[|s] := fun i => by
    obtain ⟨f, hf, heq⟩ := h.aemeasurable i
    exact ⟨f, hf, heq.filter_mono hac.ae_le⟩
  refine MarkovExchangeable.intro hX fun n u v huv hcount => ?_
  have hmass (w : Fin (n + 1) → α) :
      prefixLaw μ[|s] X (n + 1) {w} =
        (μ s)⁻¹ * (if w 0 = a then prefixLaw μ X (n + 1) {w} else 0) := by
    rw [prefixLaw_singleton_eq_measure hX,
      cond_apply hs μ,
      prefixLaw_singleton_eq_measure h.aemeasurable]
    split_ifs with hw
    · congr 1
      congr 1
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · exact And.right
      · intro hp
        exact ⟨by simpa [s, hw] using (hp 0), hp⟩
    · have hempty : s ∩ {ω | ∀ i : Fin (n + 1), X i.val ω = w i} = ∅ := by
        apply Set.eq_empty_of_forall_notMem
        intro ω hω
        exact hw (hω.1.symm.trans (hω.2 0)).symm
      rw [hempty, measure_empty]
  rw [hmass u, hmass v, huv, h.prefixLaw_singleton_eq n u v huv hcount]

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
