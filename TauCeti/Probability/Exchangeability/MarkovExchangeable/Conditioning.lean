/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.MarkovExchangeable
public import Mathlib.Probability.ConditionalProbability

/-!
# Conditioning Markov exchangeability on the initial state

Conditioning on a measurable initial-state event scales the mass of every finite path starting
there and gives zero mass to paths starting elsewhere. Hence it preserves Markov exchangeability.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115--130.
-/

public section

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  {μ : Measure Ω} {X : ℕ → Ω → α} {a : α}

/-- The mass of a finite path after conditioning on an initial state. Paths starting at another
state have zero mass, including when the conditioning event itself has zero mass. -/
theorem prefixLaw_singleton_cond_initial [MeasurableSingletonClass α]
    (hX : ∀ i, AEMeasurable (X i) μ) (hs : MeasurableSet {ω | X 0 ω = a})
    (n : ℕ) (w : Fin (n + 1) → α) :
    prefixLaw μ[|{ω | X 0 ω = a}] X (n + 1) {w} =
      (μ {ω | X 0 ω = a})⁻¹ *
        (if w 0 = a then prefixLaw μ X (n + 1) {w} else 0) := by
  let s : Set Ω := {ω | X 0 ω = a}
  have hac : μ[|s] ≪ μ := cond_absolutelyContinuous
  have hXcond : ∀ i, AEMeasurable (X i) μ[|s] := fun i => by
    obtain ⟨f, hf, heq⟩ := hX i
    exact ⟨f, hf, heq.filter_mono hac.ae_le⟩
  rw [prefixLaw_singleton_eq_measure hXcond,
    cond_apply hs μ,
    prefixLaw_singleton_eq_measure hX]
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

/-- Conditioning on a measurable initial-state event preserves Markov exchangeability. -/
theorem MarkovExchangeable.cond_initial (h : MarkovExchangeable μ X)
    (hs : MeasurableSet {ω | X 0 ω = a}) :
    MarkovExchangeable (μ[|{ω | X 0 ω = a}]) X := by
  classical
  let _ : Countable α := h.countable
  let _ : MeasurableSingletonClass α := h.measurableSingletonClass
  have hac : μ[|{ω | X 0 ω = a}] ≪ μ := cond_absolutelyContinuous
  have hX : ∀ i, AEMeasurable (X i) μ[|{ω | X 0 ω = a}] := fun i => by
    obtain ⟨f, hf, heq⟩ := h.aemeasurable i
    exact ⟨f, hf, heq.filter_mono hac.ae_le⟩
  refine MarkovExchangeable.intro hX fun n u v huv hcount => ?_
  rw [prefixLaw_singleton_cond_initial h.aemeasurable hs n u,
    prefixLaw_singleton_cond_initial h.aemeasurable hs n v,
    huv, h.prefixLaw_singleton_eq n u v huv hcount]

end TauCeti.Probability

end

end
