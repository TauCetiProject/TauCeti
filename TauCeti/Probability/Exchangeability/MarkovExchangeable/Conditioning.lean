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

Conditioning on a null-measurable initial-state event scales the mass of every finite path
starting there and gives zero mass to paths starting elsewhere. Hence it preserves Markov
exchangeability. The conditional path-mass formula gives the same mass to paths with the same
initial state and transition counts, establishing Markov exchangeability of the conditional law.
Null-measurability is all that is asked of the event, so conditioning on a single initial state
needs no hypothesis beyond the a.e. measurability that Markov exchangeability already bundles.

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
  {μ : Measure Ω} {X : ℕ → Ω → α} {a : α} {S : Set α}

/-- The mass of a finite path after conditioning on an initial-state event. Paths whose initial
state lies outside the conditioning set have zero mass, including when the conditioning event
itself has zero mass. -/
theorem prefixLaw_singleton_cond_initial_mem [MeasurableSingletonClass α]
    (hX : ∀ i, AEMeasurable (X i) μ) (hs : NullMeasurableSet {ω | X 0 ω ∈ S} μ)
    (n : ℕ) (w : Fin (n + 1) → α) :
    prefixLaw μ[|{ω | X 0 ω ∈ S}] X (n + 1) {w} =
      (μ {ω | X 0 ω ∈ S})⁻¹ *
        (if w 0 ∈ S then prefixLaw μ X (n + 1) {w} else 0) := by
  let s : Set Ω := {ω | X 0 ω ∈ S}
  have hac : μ[|s] ≪ μ := cond_absolutelyContinuous
  have hXcond : ∀ i, AEMeasurable (X i) μ[|s] := fun i => by
    obtain ⟨f, hf, heq⟩ := hX i
    exact ⟨f, hf, heq.filter_mono hac.ae_le⟩
  -- `ProbabilityTheory.cond_apply` asks for a measurable conditioning event; this is its
  -- null-measurable form
  rw [prefixLaw_singleton_eq_measure hXcond, ProbabilityTheory.cond, Measure.smul_apply,
    Measure.restrict_apply₀' hs, smul_eq_mul, Set.inter_comm,
    prefixLaw_singleton_eq_measure hX]
  split_ifs with hw
  · congr 1
    congr 1
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · exact And.right
    · intro hp
      exact ⟨(hp 0).symm ▸ hw, hp⟩
  · have hempty : s ∩ {ω | ∀ i : Fin (n + 1), X i.val ω = w i} = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro ω hω
      exact hw ((hω.2 0) ▸ hω.1)
    rw [hempty, measure_empty]

/-- Conditioning on a null-measurable initial-state event preserves Markov exchangeability. -/
theorem MarkovExchangeable.cond_initial_mem (h : MarkovExchangeable μ X)
    (hs : NullMeasurableSet {ω | X 0 ω ∈ S} μ) :
    MarkovExchangeable (μ[|{ω | X 0 ω ∈ S}]) X := by
  classical
  let _ : Countable α := h.countable
  let _ : MeasurableSingletonClass α := h.measurableSingletonClass
  have hac : μ[|{ω | X 0 ω ∈ S}] ≪ μ := cond_absolutelyContinuous
  have hX : ∀ i, AEMeasurable (X i) μ[|{ω | X 0 ω ∈ S}] := fun i => by
    obtain ⟨f, hf, heq⟩ := h.aemeasurable i
    exact ⟨f, hf, heq.filter_mono hac.ae_le⟩
  refine MarkovExchangeable.intro hX fun n u v huv hcount => ?_
  rw [prefixLaw_singleton_cond_initial_mem h.aemeasurable hs n u,
    prefixLaw_singleton_cond_initial_mem h.aemeasurable hs n v,
    huv, h.prefixLaw_singleton_eq n u v huv hcount]

/-- Conditioning on an initial state preserves Markov exchangeability. -/
theorem MarkovExchangeable.cond_initial (h : MarkovExchangeable μ X) :
    MarkovExchangeable (μ[|{ω | X 0 ω = a}]) X := by
  have := h.measurableSingletonClass
  simpa only [Set.mem_singleton_iff] using
    h.cond_initial_mem ((h.aemeasurable 0).nullMeasurableSet_preimage (measurableSet_singleton a))

end TauCeti.Probability

end

end
