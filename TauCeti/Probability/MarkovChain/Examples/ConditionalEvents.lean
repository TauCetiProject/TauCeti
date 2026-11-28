/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

import Mathlib.Probability.Distributions.Bernoulli
import TauCeti.Probability.MarkovChain.Filtered.Event
import TauCeti.Probability.Process.Filtration.Comp

/-!
# Boundary cases for conditional event tests of the Markov property

Revealing the next fair bit changes its conditional probability, even though the bit process
is still adapted. For counting measure on the natural numbers, each singleton test is
integrable while the constant test function `1` fails to be integrable.
-/

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- The fair-bit chain is Markov for the history filtration. Giving the filtration one step of
lookahead preserves adaptation and violates the Markov property. -/
example :
    let q : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by constructor <;> norm_num⟩
    let ν := bernoulliMeasure true false q
    let κ := Kernel.const Bool ν
    let μ := markovChainLaw ν κ
    let X (n : ℕ) (ω : ℕ → Bool) := ω n
    let ℱ := Filtration.piLE (X := fun _ : ℕ => Bool)
    let 𝒢 := ℱ.comp (τ := fun n : ℕ => n + 1) (fun _ _ h => Nat.add_le_add_right h 1)
    IsMarkovChain ℱ X κ μ ∧ Adapted 𝒢 X ∧ ¬ IsMarkovChain 𝒢 X κ μ := by
  intro q ν κ μ X ℱ 𝒢
  have hℱ : Adapted ℱ X := Filtration.adapted_piLE
  have h𝒢 : Adapted 𝒢 X := fun n => (Filtration.measurable_comp_iff ℱ _ n).2
    ((hℱ n).mono (ℱ.mono (Nat.le_succ n)) le_rfl)
  refine ⟨isMarkovChain_markovChainLaw ν κ, h𝒢, fun h => ?_⟩
  have hprob := (isMarkovChain_iff_condExp_indicator_singleton h𝒢).mp h 0 true
  have hE : MeasurableSet[𝒢 0] (X 1 ⁻¹' {true}) :=
    (Filtration.measurableSet_comp_iff ℱ _ 0).2 (hℱ 1 (measurableSet_singleton true))
  have hsame := condExp_of_stronglyMeasurable (μ := μ) (𝒢.le 0)
    ((stronglyMeasurable_const (b := (1 : ℝ))).indicator hE)
    ((integrable_const _).indicator (𝒢.le 0 _ hE))
  have hhalf (ω : ℕ → Bool) : (κ (X 0 ω)).real {true} = (1 / 2 : ℝ) := by
    simp [κ, ν, q]
  rw [hsame] at hprob
  simp only [hhalf] at hprob
  obtain ⟨ω, hω⟩ := hprob.exists
  -- Once the bit is known, the event indicator has value zero or one.
  by_cases hmem : ω ∈ X 1 ⁻¹' {true}
  · rw [indicator_of_mem hmem] at hω
    norm_num at hω
  · rw [indicator_of_notMem hmem] at hω
    norm_num at hω

/-- Finiteness matters for the singleton criterion. Under counting measure the process is
constant in time and all the singleton identities hold for the identity kernel. -/
example :
    let ℱ := Filtration.const ℕ (inferInstance : MeasurableSpace ℕ) le_rfl
    let X : ℕ → ℕ → ℕ := fun _ => id
    let κ : Kernel ℕ ℕ := Kernel.id
    let μ : Measure ℕ := Measure.count
    Adapted ℱ X ∧
      (∀ n (y : ℕ), μ[(X (n + 1) ⁻¹' {y}).indicator (fun _ => (1 : ℝ)) | ℱ n] =ᵐ[μ]
        fun ω => (κ (X n ω)).real {y}) ∧ ¬ IsMarkovChain ℱ X κ μ := by
  intro ℱ X κ μ
  have hX : Adapted ℱ X := fun n => by
    dsimp only [ℱ, X]
    rw [Filtration.const_apply]
    exact measurable_id
  refine ⟨hX, fun n y => ?_, fun h => ?_⟩
  · have hE : MeasurableSet (X (n + 1) ⁻¹' {y}) :=
      hX.measurable (i := n + 1) (measurableSet_singleton y)
    have hfin : μ (X (n + 1) ⁻¹' {y}) ≠ ⊤ := by simp [X, μ]
    have : SigmaFinite (μ.trim le_rfl) := by
      rw [trim_eq_self]
      infer_instance
    have hsame := condExp_of_stronglyMeasurable (μ := μ) le_rfl
      ((stronglyMeasurable_const (b := (1 : ℝ))).indicator hE)
      ((integrable_indicator_iff hE).mpr (integrableOn_const hfin))
    simp only [ℱ, Filtration.const_apply, hsame]
    exact Filter.Eventually.of_forall fun ω => by
      simp [X, κ, Kernel.id_apply, Measure.dirac_real_apply, Set.indicator]
  · have := h.isFiniteMeasure
    exact (measure_ne_top μ univ) (Measure.count_apply_infinite infinite_univ)

end TauCeti.Probability
