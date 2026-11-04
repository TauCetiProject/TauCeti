/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.BetaBinomial.Basic
public import TauCeti.Probability.Distributions.Binomial.Complement
import TauCeti.Probability.Distributions.Beta.Reflection

/-!
# Complementing beta-binomial counts

Replacing a beta-binomial success count `X` by its failure count `n - X` exchanges the
two Beta shape parameters. The native pushforward identity follows by transporting
the binomial components and reflecting the Beta mixing law. Real-cast reflection and
random-variable corollaries make the identity usable without unfolding the mixture.

The measure identities hold at every pair of real shape parameters, including the
invalid zero laws and the zero-trial boundary.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- Complementing a beta-binomial count exchanges its Beta shape parameters, including
the totalized zero laws at invalid shapes. -/
@[simp]
theorem map_sub_betaBinomialMeasure (n : ℕ) (a b : ℝ) :
    (betaBinomialMeasure n a b).map (fun k ↦ n - k) = betaBinomialMeasure n b a := by
  by_cases h : 0 < a ∧ 0 < b
  · rw [betaBinomialMeasure_eq_bind h.1 h.2, betaBinomialMeasure_eq_bind h.2 h.1,
      Measure.map_bind (by fun_prop) Measurable.of_discrete.aemeasurable]
    simp_rw [map_sub_binomial, unitInterval.symm_projIcc]
    rw [← betaMeasure_map_one_sub a b, Measure.bind_map (by fun_prop) (by fun_prop)]
  · rw [betaBinomialMeasure_eq_zero_of_invalid h, Measure.map_zero,
      betaBinomialMeasure_eq_zero_of_invalid (by tauto)]

/-- Real reflection about half the trial count exchanges the beta-binomial shapes. -/
@[simp]
theorem map_sub_map_cast_betaBinomialMeasure (n : ℕ) (a b : ℝ) :
    ((betaBinomialMeasure n a b).map (Nat.cast : ℕ → ℝ)).map
        (fun x ↦ (n : ℝ) - x) =
      (betaBinomialMeasure n b a).map (Nat.cast : ℕ → ℝ) := by
  rw [← map_sub_betaBinomialMeasure n a b,
    Measure.map_map (by fun_prop) Measurable.of_discrete,
    Measure.map_map Measurable.of_discrete (by fun_prop)]
  apply Measure.map_congr
  by_cases h : 0 < a ∧ 0 < b
  · apply ae_iff_of_countable.mpr
    intro k hk
    exact (Nat.cast_sub ((betaBinomialMeasure_singleton_ne_zero_iff h.1 h.2 n k).mp hk)).symm
  · rw [betaBinomialMeasure_eq_zero_of_invalid h, ae_zero]
    exact Filter.eventually_bot

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

/-- The failure count for a beta-binomial variable exchanges its Beta shapes. -/
theorem sub_betaBinomialMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℕ} {n : ℕ} {a b : ℝ} (hX : HasLaw X (betaBinomialMeasure n a b) P) :
    HasLaw (fun ω ↦ n - X ω) (betaBinomialMeasure n b a) P := by
  exact (⟨Measurable.of_discrete.aemeasurable, map_sub_betaBinomialMeasure n a b⟩ :
    HasLaw (fun k ↦ n - k) (betaBinomialMeasure n b a) (betaBinomialMeasure n a b)).comp hX

/-- A reflected real-cast beta-binomial variable has the exchanged shape parameters. -/
theorem sub_map_cast_betaBinomialMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {n : ℕ} {a b : ℝ}
    (hX : HasLaw X ((betaBinomialMeasure n a b).map (Nat.cast : ℕ → ℝ)) P) :
    HasLaw (fun ω ↦ (n : ℝ) - X ω)
      ((betaBinomialMeasure n b a).map (Nat.cast : ℕ → ℝ)) P := by
  exact (⟨by fun_prop, map_sub_map_cast_betaBinomialMeasure n a b⟩ :
    HasLaw (fun x : ℝ ↦ (n : ℝ) - x)
      ((betaBinomialMeasure n b a).map (Nat.cast : ℕ → ℝ))
      ((betaBinomialMeasure n a b).map (Nat.cast : ℕ → ℝ))).comp hX

end ProbabilityTheory.HasLaw
