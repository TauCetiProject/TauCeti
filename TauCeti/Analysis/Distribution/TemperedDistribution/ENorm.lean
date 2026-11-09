/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# The `Lᵖ` norm of a tempered distribution

Let `μ` be a locally finite measure of temperate growth on a finite-dimensional real normed space
`E` (by default `volume`). A tempered distribution `u` *is* an `Lᵖ(μ)` function when it is the
distribution `φ ↦ ∫ φ • f ∂μ` of some `f ∈ Lᵖ(μ)`; this `f` is unique
(`MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot`). This file defines the extended `Lᵖ(μ)`
norm `TemperedDistribution.eLpNorm u p μ` of a tempered distribution: it is `‖f‖ₑ` when `u` is the
distribution of `f ∈ Lᵖ(μ)`, and `∞` when `u` is not an `Lᵖ(μ)` function.

This is the form in which `Lᵖ` norms of distributions enter the dyadic function spaces: a
Littlewood–Paley block of an arbitrary tempered distribution need not lie in `Lᵖ`, and the Besov
norms weigh the extended `Lᵖ` norms of all of them. The extended norm is a norm on the
distributions of finite norm: it vanishes exactly at `0`, satisfies the triangle inequality and is
homogeneous.

## Main declarations

* `TemperedDistribution.eLpNorm`: the extended `Lᵖ` norm of a tempered distribution.
* `TemperedDistribution.eLpNorm_toTemperedDistribution`: on the distribution of `f ∈ Lᵖ` it is
  `‖f‖ₑ`.
* `TemperedDistribution.eLpNorm_lt_top_iff`: it is finite exactly on the `Lᵖ` functions.
* `TemperedDistribution.eLpNorm_eq_zero_iff`, `TemperedDistribution.eLpNorm_add_le`,
  `TemperedDistribution.eLpNorm_smul`: the norm axioms.
-/

public section

noncomputable section

open MeasureTheory (Lp Measure)
open scoped ENNReal SchwartzMap

namespace MeasureTheory.Lp

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {μ : Measure E}
  [μ.HasTemperateGrowth] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The tempered distribution of the zero `Lᵖ` function is `0`. -/
@[simp]
theorem toTemperedDistribution_zero : ((0 : Lp F p μ) : 𝓢'(E, F)) = 0 :=
  map_zero (toTemperedDistributionCLM F μ p)

/-- Passing from `Lᵖ` functions to tempered distributions is additive. -/
@[simp]
theorem toTemperedDistribution_add (f g : Lp F p μ) :
    ((f + g : Lp F p μ) : 𝓢'(E, F)) = (f : 𝓢'(E, F)) + (g : 𝓢'(E, F)) :=
  map_add (toTemperedDistributionCLM F μ p) f g

/-- Passing from `Lᵖ` functions to tempered distributions commutes with scalar multiplication. -/
@[simp]
theorem toTemperedDistribution_smul (c : ℂ) (f : Lp F p μ) :
    ((c • f : Lp F p μ) : 𝓢'(E, F)) = c • (f : 𝓢'(E, F)) :=
  map_smul (toTemperedDistributionCLM F μ p) c f

/-- An `Lᵖ` function is determined by its tempered distribution. -/
theorem toTemperedDistribution_injective [FiniteDimensional ℝ E] [IsLocallyFiniteMeasure μ] :
    Function.Injective (fun f : Lp F p μ ↦ (f : 𝓢'(E, F))) :=
  LinearMap.ker_eq_bot.mp ker_toTemperedDistributionCLM_eq_bot

end MeasureTheory.Lp

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The **`Lᵖ(μ)` norm of a tempered distribution**, in `ℝ≥0∞`: `‖f‖ₑ` when `u` is the tempered
distribution of `f ∈ Lᵖ(μ)`, and `∞` when `u` is not an `Lᵖ(μ)` function. The measure `μ`
defaults to `volume`; the arguments are ordered as in `MeasureTheory.eLpNorm`. -/
def eLpNorm (u : 𝓢'(E, F)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure E := by volume_tac)
    [μ.HasTemperateGrowth] : ℝ≥0∞ :=
  ⨅ (f : Lp F p μ) (_ : (f : 𝓢'(E, F)) = u), ‖f‖ₑ

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable {μ : Measure E} [μ.HasTemperateGrowth]

/-- A tempered distribution that is not an `Lᵖ` function has infinite `Lᵖ` norm. -/
theorem eLpNorm_eq_top {u : 𝓢'(E, F)} (hu : ∀ f : Lp F p μ, (f : 𝓢'(E, F)) ≠ u) :
    eLpNorm u p μ = ∞ := by
  simp [eLpNorm, hu]

variable [FiniteDimensional ℝ E] [MeasureTheory.IsLocallyFiniteMeasure μ]

/-- The `Lᵖ` norm of the tempered distribution of `f ∈ Lᵖ` is `‖f‖ₑ`. -/
@[simp]
theorem eLpNorm_toTemperedDistribution (f : Lp F p μ) :
    eLpNorm (f : 𝓢'(E, F)) p μ = ‖f‖ₑ :=
  le_antisymm (iInf_le_of_le f (iInf_le _ rfl)) <| le_iInf₂ fun g hg ↦ by
    rw [MeasureTheory.Lp.toTemperedDistribution_injective hg]

/-- A tempered distribution has finite `Lᵖ` norm exactly when it is an `Lᵖ` function. -/
theorem eLpNorm_lt_top_iff {u : 𝓢'(E, F)} :
    eLpNorm u p μ < ∞ ↔ ∃ f : Lp F p μ, (f : 𝓢'(E, F)) = u := by
  refine ⟨fun h ↦ ?_, fun ⟨f, hf⟩ ↦ hf ▸ by simp⟩
  by_contra! hu
  exact h.ne (eLpNorm_eq_top hu)

@[simp]
theorem eLpNorm_zero : eLpNorm (0 : 𝓢'(E, F)) p μ = 0 := by
  simpa using eLpNorm_toTemperedDistribution (p := p) (0 : Lp F p μ)

@[simp]
theorem eLpNorm_eq_zero_iff {u : 𝓢'(E, F)} : eLpNorm u p μ = 0 ↔ u = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ eLpNorm_zero⟩
  obtain ⟨f, rfl⟩ := eLpNorm_lt_top_iff.1 (h ▸ ENNReal.zero_lt_top)
  rw [eLpNorm_toTemperedDistribution, enorm_eq_zero] at h
  simp [h]

/-- The triangle inequality for the `Lᵖ` norm of tempered distributions. -/
theorem eLpNorm_add_le (u v : 𝓢'(E, F)) :
    eLpNorm (u + v) p μ ≤ eLpNorm u p μ + eLpNorm v p μ := by
  rcases eq_or_ne (eLpNorm u p μ) ∞ with hu | hu
  · simp [hu]
  rcases eq_or_ne (eLpNorm v p μ) ∞ with hv | hv
  · simp [hv]
  obtain ⟨f, rfl⟩ := eLpNorm_lt_top_iff.1 hu.lt_top
  obtain ⟨g, rfl⟩ := eLpNorm_lt_top_iff.1 hv.lt_top
  simpa [← MeasureTheory.Lp.toTemperedDistribution_add] using enorm_add_le f g

/-- The `Lᵖ` norm of tempered distributions is homogeneous. -/
theorem eLpNorm_smul (c : ℂ) (u : 𝓢'(E, F)) : eLpNorm (c • u) p μ = ‖c‖ₑ * eLpNorm u p μ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  by_cases hu : ∃ f : Lp F p μ, (f : 𝓢'(E, F)) = u
  · obtain ⟨f, rfl⟩ := hu
    simpa [← MeasureTheory.Lp.toTemperedDistribution_smul] using enorm_smul c f
  · push Not at hu
    rw [eLpNorm_eq_top hu, ENNReal.mul_top (by simpa using hc), eLpNorm_eq_top]
    intro f hf
    refine hu (c⁻¹ • f) ?_
    rw [MeasureTheory.Lp.toTemperedDistribution_smul, hf, smul_smul, inv_mul_cancel₀ hc, one_smul]

@[simp]
theorem eLpNorm_neg (u : 𝓢'(E, F)) : eLpNorm (-u) p μ = eLpNorm u p μ := by
  simpa using eLpNorm_smul (p := p) (-1) u

end TemperedDistribution
