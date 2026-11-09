/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# The `Lᵖ` norm of a tempered distribution

A tempered distribution `u` *is* an `Lᵖ` function when it is the distribution `φ ↦ ∫ φ • f` of some
`f ∈ Lᵖ`; this `f` is unique (`MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot`). This file
defines the extended `Lᵖ` norm `TemperedDistribution.eLpNorm u p` of a tempered distribution: it
is `‖f‖ₑ` when `u` is the distribution of `f ∈ Lᵖ`, and `∞` when `u` is not an `Lᵖ` function.

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

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- The **`Lᵖ` norm of a tempered distribution**, in `ℝ≥0∞`: `‖f‖ₑ` when `u` is the tempered
distribution of `f ∈ Lᵖ`, and `∞` when `u` is not an `Lᵖ` function. -/
def eLpNorm (u : 𝓢'(E, F)) : ℝ≥0∞ :=
  ⨅ (f : Lp F p (MeasureTheory.volume : Measure E)) (_ : (f : 𝓢'(E, F)) = u), ‖f‖ₑ

/-- An `Lᵖ` function is determined by its tempered distribution. -/
theorem _root_.MeasureTheory.Lp.toTemperedDistribution_injective :
    Function.Injective
      (fun f : Lp F p (MeasureTheory.volume : Measure E) ↦ (f : 𝓢'(E, F))) :=
  LinearMap.ker_eq_bot.mp MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot

/-- The `Lᵖ` norm of the tempered distribution of `f ∈ Lᵖ` is `‖f‖ₑ`. -/
@[simp]
theorem eLpNorm_toTemperedDistribution (f : Lp F p (MeasureTheory.volume : Measure E)) :
    eLpNorm p (f : 𝓢'(E, F)) = ‖f‖ₑ :=
  le_antisymm (iInf_le_of_le f (iInf_le _ rfl)) <| le_iInf₂ fun g hg ↦ by
    rw [MeasureTheory.Lp.toTemperedDistribution_injective hg]

/-- A tempered distribution that is not an `Lᵖ` function has infinite `Lᵖ` norm. -/
theorem eLpNorm_eq_top {u : 𝓢'(E, F)}
    (hu : ∀ f : Lp F p (MeasureTheory.volume : Measure E), (f : 𝓢'(E, F)) ≠ u) :
    eLpNorm p u = ∞ := by
  simp [eLpNorm, hu]

/-- A tempered distribution has finite `Lᵖ` norm exactly when it is an `Lᵖ` function. -/
theorem eLpNorm_lt_top_iff {u : 𝓢'(E, F)} :
    eLpNorm p u < ∞ ↔ ∃ f : Lp F p (MeasureTheory.volume : Measure E), (f : 𝓢'(E, F)) = u := by
  refine ⟨fun h ↦ ?_, fun ⟨f, hf⟩ ↦ hf ▸ by simp⟩
  by_contra! hu
  exact h.ne (eLpNorm_eq_top hu)

@[simp]
theorem eLpNorm_zero : eLpNorm p (0 : 𝓢'(E, F)) = 0 := by
  simpa [← MeasureTheory.Lp.toTemperedDistributionCLM_apply] using
    eLpNorm_toTemperedDistribution (p := p) (0 : Lp F p (MeasureTheory.volume : Measure E))

@[simp]
theorem eLpNorm_eq_zero_iff {u : 𝓢'(E, F)} : eLpNorm p u = 0 ↔ u = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ eLpNorm_zero⟩
  obtain ⟨f, rfl⟩ := eLpNorm_lt_top_iff.1 (h ▸ ENNReal.zero_lt_top)
  rw [eLpNorm_toTemperedDistribution, enorm_eq_zero] at h
  simp [h, ← MeasureTheory.Lp.toTemperedDistributionCLM_apply]

/-- The triangle inequality for the `Lᵖ` norm of tempered distributions. -/
theorem eLpNorm_add_le (u v : 𝓢'(E, F)) : eLpNorm p (u + v) ≤ eLpNorm p u + eLpNorm p v := by
  rcases eq_or_ne (eLpNorm p u) ∞ with hu | hu
  · simp [hu]
  rcases eq_or_ne (eLpNorm p v) ∞ with hv | hv
  · simp [hv]
  obtain ⟨f, rfl⟩ := eLpNorm_lt_top_iff.1 hu.lt_top
  obtain ⟨g, rfl⟩ := eLpNorm_lt_top_iff.1 hv.lt_top
  have h := map_add (MeasureTheory.Lp.toTemperedDistributionCLM F MeasureTheory.volume p) f g
  simp only [MeasureTheory.Lp.toTemperedDistributionCLM_apply] at h
  simpa [← h] using enorm_add_le f g

/-- The `Lᵖ` norm of tempered distributions is homogeneous. -/
theorem eLpNorm_smul (c : ℂ) (u : 𝓢'(E, F)) : eLpNorm p (c • u) = ‖c‖ₑ * eLpNorm p u := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  by_cases hu : ∃ f : Lp F p (MeasureTheory.volume : Measure E), (f : 𝓢'(E, F)) = u
  · obtain ⟨f, rfl⟩ := hu
    have h := map_smul (MeasureTheory.Lp.toTemperedDistributionCLM F MeasureTheory.volume p) c f
    simp only [MeasureTheory.Lp.toTemperedDistributionCLM_apply] at h
    simpa [← h] using enorm_smul c f
  · push Not at hu
    rw [eLpNorm_eq_top hu, ENNReal.mul_top (by simpa using hc), eLpNorm_eq_top]
    intro f hf
    refine hu (c⁻¹ • f) ?_
    rw [← MeasureTheory.Lp.toTemperedDistributionCLM_apply, map_smul,
      MeasureTheory.Lp.toTemperedDistributionCLM_apply, hf, smul_smul, inv_mul_cancel₀ hc,
      one_smul]

@[simp]
theorem eLpNorm_neg (u : 𝓢'(E, F)) : eLpNorm p (-u) = eLpNorm p u := by
  simpa using eLpNorm_smul (p := p) (-1) u

end TemperedDistribution
