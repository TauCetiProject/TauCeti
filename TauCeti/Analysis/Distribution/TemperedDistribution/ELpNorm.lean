/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# The `Lᵖ` norm of a tempered distribution

For `1 ≤ p ≤ ∞` an `Lᵖ` function `f` defines the tempered distribution `φ ↦ ∫ φ • f`
(`MeasureTheory.Lp.toTemperedDistribution`). The **extended `Lᵖ` norm** of a tempered
distribution `u` is

`‖u‖_p = ⨅ {f ∈ Lᵖ | f = u in 𝓢'}, ‖f‖_p`,

which is `‖f‖_p` when `u` is the distribution of `f ∈ Lᵖ` (the embedding of `Lᵖ` into `𝓢'` is
injective) and `∞` when `u` is not given by an `Lᵖ` function. It is the analogue for tempered
distributions of `MeasureTheory.eLpNorm`: an `ℝ≥0∞`-valued seminorm, defined for every `u`, which is
finite exactly on the image of `Lᵖ`. It measures the size of frequency-localized pieces of a
distribution, such as its Littlewood–Paley blocks, without first choosing a representative.

## Main declarations

* `TemperedDistribution.eLpNorm`: the extended `Lᵖ` norm of a tempered distribution.
* `TemperedDistribution.eLpNorm_toTemperedDistribution`: `‖f‖_p` for `f ∈ Lᵖ`.
* `TemperedDistribution.eLpNorm_lt_top_iff`: the norm is finite exactly on the image of `Lᵖ`.
* `TemperedDistribution.eLpNorm_add_le`, `TemperedDistribution.eLpNorm_smul`: the seminorm laws.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal SchwartzMap

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The **extended `Lᵖ` norm** of a tempered distribution: the infimum of `‖f‖_p` over the
`f ∈ Lᵖ(μ)` whose tempered distribution is `u`. It is `‖f‖_p` on the distribution of
`f ∈ Lᵖ(μ)` (`TemperedDistribution.eLpNorm_toTemperedDistribution`) and `∞` on a distribution
that is not given by an `Lᵖ` function (`TemperedDistribution.eLpNorm_lt_top_iff`). -/
def eLpNorm (u : 𝓢'(E, F)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure E := by volume_tac)
    [μ.HasTemperateGrowth] : ℝ≥0∞ :=
  ⨅ (f : Lp F p μ) (_ : (f : 𝓢'(E, F)) = u), ‖f‖ₑ

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure E} [μ.HasTemperateGrowth]

/-- The extended `Lᵖ` norm of `u` is at most the norm of any `Lᵖ` function representing `u`. -/
theorem eLpNorm_le_enorm {u : 𝓢'(E, F)} (f : Lp F p μ) (hf : (f : 𝓢'(E, F)) = u) :
    eLpNorm u p μ ≤ ‖f‖ₑ :=
  iInf₂_le f hf

/-- **The extended `Lᵖ` norm is finite exactly on `Lᵖ`.** -/
theorem eLpNorm_lt_top_iff {u : 𝓢'(E, F)} :
    eLpNorm u p μ < ∞ ↔ ∃ f : Lp F p μ, (f : 𝓢'(E, F)) = u := by
  refine ⟨fun h ↦ ?_, fun ⟨f, hf⟩ ↦ (eLpNorm_le_enorm f hf).trans_lt enorm_lt_top⟩
  by_contra! hu
  simp [eLpNorm, hu] at h

/-- A tempered distribution that is not given by an `Lᵖ` function has extended `Lᵖ` norm `∞`. -/
theorem eLpNorm_eq_top_iff {u : 𝓢'(E, F)} :
    eLpNorm u p μ = ∞ ↔ ∀ f : Lp F p μ, (f : 𝓢'(E, F)) ≠ u := by
  rw [← not_lt_top_iff, eLpNorm_lt_top_iff, not_exists]

/-- On the tempered distribution of an `Lᵖ` function, the extended `Lᵖ` norm is the `Lᵖ` norm. -/
@[simp]
theorem eLpNorm_toTemperedDistribution [FiniteDimensional ℝ E] [IsLocallyFiniteMeasure μ]
    (f : Lp F p μ) : eLpNorm (f : 𝓢'(E, F)) p μ = ‖f‖ₑ := by
  refine le_antisymm (eLpNorm_le_enorm f rfl) (le_iInf₂ fun g hg ↦ ?_)
  have := Lp.ker_toTemperedDistributionCLM_eq_bot (F := F) (μ := μ) (p := p)
  rw [LinearMap.ker_eq_bot] at this
  obtain rfl : g = f := this (by simpa using hg)
  exact le_rfl

@[simp]
theorem eLpNorm_zero : eLpNorm (0 : 𝓢'(E, F)) p μ = 0 :=
  nonpos_iff_eq_zero.1 <| (eLpNorm_le_enorm (0 : Lp F p μ) (by
    simpa only [Lp.toTemperedDistributionCLM_apply] using
      map_zero (Lp.toTemperedDistributionCLM F μ p))).trans_eq enorm_zero

/-- **Triangle inequality** for the extended `Lᵖ` norm of tempered distributions. -/
theorem eLpNorm_add_le (u v : 𝓢'(E, F)) :
    eLpNorm (u + v) p μ ≤ eLpNorm u p μ + eLpNorm v p μ := by
  simp only [eLpNorm, ENNReal.iInf_add, ENNReal.add_iInf]
  refine le_iInf₂ fun g hg ↦ le_iInf₂ fun f hf ↦ iInf₂_le_of_le (f + g) ?_ (enorm_add_le f g)
  simpa only [Lp.toTemperedDistributionCLM_apply, hf, hg] using
    (Lp.toTemperedDistributionCLM F μ p).map_add f g

theorem eLpNorm_smul_le (c : ℂ) (u : 𝓢'(E, F)) :
    eLpNorm (c • u) p μ ≤ ‖c‖ₑ * eLpNorm u p μ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  simp only [eLpNorm, ENNReal.mul_iInf_of_ne (enorm_ne_zero.2 hc) enorm_ne_top]
  refine le_iInf₂ fun f hf ↦ iInf₂_le_of_le (c • f) ?_ (enorm_smul c f).le
  simpa only [Lp.toTemperedDistributionCLM_apply, hf] using
    (Lp.toTemperedDistributionCLM F μ p).map_smul c f

/-- The extended `Lᵖ` norm is absolutely homogeneous. -/
theorem eLpNorm_smul (c : ℂ) (u : 𝓢'(E, F)) :
    eLpNorm (c • u) p μ = ‖c‖ₑ * eLpNorm u p μ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  refine le_antisymm (eLpNorm_smul_le c u) ?_
  calc ‖c‖ₑ * eLpNorm u p μ = ‖c‖ₑ * eLpNorm (c⁻¹ • c • u) p μ := by rw [inv_smul_smul₀ hc]
    _ ≤ ‖c‖ₑ * (‖c⁻¹‖ₑ * eLpNorm (c • u) p μ) := by gcongr; exact eLpNorm_smul_le _ _
    _ = eLpNorm (c • u) p μ := by
      rw [← mul_assoc, ← enorm_mul, mul_inv_cancel₀ hc, enorm_one, one_mul]

@[simp]
theorem eLpNorm_neg (u : 𝓢'(E, F)) : eLpNorm (-u) p μ = eLpNorm u p μ := by
  simpa using eLpNorm_smul (p := p) (μ := μ) (-1) u

end TemperedDistribution
