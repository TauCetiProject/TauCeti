/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Brenier
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Mixture.Basic

/-!
# Strict convexity of `W₂ ^ 2` on a Euclidean space

On a finite-dimensional real inner product space, Brenier's theorem
(`TauCeti.IsOptimalCoupling.exists_eq_graphPlan_of_absolutelyContinuous`) shows that every optimal
plan for the cost `edist ^ 2` out of a law absolutely continuous with respect to an additive Haar
measure, such as Lebesgue measure on `ℝⁿ`, into a law at finite `W₂` distance from it, is induced
by a map. This is the hypothesis of the general strict convexity result
`TauCeti.wassersteinEDist_smul_add_smul_rpow_lt`, so `ν ↦ W₂(μ, ν) ^ 2` is strictly convex for
such a `μ`.

## Main statements

* `TauCeti.wassersteinEDist_two_smul_add_smul_sq_lt` — strict convexity of `ν ↦ W₂(μ, ν) ^ 2`
  for an absolutely continuous `μ`.

## References

* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, Chapter 7,
  for strict convexity of `ν ↦ W₂(μ, ν) ^ 2` when `μ` is absolutely continuous.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ρ : Measure E} [ρ.IsAddHaarMeasure]

/-- **Strict convexity of `ν ↦ W₂(μ, ν) ^ 2` for an absolutely continuous `μ`.** On a
finite-dimensional real inner product space, let `μ` be a probability law absolutely continuous
with respect to an additive Haar measure, and let `ν₀ ≠ ν₁` be probability laws at finite `W₂`
distance from `μ`. For nonzero weights with `a + b = 1`,
`W₂(μ, a • ν₀ + b • ν₁) ^ 2 < a * W₂(μ, ν₀) ^ 2 + b * W₂(μ, ν₁) ^ 2`. -/
theorem wassersteinEDist_two_smul_add_smul_sq_lt {μ ν₀ ν₁ : Measure E} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁] (hμ : μ ≪ ρ) {a b : ℝ≥0∞}
    (hab : a + b = 1) (ha : a ≠ 0) (hb : b ≠ 0) (h₀ : wassersteinEDist 2 μ ν₀ ≠ ∞)
    (h₁ : wassersteinEDist 2 μ ν₁ ≠ ∞) (hne : ν₀ ≠ ν₁) :
    wassersteinEDist 2 μ (a • ν₀ + b • ν₁) ^ 2
      < a * wassersteinEDist 2 μ ν₀ ^ 2 + b * wassersteinEDist 2 μ ν₁ ^ 2 := by
  have hle := wassersteinEDist_smul_add_smul_rpow_le measurable_edist two_ne_zero
    ENNReal.ofNat_ne_top hab μ ν₀ ν₁
  have hlt := wassersteinEDist_smul_add_smul_rpow_lt two_ne_zero ENNReal.ofNat_ne_top hab ha hb
    (μ := μ) (fun π hπ ↦ ?_) hne
  · simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat] using hlt
  -- The mixture is at finite distance from `μ`, by convexity, so Brenier's theorem applies.
  have hfin : wassersteinEDist 2 μ (a • ν₀ + b • ν₁) ≠ ∞ := by
    obtain ⟨ha', hb'⟩ := ENNReal.add_ne_top.1 (hab ▸ ENNReal.one_ne_top)
    simp only [ENNReal.toReal_ofNat] at hle
    refine fun htop ↦ (ne_top_of_le_ne_top ?_ hle) (by simp [htop])
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ha' (ENNReal.rpow_ne_top_of_nonneg zero_le_two h₀),
        ENNReal.mul_ne_top hb' (ENNReal.rpow_ne_top_of_nonneg zero_le_two h₁)⟩
  rw [ENNReal.toReal_ofNat] at hπ
  obtain ⟨T, hT, hπT⟩ := hπ.exists_eq_graphPlan_of_absolutelyContinuous hμ hfin
  exact ⟨T, hT.aemeasurable, hπT⟩

end TauCeti
