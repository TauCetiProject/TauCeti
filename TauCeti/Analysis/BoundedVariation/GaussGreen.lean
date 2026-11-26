/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.DeGiorgi
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.TestFunction.Divergence
import TauCeti.MeasureTheory.Integral.DominatedConvergence

/-!
# The Gauss–Green formula for fields without compact support

Let `E` be a finite-dimensional real inner product space and `s ⊆ E` a set of finite perimeter
`P(s) = P(s; E)`. De Giorgi's theorem gives the Gauss–Green formula with surface measure,
`∫_s div φ = ∫_{∂*s} ⟪φ, ν_s⟫ dHⁿ⁻¹`, for `C¹` fields `φ` with compact support
(`TauCeti.integral_trace_fderiv_mul_indicator_eq_setIntegral_inner_outerNormal`). This file
removes the compact support: the formula holds for a bounded `C¹` field `φ` whose divergence is
integrable on `s`, provided that `s` has finite volume or `‖φ‖` is integrable on `s`
(`TauCeti.integral_trace_fderiv_mul_indicator_eq_setIntegral_inner_outerNormal_of_bounded`).

The proof applies the compactly supported formula to `ρ_k φ`, where `ρ_k` is a cutoff equal to
`1` on the ball of radius `k + 1` with `‖Dρ_k‖ ≤ C / (k + 1)`
(`TauCeti.exists_cutoff_fderiv_bound`). Then `div (ρ_k φ) = ρ_k div φ + Dρ_k φ`; the first term
converges to `div φ` by dominated convergence (`TauCeti.tendsto_integral_smul_of_eq_one_ball`),
the integral over `s` of the second is at most `C / (k + 1)` times `M |s|` or `∫_s ‖φ‖`, and the
boundary integrals converge by the same lemma applied to the finite measure `Hⁿ⁻¹⌊∂*s`, of total
mass `P(s)`.

Without one of the two integrability hypotheses the formula fails: for `s` the exterior of the
unit ball and a bounded field equal to `x / ‖x‖ⁿ` on `s`, the divergence vanishes on `s` while the
flux through the sphere is `−n ω_n`.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, 14.1 and Theorem 14.3.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Measure TopologicalSpace Set Filter Metric Module
open scoped ENNReal Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {s : Set E}

/-- The error terms `∫_s Dρ_k φ` of the cutoffs are integrable and tend to `0`: they are
bounded by `C / (k + 1)` times `M |s|` or `∫_s ‖φ‖`. -/
private theorem integrable_and_tendsto_integral_apply_mul_indicator
    (hu : LocallyIntegrable (s.indicator (1 : E → ℝ))) {φ : E → E} (hφ : Continuous φ) {M : ℝ}
    (hM : ∀ x, ‖φ x‖ ≤ M)
    (h : Integrable (s.indicator (1 : E → ℝ)) ∨ Integrable fun x ↦ ‖φ x‖ * s.indicator 1 x)
    {C : ℝ} (hC0 : 0 ≤ C) {ρ' : ℕ → E → E →L[ℝ] ℝ}
    (hρ'b : ∀ (k : ℕ) x, ‖ρ' k x‖ ≤ C * ((k : ℝ) + 1)⁻¹) (hρ'c : ∀ k, Continuous (ρ' k))
    (hρ's : ∀ k, HasCompactSupport (ρ' k)) :
    (∀ k, Integrable fun x ↦ ρ' k x (φ x) * s.indicator 1 x) ∧
      Tendsto (fun k : ℕ ↦ ∫ x, ρ' k x (φ x) * s.indicator 1 x) atTop (𝓝 0) := by
  have hind (x : E) : ‖s.indicator (1 : E → ℝ) x‖ ≤ 1 := by
    by_cases hx : x ∈ s <;> simp [hx]
  refine ⟨fun k ↦ ?_, ?_⟩
  · have hg : Integrable fun x ↦ ρ' k x (φ x) :=
      ((hρ'c k).clm_apply hφ).integrable_of_hasCompactSupport
        ((hρ's k).mono fun x hx h0 ↦ hx (by simp [h0]))
    exact hg.mul_bdd hu.aestronglyMeasurable (ae_of_all _ hind)
  -- A dominating integrable function `G ≥ ‖φ‖ 1_s`.
  obtain ⟨G, hG, hGb⟩ : ∃ G : E → ℝ, Integrable G ∧
      ∀ x, ‖φ x‖ * ‖s.indicator (1 : E → ℝ) x‖ ≤ G x := by
    rcases h with h | h
    · refine ⟨fun x ↦ M * s.indicator 1 x, h.const_mul M, fun x ↦ ?_⟩
      by_cases hx : x ∈ s <;> simp [hx, hM x]
    · refine ⟨fun x ↦ ‖φ x‖ * s.indicator 1 x, h, fun x ↦ ?_⟩
      by_cases hx : x ∈ s <;> simp [hx]
  have hlim : Tendsto (fun k : ℕ ↦ C * ((k : ℝ) + 1)⁻¹ * ∫ x, G x) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul C).mul_const (∫ x, G x)
    simpa [one_div] using this
  refine squeeze_zero_norm (fun k ↦ ?_) hlim
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hG.const_mul _) (ae_of_all _ fun x ↦ ?_)
  calc ‖ρ' k x (φ x) * s.indicator 1 x‖
      ≤ ‖ρ' k x‖ * ‖φ x‖ * ‖s.indicator (1 : E → ℝ) x‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right ((ρ' k x).le_opNorm _) (norm_nonneg _)
    _ ≤ C * ((k : ℝ) + 1)⁻¹ * G x := by
        rw [mul_assoc]
        exact mul_le_mul (hρ'b k x) (hGb x) (by positivity) (by positivity)

/-- The boundary integrals `∫_{∂*s} ⟪ρ_k φ, ν_s⟫ dHⁿ⁻¹` of the cutoffs converge to
`∫_{∂*s} ⟪φ, ν_s⟫ dHⁿ⁻¹`, by dominated convergence against the finite measure `Hⁿ⁻¹⌊∂*s`. -/
private theorem tendsto_setIntegral_inner_smul_outerNormal
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) (⊤ : Opens E) volume)
    (hfin : ∀ K, IsCompact K → K ⊆ (⊤ : Opens E) →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U (s.indicator 1) ≠ ∞)
    (hP : perimeter volume ⊤ s ≠ ∞) {φ : E → E} (hφ : Continuous φ) {M : ℝ}
    (hM : ∀ x, ‖φ x‖ ≤ M) {ρ : ℕ → E → ℝ} (hρc : ∀ k, Continuous (ρ k))
    (hρ01 : ∀ k x, 0 ≤ ρ k x ∧ ρ k x ≤ 1)
    (hρ1 : ∀ (k : ℕ), ∀ x ∈ closedBall (0 : E) ((k : ℝ) + 1), ρ k x = 1) :
    Tendsto (fun k : ℕ ↦ ∫ x in reducedBoundary volume ⊤ s,
        ⟪ρ k x • φ x, outerNormal volume ⊤ s x⟫ ∂μHE[finrank ℝ E - 1]) atTop
      (𝓝 (∫ x in reducedBoundary volume ⊤ s, ⟪φ x, outerNormal volume ⊤ s x⟫
        ∂μHE[finrank ℝ E - 1])) := by
  set H := μHE[finrank ℝ E - 1].restrict (reducedBoundary volume ⊤ s)
  have hH : IsFiniteMeasure H := ⟨by
    rw [Measure.restrict_apply_univ, ← perimeter_eq_euclideanHausdorffMeasure_reducedBoundary
      hu hfin]
    exact hP.lt_top⟩
  have hb : ∀ᵐ x ∂H, ‖⟪φ x, outerNormal volume ⊤ s x⟫‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_reducedBoundary] with x hx
    refine (norm_inner_le_norm _ _).trans ?_
    rw [norm_outerNormal hx, mul_one]
    exact hM x
  have hi : Integrable (fun x ↦ ⟪φ x, outerNormal volume ⊤ s x⟫) H :=
    ⟨hφ.aestronglyMeasurable.inner measurable_outerNormal.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded hb⟩
  simpa only [real_inner_smul_left, smul_eq_mul] using
    tendsto_integral_smul_of_eq_one_ball (R := fun k : ℕ ↦ (k : ℝ) + 1)
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      (fun k ↦ (hρc k).aestronglyMeasurable)
      (fun k x hx ↦ hρ1 k x (mem_closedBall_zero_iff.2 hx.le)) hρ01 hi

/-- **The Gauss–Green formula for bounded fields.** Let `s` have finite perimeter `P(s)` and let
`φ` be a bounded `C¹` vector field whose divergence is integrable on `s`. If `s` has finite volume
or `‖φ‖` is integrable on `s`, then

`∫_s div φ = ∫_{∂*s} ⟪φ, ν_s⟫ dHⁿ⁻¹`. -/
theorem integral_trace_fderiv_mul_indicator_eq_setIntegral_inner_outerNormal_of_bounded
    (hu : LocallyIntegrable (s.indicator (1 : E → ℝ)))
    (hP : perimeter volume ⊤ s ≠ ∞) {φ : E → E} (hφ : ContDiff ℝ 1 φ) {M : ℝ}
    (hM : ∀ x, ‖φ x‖ ≤ M)
    (hdiv : Integrable fun x ↦ LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) * s.indicator 1 x)
    (h : Integrable (s.indicator (1 : E → ℝ)) ∨ Integrable fun x ↦ ‖φ x‖ * s.indicator 1 x) :
    ∫ x, LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) * s.indicator 1 x =
      ∫ x in reducedBoundary volume ⊤ s, ⟪φ x, outerNormal volume ⊤ s x⟫
        ∂μHE[finrank ℝ E - 1] := by
  have hu' : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) (⊤ : Opens E) volume :=
    hu.locallyIntegrableOn _
  have hfin : ∀ K, IsCompact K → K ⊆ (⊤ : Opens E) →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U (s.indicator 1) ≠ ∞ :=
    fun K _ _ ↦ ⟨⊤, by simp, by rwa [← perimeter_def]⟩
  -- The cutoffs `ρ_k`, equal to `1` on the ball of radius `k + 1`.
  obtain ⟨C, hC0, hcut⟩ := exists_cutoff_fderiv_bound (E := E)
  choose ρ ρ' hρs hρ01 hρ1 hρ0 hρd hρ'b hρ'c _ using
    fun k : ℕ ↦ hcut 0 ((k : ℝ) + 1) (by positivity)
  have hρK (k : ℕ) : HasCompactSupport (ρ k) :=
    HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * ((k : ℝ) + 1))) fun x hx ↦
      hρ0 k x (by simpa [mem_closedBall_zero_iff, dist_zero_right] using hx)
  have hρ'K (k : ℕ) : HasCompactSupport (ρ' k) := by
    simpa only [funext fun x ↦ (hρd k x).fderiv] using (hρK k).fderiv (𝕜 := ℝ)
  -- The compactly supported formula for `ρ_k φ`.
  have hGG (k : ℕ) := integral_trace_fderiv_mul_indicator_eq_setIntegral_inner_outerNormal hu'
    hfin ((hρs k 1).smul hφ) (hρK k).smul_right (by simp)
  -- The right sides converge, by dominated convergence against `Hⁿ⁻¹⌊∂*s`.
  have hR := tendsto_setIntegral_inner_smul_outerNormal hu' hfin hP hφ.continuous hM
    (fun k ↦ (hρs k 0).continuous) hρ01 hρ1
  -- The left sides converge: `div (ρ_k φ) = ρ_k div φ + Dρ_k φ`.
  set D := fun x ↦ LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) * s.indicator 1 x
  have hsplit (k : ℕ) (x : E) :
      LinearMap.trace ℝ E (fderiv ℝ (fun y ↦ ρ k y • φ y) x : E →ₗ[ℝ] E) * s.indicator 1 x =
        ρ k x * D x + ρ' k x (φ x) * s.indicator 1 x := by
    rw [trace_fderiv_smul (hρd k x).differentiableAt (hφ.differentiable one_ne_zero x),
      (hρd k x).fderiv]
    ring
  have hI₁ (k : ℕ) : Integrable fun x ↦ ρ k x * D x :=
    hdiv.bdd_mul (hρs k 0).continuous.aestronglyMeasurable
      (ae_of_all _ fun x ↦ by rw [Real.norm_of_nonneg (hρ01 k x).1]; exact (hρ01 k x).2)
  have hL₁ : Tendsto (fun k : ℕ ↦ ∫ x, ρ k x * D x) atTop (𝓝 (∫ x, D x)) := by
    simpa only [smul_eq_mul] using tendsto_integral_smul_of_eq_one_ball
      (R := fun k : ℕ ↦ (k : ℝ) + 1)
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      (fun k ↦ (hρs k 0).continuous.aestronglyMeasurable)
      (fun k x hx ↦ hρ1 k x (mem_closedBall_zero_iff.2 hx.le)) hρ01 hdiv
  obtain ⟨hI₂, hL₂⟩ := integrable_and_tendsto_integral_apply_mul_indicator hu hφ.continuous hM h
    hC0 hρ'b hρ'c hρ'K
  have hL : Tendsto (fun k : ℕ ↦ ∫ x, ρ k x * D x + ρ' k x (φ x) * s.indicator 1 x) atTop
      (𝓝 (∫ x, D x)) := by
    have := hL₁.add hL₂
    rw [add_zero] at this
    exact this.congr fun k ↦ (integral_add (hI₁ k) (hI₂ k)).symm
  exact tendsto_nhds_unique hL (hR.congr fun k ↦
    (hGG k).symm.trans (integral_congr_ae (ae_of_all _ fun x ↦ hsplit k x)))

end TauCeti
