/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.ReducedBoundary
import TauCeti.Analysis.Distribution.TestFunction.Approximation

/-!
# Integration by parts against `C¹` vector fields and the Gauss–Green formula

Let `Ω` be an open set of a finite-dimensional real inner product space `E` and `u : E → ℝ` a
function locally integrable on `Ω` with locally finite variation, with polar decomposition
`Du = σ_u |Du|` (`TauCeti.polarDensity`, `TauCeti.variationMeasure`). By definition the identity

`∫ u div φ dμ = -∫ ⟪φ, σ_u⟫ d|Du|`

holds for smooth test vector fields `φ ∈ 𝓓(Ω, E)`. This file extends it to every `C¹` vector field
`φ` with compact support in `Ω`, where `div φ = tr (Dφ)`
(`TauCeti.integral_trace_fderiv_mul_eq_neg_integral_inner_polarDensity`). For the indicator of a
set `s` of locally finite perimeter in `Ω`, with outer normal `ν_s` (`TauCeti.outerNormal`), this
is the **Gauss–Green formula** for compactly supported `C¹` vector fields:

`∫_s div φ dμ = ∫ ⟪φ, ν_s⟫ d|Dχ_s|`

(`TauCeti.integral_trace_fderiv_mul_indicator_eq_integral_inner_outerNormal`). The perimeter
measure `|Dχ_s|` is concentrated on the reduced boundary (`TauCeti.ae_mem_reducedBoundary`).

Mollification approximates a compactly supported `C¹` field by test fields uniformly together with
their derivatives, with supports in a fixed compact subset of `Ω`
(`ContDiff.exists_testFunction_dist_le_and_dist_fderiv_le`). Both sides of the identity are
continuous for this convergence: the left side because `u` is integrable on that compact set
(`TauCeti.dist_integral_trace_fderiv_mul_le`), and the right side because the variation measure
is finite there (`TauCeti.dist_integral_inner_polarDensity_le`).

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.1.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §12.1 (the
  Gauss–Green measure of a set of locally finite perimeter).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace Set Filter Metric TestFunction
open scoped ENNReal RealInnerProductSpace Distributions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω : Opens E} {u : E → ℝ} {s : Set E}

/-- Vector fields supported in a fixed compact set `K` whose derivatives are uniformly close have
close divergence pairings `∫ div φ * u dμ` with a function `u` integrable on `K`. The constant is
the norm of the trace times `∫_K |u| dμ`. -/
theorem dist_integral_trace_fderiv_mul_le {K : Set E} (hK : IsCompact K)
    (hu : IntegrableOn u K μ) {f g : E → E} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfK : tsupport f ⊆ K) (hgK : tsupport g ⊆ K) {ε : ℝ}
    (hε : ∀ x, dist (fderiv ℝ f x) (fderiv ℝ g x) ≤ ε) :
    dist (∫ x, LinearMap.trace ℝ E (fderiv ℝ f x : E →ₗ[ℝ] E) * u x ∂μ)
      (∫ x, LinearMap.trace ℝ E (fderiv ℝ g x : E →ₗ[ℝ] E) * u x ∂μ) ≤
      ‖traceCLM ℝ E‖ * ε * ∫ x in K, ‖u x‖ ∂μ := by
  have hdiv {h : E → E} (hh : ContDiff ℝ 1 h) :
      Continuous fun x => LinearMap.trace ℝ E (fderiv ℝ h x : E →ₗ[ℝ] E) := by
    simpa [Function.comp_def] using
      (traceCLM ℝ E).continuous.comp (hh.continuous_fderiv one_ne_zero)
  -- Both integrands vanish off `K`, where `u` is integrable.
  have hvan {h : E → E} (hhK : tsupport h ⊆ K) (x : E) (hx : x ∉ K) :
      LinearMap.trace ℝ E (fderiv ℝ h x : E →ₗ[ℝ] E) * u x = 0 := by
    simp [image_eq_zero_of_notMem_tsupport fun h' => hx (hhK (tsupport_fderiv_subset ℝ h'))]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (hvan hfK),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (hvan hgK), dist_eq_norm,
    ← integral_sub (hu.continuousOn_mul (hdiv hf).continuousOn hK)
      (hu.continuousOn_mul (hdiv hg).continuousOn hK), ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hu.norm.const_mul _) (Eventually.of_forall fun x => ?_)
  have htr : LinearMap.trace ℝ E (fderiv ℝ f x : E →ₗ[ℝ] E) -
      LinearMap.trace ℝ E (fderiv ℝ g x : E →ₗ[ℝ] E) =
        traceCLM ℝ E (fderiv ℝ f x - fderiv ℝ g x) := by
    simp [map_sub]
  rw [← sub_mul, htr, norm_mul]
  gcongr
  exact ((traceCLM ℝ E).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using hε x) (norm_nonneg _))

/-- **Integration by parts against `C¹` vector fields.** For `u` locally integrable on `Ω` with
locally finite variation, the polar decomposition `Du = σ_u |Du|` represents the distributional
derivative against every `C¹` vector field `φ` with compact support in `Ω`:
`∫ u div φ dμ = -∫ ⟪φ, σ_u⟫ d|Du|`, where `div φ = tr (Dφ)`. -/
theorem integral_trace_fderiv_mul_eq_neg_integral_inner_polarDensity
    (hu : LocallyIntegrableOn u Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞)
    {φ : E → E} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    ∫ x, LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) * u x ∂μ =
      -∫ x, ⟪φ x, polarDensity μ Ω u x⟫ ∂variationMeasure μ Ω u := by
  obtain ⟨δ, hδ, hδΩ⟩ := hc.isCompact.exists_cthickening_subset_open Ω.isOpen hs
  set K := cthickening δ (tsupport φ)
  have hK : IsCompact K := hc.isCompact.cthickening
  have hφK : tsupport φ ⊆ K := self_subset_cthickening _
  have huK : IntegrableOn u K μ := hu.integrableOn_compact_subset hδΩ hK
  set C := ‖traceCLM ℝ E‖ * ∫ x in K, ‖u x‖ ∂μ +
    (variationMeasure μ Ω u).real (((↑) : Ω → E) ⁻¹' K)
  have hC : 0 ≤ C := by positivity
  -- Compare both sides with those of a test field `ψ` that is `C¹`-close to `φ`.
  refine dist_le_zero.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  set η := ε / (C + 1)
  have hη : 0 < η := by positivity
  obtain ⟨ψ, hψK, hψ⟩ :=
    hφ.exists_testFunction_dist_le_and_dist_fderiv_le hc.isCompact subset_rfl hδ hδΩ hη
  have hψ1 : ContDiff ℝ 1 (ψ : E → E) := ψ.contDiff.of_le (by simp)
  have hL := dist_integral_trace_fderiv_mul_le hK huK hφ hψ1 hφK hψK fun x => by
    rw [dist_comm]
    exact (hψ x).2
  have hR := dist_integral_inner_polarDensity_le hu hfin hψ1.continuous hφ.continuous hK hδΩ
    hψK hφK fun x => (hψ x).1
  have hEq := integral_divergenceCLM_mul_eq_neg_integral_inner_polarDensity hu hfin ψ
  simp only [divergenceCLM_apply] at hEq
  calc _ ≤ dist (∫ x, LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) * u x ∂μ)
          (∫ x, LinearMap.trace ℝ E (fderiv ℝ ψ x : E →ₗ[ℝ] E) * u x ∂μ) +
        dist (∫ x, ⟪ψ x, polarDensity μ Ω u x⟫ ∂variationMeasure μ Ω u)
          (∫ x, ⟪φ x, polarDensity μ Ω u x⟫ ∂variationMeasure μ Ω u) := by
        refine (dist_triangle _
          (∫ x, LinearMap.trace ℝ E (fderiv ℝ ψ x : E →ₗ[ℝ] E) * u x ∂μ) _).trans_eq ?_
        rw [hEq, dist_neg_neg]
    _ ≤ η * C := by
        rw [mul_add, ← mul_assoc, mul_comm η]
        exact add_le_add hL hR
    _ ≤ 0 + ε := by
        rw [zero_add, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith

/-- **The Gauss–Green formula for `C¹` vector fields.** For a set `s` of locally finite perimeter
in `Ω` with outer normal `ν_s`, `∫_s div φ dμ = ∫ ⟪φ, ν_s⟫ d|Dχ_s|` for every `C¹` vector field
`φ` with compact support in `Ω`, where `div φ = tr (Dφ)`. -/
theorem integral_trace_fderiv_mul_indicator_eq_integral_inner_outerNormal
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)
    {φ : E → E} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    ∫ x, LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) * s.indicator 1 x ∂μ =
      ∫ y, ⟪φ y, outerNormal μ Ω s y⟫ ∂variationMeasure μ Ω (s.indicator 1) := by
  rw [integral_trace_fderiv_mul_eq_neg_integral_inner_polarDensity hu hfin hφ hc hs,
    ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [ae_outerNormal_eq] with y hy
  rw [hy, inner_neg_right]

end TauCeti
