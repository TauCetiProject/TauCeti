/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.ReducedBoundary

/-!
# The Gauss–Green formula for `C¹` vector fields

Let `Ω` be an open set of a finite-dimensional real inner product space `E` and `s` a set of
locally finite perimeter in `Ω`, with outer normal `ν_s` (`TauCeti.outerNormal`). For every `C¹`
vector field `φ` with compact support in `Ω`, with `div φ = tr (Dφ)`, this file proves the
**Gauss–Green formula**

`∫_s div φ dμ = ∫ ⟪φ, ν_s⟫ d|Dχ_s|`

(`TauCeti.integral_trace_fderiv_mul_indicator_eq_integral_inner_outerNormal`). The perimeter
measure `|Dχ_s|` is concentrated on the reduced boundary (`TauCeti.ae_mem_reducedBoundary`).
It is the case `u = χ_s` of integration by parts against `C¹` vector fields,
`∫ u div φ dμ = -∫ ⟪φ, σ_u⟫ d|Du|`
(`TauCeti.integral_trace_fderiv_mul_eq_neg_integral_inner_polarDensity`), since `ν_s = -σ_{χ_s}`
almost everywhere (`TauCeti.ae_outerNormal_eq`).

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.1.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §12.1 (the
  Gauss–Green measure of a set of locally finite perimeter).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace Set
open scoped ENNReal RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω : Opens E} {u : E → ℝ} {s : Set E}

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
