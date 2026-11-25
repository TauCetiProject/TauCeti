/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Basic
public import TauCeti.Analysis.BoundedVariation.DeGiorgi
import TauCeti.Analysis.Distribution.TestFunction.Divergence

/-!
# The weighted Gauss–Green formula

Let `W` be a `C¹` weight on a finite-dimensional real inner product space `E` of dimension
`n ≥ 2`, with measure `μ = e^{−W} · volume`, and let `U` be a set of locally finite perimeter in
an open set `Ω`, with reduced boundary `∂*U` and outer normal `ν_U`. For every `C¹` vector field
`X` with compact support in `Ω`,

`∫_U div_μ X dμ = ∫_{∂*U} ⟨X, ν_U⟩ e^{−W} dHⁿ⁻¹`,

where `div_μ X = div X − ⟨∇W, X⟩` is the weighted divergence
(`TauCeti.integral_weightedDivergence_eq_integral_reducedBoundary`). This is the Euclidean
Gauss–Green formula with surface measure
(`TauCeti.integral_trace_fderiv_mul_indicator_eq_setIntegral_inner_outerNormal`) applied to the
field `e^{−W} X`, whose divergence is `e^{−W} div_μ X` (`TauCeti.trace_fderiv_exp_neg_smul`).

## References

* E. Milman, J. Neeman, *The Gaussian double-bubble and multi-bubble conjectures*, Ann. of Math.
  (2022), equation (3.1).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Module
open scoped ENNReal RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {W : E → ℝ} {Ω : Opens E} {s : Set E}

/-- **The weighted Gauss–Green formula.** For a `C¹` weight `W`, in dimension `n ≥ 2`, a set `s`
of locally finite perimeter in `Ω` and a `C¹` vector field `X` with compact support in `Ω`,
`∫_s div_μ X dμ = ∫_{∂*s} ⟨X, ν_s⟩ e^{−W} dHⁿ⁻¹`, where `div_μ X = div X − DW X`. -/
theorem integral_weightedDivergence_eq_integral_reducedBoundary (hW : ContDiff ℝ 1 W)
    (hn : 2 ≤ finrank ℝ E) (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω volume)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U (s.indicator 1) ≠ ∞)
    {X : E → E} (hX : ContDiff ℝ 1 X) (hc : HasCompactSupport X) (hXΩ : tsupport X ⊆ Ω) :
    ∫ x, (LinearMap.trace ℝ E (fderiv ℝ X x : E →ₗ[ℝ] E) - fderiv ℝ W x (X x)) *
        Real.exp (-W x) * s.indicator 1 x =
      ∫ x in reducedBoundary volume Ω s, ⟪X x, outerNormal volume Ω s x⟫ * Real.exp (-W x)
        ∂μHE[finrank ℝ E - 1] := by
  have hWd := hW.differentiable one_ne_zero
  have hφ : ContDiff ℝ 1 fun y => Real.exp (-W y) • X y := hW.neg.exp.smul hX
  have key := integral_trace_fderiv_mul_indicator_eq_setIntegral_inner_outerNormal hn hu hfin hφ
    hc.smul_left ((tsupport_smul_subset_right _ _).trans hXΩ)
  simp_rw [trace_fderiv_exp_neg_smul (hWd _) (hX.differentiable one_ne_zero _),
    real_inner_smul_left] at key
  rw [key]
  congr 1 with x
  ring

end TauCeti
