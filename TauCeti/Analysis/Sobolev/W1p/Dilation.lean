/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart.ChangeOfVariables
import TauCeti.MeasureTheory.Function.Lp.Dilation
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Dilations in `W^{1,p}`

Let `E` be a finite-dimensional real inner product space of dimension `n` with an additive Haar
measure `μ`, let `c ≠ 0`, `b : E`, and let `U, V ⊆ E` be open with `U = (c • · + b)⁻¹(V)`. For
every exponent `1 ≤ p ≤ ∞`, precomposition with `x ↦ c • x + b` is given at order one by
`TauCeti.Wkp.compAffineEquiv` specialized to `ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)`,
whose value, gradient, and `W^{1,p}_Γ` invariance are established in
`TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables.Affine` and
`TauCeti.Analysis.Sobolev.W1p.BoundaryPart.ChangeOfVariables`.

This module provides the remaining `W^{1,p}` average and deviation identities for affine
dilations:
* `TauCeti.W1p.eLpNorm_value_compAffineEquiv_smulLeft_sub`: the `Lᵖ` seminorm of the deviation of
  the affine dilate from a constant.
* `TauCeti.W1p.setAverage_value_compAffineEquiv_smulLeft`: means over a set are unchanged by the
  affine dilation.
-/

public section

noncomputable section

open MeasureTheory Module Set TopologicalSpace
open scoped ENNReal InnerProductSpace Pointwise

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure] {U V : Opens E}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {c : ℝ}

/-- **Affine dilation scaling of the deviation from a constant.** For `c ≠ 0`, `1 ≤ p ≤ ∞`,
`U = (c • · + b)⁻¹(V)`, and every `a`,
`‖u (c • · + b) - a‖_{Lᵖ(U)} = |c| ^ (-n / p) ‖u - a‖_{Lᵖ(V)}`, where `n` is the dimension of `E`
(with `(1 / ⊤ : ℝ≥0∞).toReal = 0`, hence factor `1`, at `p = ∞`). -/
theorem W1p.eLpNorm_value_compAffineEquiv_smulLeft_sub (hc : c ≠ 0) (b : E)
    (hUV : (U : Set E) = (fun x ↦ ContinuousLinearEquiv.smulLeft (Units.mk0 c hc) x + b) ⁻¹' V)
    (u : W1p mu V p) (a : ℝ) :
    eLpNorm (fun x ↦
        W1p.value (Wkp.compAffineEquiv mu (ContinuousLinearEquiv.smulLeft (Units.mk0 c hc))
          b hUV 1 u : W1p mu U p) x - a) p (mu.restrict U) =
      ENNReal.ofReal (|c|⁻¹ ^ ((finrank ℝ E : ℝ) / p.toReal)) *
        eLpNorm (fun x ↦ W1p.value u x - a) p (mu.restrict V) := by
  set B : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)
  have hfac : ENNReal.ofReal |(LinearMap.det (B : E →ₗ[ℝ] E))⁻¹| ^ (1 / p).toReal =
      ENNReal.ofReal (|c|⁻¹ ^ ((finrank ℝ E : ℝ) / p.toReal)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) ENNReal.toReal_nonneg, abs_inv,
      ContinuousLinearEquiv.abs_det_smulLeft_inv_rpow E hc p]
  have hae : (fun x ↦
      W1p.value (Wkp.compAffineEquiv mu B b hUV 1 u : W1p mu U p) x - a) =ᵐ[mu.restrict U]
      fun x ↦ W1p.value u (B x + b) - a := by
    have hv1 := congrArg (fun f : Lp ℝ p (mu.restrict U) ↦ (f : E → ℝ))
      (Wkp.value_one (Wkp.compAffineEquiv mu B b hUV 1 u))
    have hv2 := congrArg (fun f : Lp ℝ p (mu.restrict V) ↦ (f : E → ℝ))
      (Wkp.value_one (u : Wkp mu V p 1))
    filter_upwards [Wkp.value_compAffineEquiv_ae mu B b hUV 1 u] with x hx
    rw [← hv1, ← hv2]
    exact congrArg (· - a) hx
  rw [eLpNorm_congr_ae hae, hUV, ← hfac]
  exact Measure.eLpNorm_comp_continuousLinearEquiv_add_restrict_preimage mu
    (fun x ↦ W1p.value u x - a) B b p

/-- **Means are invariant under affine dilation.** For `c ≠ 0`, `1 ≤ p ≤ ∞`,
`U = (c • · + b)⁻¹(V)`, and `S ⊆ V`, the mean of `u (c • · + b)` over `(c • · + b)⁻¹(S)` is the
mean of `u` over `S`. -/
theorem W1p.setAverage_value_compAffineEquiv_smulLeft (hc : c ≠ 0) (b : E)
    (hUV : (U : Set E) = (fun x ↦ ContinuousLinearEquiv.smulLeft (Units.mk0 c hc) x + b) ⁻¹' V)
    {S : Set E} (hS : S ⊆ V) (u : W1p mu V p) :
    ⨍ y in (fun x ↦ c • x + b) ⁻¹' S,
        W1p.value (Wkp.compAffineEquiv mu (ContinuousLinearEquiv.smulLeft (Units.mk0 c hc))
          b hUV 1 u) y ∂mu =
      ⨍ y in S, W1p.value u y ∂mu := by
  set B : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)
  have hpre : (fun x ↦ c • x + b) ⁻¹' S = (fun x ↦ B x + b) ⁻¹' S := by
    ext x; simp [B]
  have hSU : (fun x ↦ B x + b) ⁻¹' S ⊆ (U : Set E) := (preimage_mono hS).trans hUV.symm.subset
  have hvae : W1p.value (Wkp.compAffineEquiv mu B b hUV 1 u) =ᵐ[mu.restrict U]
      fun x ↦ W1p.value u (B x + b) := by
    have hv1 := congrArg (fun f : Lp ℝ p (mu.restrict U) ↦ (f : E → ℝ))
      (Wkp.value_one (Wkp.compAffineEquiv mu B b hUV 1 u))
    have hv2 := congrArg (fun f : Lp ℝ p (mu.restrict V) ↦ (f : E → ℝ))
      (Wkp.value_one (u : Wkp mu V p 1))
    filter_upwards [Wkp.value_compAffineEquiv_ae mu B b hUV 1 u] with x hx
    rw [← hv1, ← hv2]
    exact hx
  rw [hpre, average_congr (ae_restrict_of_ae_restrict_of_subset hSU hvae)]
  have : (mu.map B).IsAddHaarMeasure := B.isAddHaarMeasure_map mu
  have hmap : mu.map ((B.toHomeomorph.trans (Homeomorph.addRight b)).toMeasurableEquiv) =
      (Measure.addHaarScalarFactor (mu.map B) mu : ℝ≥0∞) • mu :=
    Measure.map_continuousLinearEquiv_add_eq_smul mu mu B b
  exact setAverage_comp_preimage_of_map_eq_smul hmap
    (ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (mu.map B) mu).ne')
    ENNReal.coe_ne_top _ S

end TauCeti
