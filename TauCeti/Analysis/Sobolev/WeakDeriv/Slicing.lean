/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence
public import TauCeti.MeasureTheory.Measure.Lebesgue.OrthogonalSlices
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz

/-!
# Transverse divergence of line integrals

Let `E` be a finite-dimensional real inner product space with its volume, `e` a unit vector, and
`φ` a test vector field on the orthogonal hyperplane `(ℝ ∙ e)ᗮ`. For a compactly supported `C¹`
function `w`, the line integrals `y ↦ ∫ w (y + t • e) dt` pair with the divergence of `φ` as

`∫ div φ (y) ∫ w (y + t • e) dt dy = -∫_E Dw (φ ∘ π)`,

where `π` is the orthogonal projection onto `(ℝ ∙ e)ᗮ`, so that `-∫_E Dw (φ ∘ π)` is the
integral of `-Dw (y + t • e) (φ y)` over the orthogonal line coordinates `(y, t)`. This is
integration by parts (`TauCeti.HasWeakFDerivOn.integral_divergenceCLM_smul_eq_neg_integral`) on
each hyperplane `t = const`, combined with Fubini's theorem in orthogonal line coordinates
(`TauCeti.integral_mul_integral_line_eq`). It computes the transverse variation of the line
integrals in the slicing theory of functions of bounded variation.

## Main results

* `TauCeti.integral_divergence_mul_integral_line_eq`: the pairing of the line integrals of a
  compactly supported `C¹` function with the divergence of a transverse test vector field.
-/

public section

open MeasureTheory TopologicalSpace TestFunction
open scoped Distributions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace TauCeti

/-- For a compactly supported `C¹` function `w`, the pairing of its line integrals with the
divergence of a transverse test vector field `φ` is `-∫_E Dw (φ ∘ π)`, written in orthogonal line
coordinates. -/
theorem integral_divergence_mul_integral_line_eq {w : E → ℝ} (hw : ContDiff ℝ 1 w)
    (hwc : HasCompactSupport w) (e : E) (he : ‖e‖ = 1) (φ : 𝓓(⊤, (ℝ ∙ e)ᗮ)) :
    ∫ y : (ℝ ∙ e)ᗮ, divergenceCLM φ y * ∫ t : ℝ, w ((y : E) + t • e) =
      -∫ p : (ℝ ∙ e)ᗮ × ℝ, fderiv ℝ w (orthogonalLineEquiv e he p) (φ p.1)
        ∂(volume.prod volume) := by
  have hL := measurePreserving_orthogonalLineEquiv e he
  obtain ⟨C, hC⟩ := (divergenceCLM φ).continuous.bounded_above_of_compact_support
    (divergenceCLM φ).hasCompactSupport
  obtain ⟨Cφ, hCφ⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hD : Continuous (fderiv ℝ w) := hw.continuous_fderiv one_ne_zero
  have hDint : Integrable (fun x => ‖fderiv ℝ w x‖) :=
    (hD.norm.integrable_of_hasCompactSupport (hwc.fderiv (𝕜 := ℝ)).norm)
  -- The integrand of the right side is integrable on the product.
  have hint : Integrable (fun p : (ℝ ∙ e)ᗮ × ℝ =>
      fderiv ℝ w (orthogonalLineEquiv e he p) (φ p.1)) (volume.prod volume) := by
    refine Integrable.mono' ((hL.integrable_comp_of_integrable hDint).mul_const Cφ)
      ((hD.comp (orthogonalLineEquiv e he).continuous).clm_apply
        ((continuous_subtype_val.comp φ.continuous).comp continuous_fst)).aestronglyMeasurable
      (.of_forall fun p => ?_)
    exact (fderiv ℝ w _).le_opNorm_of_le (by simpa using hCφ p.1)
  have hprod : Integrable (fun p : (ℝ ∙ e)ᗮ × ℝ =>
      divergenceCLM φ p.1 * w (orthogonalLineEquiv e he p)) (volume.prod volume) :=
    (hL.integrable_comp_of_integrable (hw.continuous.integrable_of_hasCompactSupport hwc)).bdd_mul
      ((divergenceCLM φ).continuous.comp continuous_fst).aestronglyMeasurable
      (.of_forall fun p => hC p.1)
  rw [integral_mul_integral_line_eq (hw.continuous.integrable_of_hasCompactSupport hwc) e he
    (divergenceCLM φ).continuous.aestronglyMeasurable hC, integral_prod_symm _ hprod,
    integral_prod_symm _ hint, ← integral_neg]
  refine integral_congr_ae (.of_forall fun t => ?_)
  -- On each hyperplane `t = const`, integrate by parts against the test field `φ`.
  have hshift : ContDiff ℝ 1 fun y : (ℝ ∙ e)ᗮ => (y : E) + t • e :=
    (ℝ ∙ e)ᗮ.subtypeL.contDiff.add contDiff_const
  have hweak : HasWeakFDerivOn volume ⊤ (fun y : (ℝ ∙ e)ᗮ => w ((y : E) + t • e))
      fun y => (fderiv ℝ w ((y : E) + t • e)).comp (ℝ ∙ e)ᗮ.subtypeL :=
    (hw.comp hshift).locallyLipschitz.locallyLipschitzOn.hasWeakFDerivOn
      (.of_forall fun y _ => ((hw.differentiable one_ne_zero _).hasFDerivAt).comp y
        ((ℝ ∙ e)ᗮ.subtypeL.hasFDerivAt.add_const _))
  simpa [orthogonalLineEquiv_apply, smul_eq_mul] using
    hweak.integral_divergenceCLM_smul_eq_neg_integral φ

end TauCeti
