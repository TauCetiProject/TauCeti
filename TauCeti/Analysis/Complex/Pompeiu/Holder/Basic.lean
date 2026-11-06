/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Basic
public import TauCeti.Analysis.Complex.CauchyKernel
public import TauCeti.Analysis.Convolution.Holder
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Topology.MetricSpace.Holder
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Hölder bounds for the planar Cauchy transform

The input support and output disc are fixed separately. Truncating the reciprocal kernel at the
sum of their radii preserves the actual Cauchy integral and yields bounds in the Hölder norm.
The normalization is `π⁻¹`, with conjugate Wirtinger operator
`(2 : ℂ)⁻¹ • (D f 1 + I • D f I)`, where `D f` is the real Fréchet derivative.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix B.
* The Cauchy/Beurling Hölder development in `t4v1/damian_formalizare`,
  `MorseFloer/Part2/CauchyPompeiu.lean` and `CauchyHolder.lean`, uses a Cauchy transform with
  normalization `(2π)⁻¹` for twice the conjugate Wirtinger derivative. The normalization here
  is twice that transform.
-/

public noncomputable section

open MeasureTheory Metric Set Complex
open scoped NNReal

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {f : ℂ → F} {c w : ℂ} {r R : ℝ}

private lemma truncatedCauchyKernel_smul_eq
    (hs : Function.support f ⊆ closedBall c r) (hw : w ∈ closedBall c R) (z : ℂ) :
    truncatedCauchyKernel (r + R) z • f (w - z) = z⁻¹ • f (w - z) := by
  simpa only [truncatedCauchyKernel_def] using
    (indicator_kernel_smul_sub_eq (K := fun z : ℂ ↦ z⁻¹) hs hw z)

/-- On a fixed output disc, cutting the reciprocal off at the sum of the input and output
radii preserves the actual Cauchy integral. -/
theorem integral_sub_inv_smul_eq_truncatedCauchyKernel_smul
    (hs : Function.support f ⊆ closedBall c r) (hw : w ∈ closedBall c R) :
    (∫ z, (w - z)⁻¹ • f z) = ∫ z, truncatedCauchyKernel (r + R) z • f (w - z) := by
  have h := integral_sub_left_eq_self (fun z : ℂ ↦ (w - z)⁻¹ • f z) volume w
  simp only [sub_sub_cancel] at h
  rw [← h]
  apply integral_congr_ae
  exact ae_of_all _ fun z ↦ (truncatedCauchyKernel_smul_eq hs hw z).symm

/-- The normalized Cauchy transform has a fixed-disc supremum bound `2(r+R) M` whenever the
source is supported in the input disc and bounded by `M`. -/
theorem norm_pi_inv_smul_integral_sub_inv_smul_le
    (hr : 0 ≤ r) (hR : 0 ≤ R) (hs : Function.support f ⊆ closedBall c r)
    {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) (hw : w ∈ closedBall c R) :
    ‖(Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z‖ ≤ 2 * (r + R) * M := by
  rw [integral_sub_inv_smul_eq_truncatedCauchyKernel_smul hs hw, norm_smul]
  have hb := norm_integral_kernel_smul_sub_le
    (integrable_truncatedCauchyKernel (r + R)) hM w
  rw [integral_norm_truncatedCauchyKernel (add_nonneg hr hR)] at hb
  calc
    _ ≤ ‖(Real.pi : ℂ)⁻¹‖ * ((2 * Real.pi * (r + R)) * M) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := by
      simp only [norm_inv, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      field_simp

/-- On a fixed output disc the normalized Cauchy transform preserves the Hölder exponent,
with the function-term bound `2(r+R)` and no loss in the exponent. -/
theorem holderOnWith_pi_inv_smul_integral_sub_inv_smul
    {H α : ℝ≥0} (hα : 0 < α) (hf : HolderWith H α f)
    (hr : 0 ≤ r) (hR : 0 ≤ R) (hs : Function.support f ⊆ closedBall c r) :
    HolderOnWith ((2 * (r + R)).toNNReal * H) α
      (fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z) (closedBall c R) := by
  have hc := HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c r) hs
  have hf' := hf.continuous hα
  obtain ⟨M, hM⟩ := hf'.bounded_above_of_compact_support hc
  have h := (holderWith_integral_kernel_smul_sub
    (integrable_truncatedCauchyKernel (r + R)) hα hf hM)
  have hscaled := (h.smul ((Real.pi : ℂ)⁻¹)).holderOnWith (closedBall c R)
  have hconst : ((∫ z, ‖truncatedCauchyKernel (r + R) z‖).toNNReal * H) *
      ‖(Real.pi : ℂ)⁻¹‖₊ =
        (2 * (r + R)).toNNReal * H := by
    apply NNReal.eq
    rw [integral_norm_truncatedCauchyKernel (add_nonneg hr hR)]
    simp only [NNReal.coe_mul, coe_nnnorm]
    rw [
      Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity)]
    simp only [norm_inv, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    field_simp
  rw [hconst] at hscaled
  intro w hw v hv
  dsimp only
  rw [integral_sub_inv_smul_eq_truncatedCauchyKernel_smul hs hw,
    integral_sub_inv_smul_eq_truncatedCauchyKernel_smul hs hv]
  exact hscaled w hw v hv

/-- Uniformly bounded pointwise convergence on one fixed support disc passes through the
actual normalized Cauchy integral, including when the limiting source is only continuous. -/
theorem tendsto_pi_inv_smul_integral_sub_inv_smul
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {g : ι → ℂ → F} {M : ℝ}
    (hg : ∀ i, Continuous (g i)) (hgs : ∀ i, Function.support (g i) ⊆ closedBall c r)
    (hfs : Function.support f ⊆ closedBall c r) (hM : ∀ i z, ‖g i z‖ ≤ M)
    (hlim : ∀ z, Filter.Tendsto (fun i ↦ g i z) l (nhds (f z))) (w : ℂ) :
    Filter.Tendsto (fun i ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • g i z) l
      (nhds ((Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z)) := by
  let ρ := r + dist w c
  have hw : w ∈ closedBall c (dist w c) := mem_closedBall.mpr le_rfl
  have hi := tendsto_integral_filter_of_dominated_convergence
    (F := fun i z ↦ truncatedCauchyKernel ρ z • g i (w - z))
    (fun z ↦ ‖truncatedCauchyKernel ρ z‖ * M)
    (Filter.Eventually.of_forall fun i ↦
      (measurable_truncatedCauchyKernel ρ).aestronglyMeasurable.smul
        (((hg i).comp (continuous_const.sub continuous_id)).aestronglyMeasurable))
    (Filter.Eventually.of_forall fun i ↦ ae_of_all _ fun z ↦ by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hM i _) (norm_nonneg _))
    ((integrable_truncatedCauchyKernel ρ).norm.mul_const M)
    (ae_of_all _ fun z ↦ (hlim (w - z)).const_smul (truncatedCauchyKernel ρ z))
  have hi' := hi.const_smul ((Real.pi : ℂ)⁻¹)
  convert hi' using 1
  · funext i
    rw [integral_sub_inv_smul_eq_truncatedCauchyKernel_smul (hgs i) hw]
  · rw [integral_sub_inv_smul_eq_truncatedCauchyKernel_smul hfs hw]

end TauCeti
