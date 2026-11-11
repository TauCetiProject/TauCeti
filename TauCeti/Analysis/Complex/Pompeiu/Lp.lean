/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Basic
public import TauCeti.Analysis.Complex.CauchyKernel
public import TauCeti.MeasureTheory.Function.Lp.Operator.Integral.Basic
import TauCeti.MeasureTheory.Integral.SchurTest
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The Cauchy transform on fixed input and output discs

The normalization `TauCeti.cauchyTransform f w = π⁻¹ ∫ z, (w - z)⁻¹ • f z` corresponds to
`bar∂ = (∂ₛ + i ∂ₜ) / 2`. For input supported in the closed disc of radius `r` about `c`, the
transform belongs to `Lᵖ` on the output disc of radius `R`, for every `1 ≤ p ≤ ∞`.
The operator `TauCeti.cauchyTransformLp` has norm at most `2 * (r + R)`.

The proof applies the existing operator-valued Schur test. Integrating the reciprocal kernel over
the input or output disc gives the common bound `2π(r + R)` before normalization. The result
controls the function term on bounded discs; no global `Lᵖ` bound for the transform is asserted.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.2 (Cauchy–Riemann estimates).
* G. B. Folland, *Real Analysis*, second edition, Theorem 6.18 (integral operator bounds).
* t4v1/damian_formalizare, `MorseFloer/Part2/CauchyPompeiu.lean` and `CauchyHolder.lean`,
  revision `545ebb1a7d4c55299b1f59787a7ff0d4d703af27` (an independent Cauchy/Beurling
  Hölder-scale development). Its `dbar` and `dz` are twice the Wirtinger derivatives here;
  its Cauchy transform has factor `(2π)⁻¹`. After the change of variables `z = w - ξ`,
  `cauchyTransform` here is twice that transform. Its unnormalized Beurling integral becomes
  `∂ cauchyTransform` after multiplication by `-π⁻¹`. This file imports no code from that project.
-/

public noncomputable section

open MeasureTheory Metric Set Function Filter
open scoped ENNReal NNReal Real Topology Convolution

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

private def cauchyKernelL (w z : ℂ) : F →L[ℂ] F :=
  ((Real.pi : ℂ)⁻¹ * (w - z)⁻¹) • ContinuousLinearMap.id ℂ F

private theorem cauchyKernelL_apply (w z : ℂ) (v : F) :
    cauchyKernelL w z v = (Real.pi : ℂ)⁻¹ • ((w - z)⁻¹ • v) := by
  simp only [cauchyKernelL, smul_apply, ContinuousLinearMap.id_apply,
    smul_smul]

private theorem stronglyMeasurable_cauchyKernelL :
    StronglyMeasurable (uncurry (cauchyKernelL (F := F))) := by
  have h : StronglyMeasurable (fun q : ℂ × ℂ ↦ (Real.pi : ℂ)⁻¹ * (q.1 - q.2)⁻¹) :=
    ((measurable_fst.sub measurable_snd).inv.const_mul _).stronglyMeasurable
  exact h.smul stronglyMeasurable_const

private theorem integrableOn_cauchyKernelL (c w : ℂ) (r : ℝ≥0) :
    IntegrableOn (cauchyKernelL (F := F) w) (closedBall c r) := by
  have h := (Complex.locallyIntegrable_sub_inv w).integrableOn_isCompact
    (isCompact_closedBall c (r : ℝ))
  exact (h.const_mul (Real.pi : ℂ)⁻¹).smul_const (ContinuousLinearMap.id ℂ F)

private theorem norm_cauchyKernelL_le (w z : ℂ) :
    ‖cauchyKernelL (F := F) w z‖ ≤ Real.pi⁻¹ * ‖z - w‖⁻¹ := by
  calc ‖cauchyKernelL (F := F) w z‖
      ≤ ‖(Real.pi : ℂ)⁻¹ * (w - z)⁻¹‖ * 1 := by
        rw [cauchyKernelL, norm_smul]
        gcongr
        exact ContinuousLinearMap.norm_id_le
    _ = Real.pi⁻¹ * ‖z - w‖⁻¹ := by
      simp only [norm_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le, norm_sub_rev, mul_one]

private theorem norm_cauchyKernelL_swap (w z : ℂ) :
    ‖cauchyKernelL (F := F) w z‖ = ‖cauchyKernelL (F := F) z w‖ := by
  simp only [cauchyKernelL, norm_smul, norm_mul, norm_inv, norm_sub_rev]

private theorem lintegral_cauchyKernelL_le {c w : ℂ} (r R : ℝ≥0)
    (hw : w ∈ closedBall c (R : ℝ)) :
    ∫⁻ z, ‖cauchyKernelL (F := F) w z‖ₑ ∂(volume.restrict (closedBall c r)) ≤
      (2 * (r + R) : ℝ≥0) := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm (integrableOn_cauchyKernelL c w r),
    ← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  have hi := (Complex.locallyIntegrable_sub_inv w).integrableOn_isCompact
    (isCompact_closedBall c (r : ℝ))
  calc (∫ z in closedBall c (r : ℝ), ‖cauchyKernelL (F := F) w z‖)
      ≤ ∫ z in closedBall c (r : ℝ), Real.pi⁻¹ * ‖z - w‖⁻¹ := by
        apply integral_mono_ae (integrableOn_cauchyKernelL c w r).norm
          (by simpa only [norm_inv, norm_sub_rev] using hi.norm.const_mul Real.pi⁻¹)
        exact Eventually.of_forall fun z ↦ norm_cauchyKernelL_le w z
    _ = Real.pi⁻¹ * ∫ z in closedBall c (r : ℝ), ‖z - w‖⁻¹ := integral_const_mul _ _
    _ ≤ Real.pi⁻¹ * (2 * Real.pi * ((r : ℝ) + R)) := by
        gcongr
        exact integral_norm_sub_inv_closedBall_le_add r.2 hw
    _ = (2 * (r + R) : ℝ≥0) := by
        push_cast
        field_simp

private theorem cauchyKernelL_row (c : ℂ) (r R : ℝ≥0) :
    ∀ᵐ w ∂(volume.restrict (closedBall c (R : ℝ))),
      ∫⁻ z, ‖cauchyKernelL (F := F) w z‖ₑ ∂(volume.restrict (closedBall c (r : ℝ))) ≤
        (2 * (r + R) : ℝ≥0) :=
  (ae_restrict_mem measurableSet_closedBall).mono fun _ hw ↦ lintegral_cauchyKernelL_le r R hw

private theorem cauchyKernelL_column (c : ℂ) (r R : ℝ≥0) :
    ∀ᵐ z ∂(volume.restrict (closedBall c (r : ℝ))),
      ∫⁻ w, ‖cauchyKernelL (F := F) w z‖ₑ ∂(volume.restrict (closedBall c (R : ℝ))) ≤
        (2 * (r + R) : ℝ≥0) := by
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
  calc (∫⁻ w, ‖cauchyKernelL (F := F) w z‖ₑ ∂(volume.restrict (closedBall c (R : ℝ))))
      = ∫⁻ w, ‖cauchyKernelL (F := F) z w‖ₑ ∂(volume.restrict (closedBall c (R : ℝ))) := by
        apply lintegral_congr
        intro w
        simpa only [ofReal_norm] using
          congrArg ENNReal.ofReal (norm_cauchyKernelL_swap (F := F) w z)
    _ ≤ (2 * (r + R) : ℝ≥0) := by
        simpa only [add_comm] using lintegral_cauchyKernelL_le (F := F) R r hz

/-- The Cauchy transform from `Lᵖ` on the input disc of radius `r` to `Lᵖ` on the output disc of
radius `R`, both centred at `c`. The source is integrated only over its input disc. -/
def cauchyTransformLp (c : ℂ) (r R : ℝ≥0) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp F p (volume.restrict (closedBall c (r : ℝ))) →L[ℂ]
      Lp F p (volume.restrict (closedBall c (R : ℝ))) :=
  integralOperatorLp (cauchyKernelL (F := F)) p
    stronglyMeasurable_cauchyKernelL.aestronglyMeasurable
    (cauchyKernelL_row c r R) (cauchyKernelL_column c r R)

/-- The fixed-disc Cauchy operator has norm at most twice the sum of the input and output radii.
The estimate includes `p = 1` and `p = ∞`. -/
theorem norm_cauchyTransformLp_le (c : ℂ) (r R : ℝ≥0) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ‖cauchyTransformLp (F := F) c r R p‖ ≤ 2 * ((r : ℝ) + R) := by
  simpa only [cauchyTransformLp, max_self, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat]
    using (norm_integralOperatorLp_le_max (K := cauchyKernelL (F := F))
      (hK := stronglyMeasurable_cauchyKernelL.aestronglyMeasurable)
      (hA := cauchyKernelL_row c r R) (hB := cauchyKernelL_column c r R) (p := p))

/-- On representatives the bounded Cauchy operator acts by the normalized integral over the
input disc, almost everywhere on the output disc. -/
theorem coeFn_cauchyTransformLp (c : ℂ) (r R : ℝ≥0) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Lp F p (volume.restrict (closedBall c (r : ℝ)))) :
    cauchyTransformLp c r R p u =ᵐ[volume.restrict (closedBall c (R : ℝ))]
      fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z in closedBall c (r : ℝ), (w - z)⁻¹ • u z := by
  refine (coeFn_integralOperatorLp u).trans (.of_forall fun w ↦ ?_)
  simp only [cauchyKernelL_apply, integral_smul]

private theorem cauchyTransform_eq_kernel_integral {f : ℂ → F} {c : ℂ} {r : ℝ≥0}
    (hs : support f ⊆ closedBall c (r : ℝ)) :
    cauchyTransform f = fun w ↦ ∫ z in closedBall c (r : ℝ), cauchyKernelL w z (f z) := by
  funext w
  simp only [cauchyTransform_eq_integral_closedBall hs, cauchyKernelL_apply, integral_smul]

/-- The Cauchy transform of compactly supported `Lᵖ` data belongs to `Lᵖ` on each output disc,
including the endpoints `p = 1` and `p = ∞`. -/
theorem memLp_cauchyTransform {f : ℂ → F} {c : ℂ} {r R : ℝ≥0} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hf : MemLp f p (volume.restrict (closedBall c (r : ℝ))))
    (hs : support f ⊆ closedBall c (r : ℝ)) :
    MemLp (cauchyTransform f) p (volume.restrict (closedBall c (R : ℝ))) := by
  have h := memLp_integral_apply (K := cauchyKernelL (F := F))
    stronglyMeasurable_cauchyKernelL.aestronglyMeasurable hf hp
    (cauchyKernelL_row c r R) (cauchyKernelL_column c r R)
  rw [cauchyTransform_eq_kernel_integral hs]
  exact h

/-- The fixed-support function bound, with input and output radii explicit. It controls only the
output disc, and includes every exponent from one through infinity. -/
theorem eLpNorm_cauchyTransform_le {f : ℂ → F} {c : ℂ} {r R : ℝ≥0} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hf : AEStronglyMeasurable f (volume.restrict (closedBall c (r : ℝ))))
    (hs : support f ⊆ closedBall c (r : ℝ)) :
    eLpNorm (cauchyTransform f) p (volume.restrict (closedBall c (R : ℝ))) ≤
      (2 * (r + R) : ℝ≥0) * eLpNorm f p (volume.restrict (closedBall c (r : ℝ))) := by
  have h := eLpNorm_integral_apply_le (K := cauchyKernelL (F := F))
    stronglyMeasurable_cauchyKernelL.aestronglyMeasurable hf hp
    (cauchyKernelL_row c r R) (cauchyKernelL_column c r R)
  rw [← coe_rpow_one_sub_toReal_inv_mul_rpow_toReal_inv hp,
    ← NNReal.rpow_add' (by simp), sub_add_cancel, NNReal.rpow_one] at h
  rw [cauchyTransform_eq_kernel_integral hs]
  exact h

/-- For fixed-support `Lᵖ` data the Cauchy integral is integrable at almost every output point. -/
theorem ae_integrable_cauchyTransform {f : ℂ → F} {c : ℂ} {r R : ℝ≥0} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hf : MemLp f p (volume.restrict (closedBall c (r : ℝ))))
    (hs : support f ⊆ closedBall c (r : ℝ)) :
    ∀ᵐ w ∂(volume.restrict (closedBall c (R : ℝ))),
      Integrable (fun z ↦ (w - z)⁻¹ • f z) volume := by
  filter_upwards [ae_integrable_apply_of_memLp
    (K := cauchyKernelL (F := F)) stronglyMeasurable_cauchyKernelL.aestronglyMeasurable hf hp
    (cauchyKernelL_row c r R) (cauchyKernelL_column c r R)] with w hw
  have hw' : Integrable (fun z ↦ cauchyKernelL w z (f z))
      (volume.restrict (closedBall c (r : ℝ))) := hw
  have hi : IntegrableOn (fun z ↦ (w - z)⁻¹ • f z) (closedBall c (r : ℝ)) := by
    have heq : (Real.pi : ℂ) • (fun z ↦ cauchyKernelL w z (f z)) =
        fun z ↦ (w - z)⁻¹ • f z := by
      funext z
      rw [Pi.smul_apply, cauchyKernelL_apply, smul_smul,
        mul_inv_cancel₀ (by exact_mod_cast Real.pi_ne_zero), one_smul]
    exact heq ▸ hw'.smul (Real.pi : ℂ)
  exact hi.integrable_of_forall_notMem_eq_zero fun z hz ↦ by
    rw [notMem_support.mp (fun h ↦ hz (hs h)), smul_zero]

end TauCeti
