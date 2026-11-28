/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import TauCeti.Analysis.SpecialFunctions.Log.MaxDiv
import TauCeti.Analysis.Convex.Integral

/-!
# Integrating bounded continuous functions against an integrable weight

On a space `α` with a measure `μ`, where `α` or `F` is second-countable, a bounded continuous
function `u : α →ᵇ F` times an integrable scalar weight `w` is integrable, and the integral
`∫ w • u ∂μ` depends Lipschitz continuously on `u` for the supremum norm, with constant
`∫ ‖w‖ ∂μ` (`MeasureTheory.Integrable.lipschitzWith_integral_smul`). The space need not
be compact, and the measure need not be finite. This is what lets an integral identity against a
fixed weight pass to uniform limits, for instance from smooth functions to all bounded uniformly
continuous ones in a distributional identity tested against a compactly supported function.

Integration against `w` is then a continuous linear functional `u ↦ ∫ w • u ∂μ` on
`α →ᵇ F` (`BoundedContinuousFunction.integralSMulCLM`), of norm at most `∫ ‖w‖ ∂μ`
(`BoundedContinuousFunction.norm_integralSMulCLM_le`).

For any `f : Ω →ᵇ E`, threshold `δ`, and integrable real weight `w`, the truncated norm product
`s ↦ max ‖f s‖ δ * w s` is integrable (`BoundedContinuousFunction.integrable_max_norm_mul`), and
when `δ ≥ 0`, `w ≥ 0` a.e., and `∫ w ∂μ = α`,
`α⁻¹ * ∫ s, max ‖f s‖ δ * w s ∂μ ≤ α⁻¹ * (∫ s, ‖f s‖ * w s ∂μ) + δ`
(`BoundedContinuousFunction.inv_mul_integral_max_le`).

For `δ > 0`, this file also records the weighted integrable-envelope bounds for `TauCeti.logMaxDiv`:
* `BoundedContinuousFunction.integrable_logMaxDiv_mul`: `(TauCeti.logMaxDiv f δ ·) * w` is
  `μ`-integrable for any `μ`-integrable `w`;
* `BoundedContinuousFunction.integral_log_max_mul_eq`:
  `∫ Real.log (max ‖f s‖ δ) * w s ∂μ =`
  `(∫ Real.log δ * w s ∂μ) + (∫ TauCeti.logMaxDiv f δ s * w s ∂μ)`;
* `BoundedContinuousFunction.inv_mul_integral_log_max_le`:
  `α⁻¹ * ∫ Real.log (max ‖f s‖ δ) * w s ∂μ ≤ Real.log (α⁻¹ * ∫ max ‖f s‖ δ * w s ∂μ)`;
* `BoundedContinuousFunction.exp_integral_log_max_le_rpow`:
  `Real.exp (∫ Real.log (max ‖f s‖ δ) * w s ∂μ) ≤ (α⁻¹ * ∫ ‖f s‖ * w s ∂μ + δ) ^ α`.
-/

public section

namespace MeasureTheory

open scoped BoundedContinuousFunction

variable {α 𝕜 F : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
  {μ : Measure α} [NormedRing 𝕜] [NormedAddCommGroup F] [SecondCountableTopologyEither α F]
  [Module 𝕜 F] [IsBoundedSMul 𝕜 F] {w : α → 𝕜}

/-- A bounded continuous function times an integrable scalar weight is integrable. -/
theorem _root_.BoundedContinuousFunction.integrable_smul (u : α →ᵇ F) (hw : Integrable w μ) :
    Integrable (fun x ↦ w x • u x) μ :=
  hw.smul_of_top_left (memLp_top_of_bound u.continuous.aestronglyMeasurable ‖u‖
    (ae_of_all _ u.norm_coe_le_norm))

variable [NormedSpace ℝ F]

/-- **Integration against an integrable weight is Lipschitz in the supremum norm.** For an
integrable scalar weight `w`, the map `u ↦ ∫ w • u ∂μ` on bounded continuous functions is
Lipschitz with constant `∫ ‖w‖ ∂μ`. -/
theorem Integrable.lipschitzWith_integral_smul (hw : Integrable w μ) :
    LipschitzWith (∫ x, ‖w x‖ ∂μ).toNNReal fun u : α →ᵇ F ↦ ∫ x, w x • u x ∂μ := by
  refine LipschitzWith.of_dist_le_mul fun u v ↦ ?_
  rw [dist_eq_norm, ← integral_sub (u.integrable_smul hw) (v.integrable_smul hw), dist_eq_norm,
    Real.coe_toNNReal _ (integral_nonneg fun _ ↦ norm_nonneg _), ← integral_mul_const]
  refine norm_integral_le_of_norm_le (hw.norm.mul_const _) (ae_of_all _ fun x ↦ ?_)
  rw [← smul_sub]
  exact (norm_smul_le _ _).trans
    (mul_le_mul_of_nonneg_left ((u - v).norm_coe_le_norm x) (norm_nonneg _))

/-- Integration against an integrable weight is continuous in the supremum norm. -/
theorem Integrable.continuous_integral_smul (hw : Integrable w μ) :
    Continuous fun u : α →ᵇ F ↦ ∫ x, w x • u x ∂μ :=
  hw.lipschitzWith_integral_smul.continuous

variable [SMulCommClass 𝕜 ℝ F]

/-- Integration against an integrable scalar weight `w`, as the continuous linear map
`u ↦ ∫ w • u ∂μ` on bounded continuous functions, of norm at most `∫ ‖w‖ ∂μ`. -/
noncomputable def _root_.BoundedContinuousFunction.integralSMulCLM (hw : Integrable w μ) :
    (α →ᵇ F) →L[ℝ] F :=
  LinearMap.mkContinuous
    { toFun u := ∫ x, w x • u x ∂μ
      map_add' u v := by
        simp only [add_apply, smul_add]
        exact integral_add (u.integrable_smul hw) (v.integrable_smul hw)
      map_smul' c u := by
        simp only [smul_apply, smul_comm (w _) c, integral_smul, RingHom.id_apply] }
    (∫ x, ‖w x‖ ∂μ) fun u ↦ by
      simpa [Real.coe_toNNReal _ (integral_nonneg fun _ ↦ norm_nonneg _)] using
        hw.lipschitzWith_integral_smul.dist_le_mul u 0

/-- `integralSMulCLM hw` integrates `u` against the weight `w`. -/
@[simp]
theorem _root_.BoundedContinuousFunction.integralSMulCLM_apply (hw : Integrable w μ)
    (u : α →ᵇ F) : BoundedContinuousFunction.integralSMulCLM hw u = ∫ x, w x • u x ∂μ := by
  rfl

/-- The operator norm of integration against `w` is at most the `L¹` norm `∫ ‖w‖` of `w`. -/
theorem _root_.BoundedContinuousFunction.norm_integralSMulCLM_le (hw : Integrable w μ) :
    ‖(BoundedContinuousFunction.integralSMulCLM hw : (α →ᵇ F) →L[ℝ] F)‖ ≤ ∫ x, ‖w x‖ ∂μ :=
  LinearMap.mkContinuous_norm_le _ (integral_nonneg fun _ ↦ norm_nonneg _) _

end MeasureTheory

namespace BoundedContinuousFunction

open MeasureTheory

/-- For a bounded continuous function `f : Ω →ᵇ E`, any threshold `δ : ℝ`, and an integrable
weight `w`, `s ↦ max ‖f s‖ δ * w s` is integrable. -/
theorem integrable_max_norm_mul {Ω E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} [SeminormedAddCommGroup E] (f : Ω →ᵇ E) (δ : ℝ)
    {w : Ω → ℝ} (hw_int : Integrable w μ) : Integrable (fun s ↦ max ‖f s‖ δ * w s) μ :=
  hw_int.bdd_mul (f.continuous.norm.max continuous_const).aestronglyMeasurable
    (ae_of_all _ fun s ↦ Real.norm_of_nonneg ((norm_nonneg (f s)).trans (le_max_left _ _)) ▸
      max_le_max (f.norm_coe_le_norm s) le_rfl)

/-- For a bounded continuous function `f : Ω →ᵇ E`, threshold `δ ≥ 0`, and an almost everywhere
nonnegative integrable weight `w` of total mass `∫ s, w s ∂μ = α`,
`α⁻¹ * ∫ s, max ‖f s‖ δ * w s ∂μ ≤ α⁻¹ * (∫ s, ‖f s‖ * w s ∂μ) + δ`. -/
theorem inv_mul_integral_max_le {Ω E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} [SeminormedAddCommGroup E] (f : Ω →ᵇ E)
    {w : Ω → ℝ} {α δ : ℝ} (hδ : 0 ≤ δ) (hw_int : Integrable w μ)
    (hw_nonneg : 0 ≤ᵐ[μ] w) (hw_sum : ∫ s, w s ∂μ = α) :
    α⁻¹ * ∫ s, max ‖f s‖ δ * w s ∂μ ≤ α⁻¹ * (∫ s, ‖f s‖ * w s ∂μ) + δ := by
  rcases eq_or_lt_of_le (hw_sum ▸ integral_nonneg_of_ae hw_nonneg) with rfl | hα
  · simpa using hδ
  · have hf_int : Integrable (fun s ↦ ‖f s‖ * w s) μ := hw_int.bdd_mul
      f.continuous.norm.aestronglyMeasurable
      (ae_of_all _ fun s ↦ norm_norm (f s) ▸ f.norm_coe_le_norm s)
    have hint : ∫ s, max ‖f s‖ δ * w s ∂μ ≤ (∫ s, ‖f s‖ * w s ∂μ) + δ * α :=
      (integral_mono_ae (f.integrable_max_norm_mul δ hw_int) (hf_int.add (hw_int.const_mul δ))
        (hw_nonneg.mono fun s hs ↦ by
          rw [Pi.add_apply, ← add_mul]; exact mul_le_mul_of_nonneg_right (max_le
            (le_add_of_nonneg_right hδ) (le_add_of_nonneg_left (norm_nonneg _))) hs)).trans_eq
        (by simp [integral_add hf_int (hw_int.const_mul δ), integral_const_mul, hw_sum])
    refine (mul_le_mul_of_nonneg_left hint (inv_pos.2 hα).le).trans_eq ?_
    rw [mul_add, mul_left_comm, inv_mul_cancel₀ hα.ne', mul_one]

/-- For `f : Ω →ᵇ E`, `δ > 0`, and an integrable weight `w`, `(TauCeti.logMaxDiv f δ ·) * w` is
integrable. -/
theorem integrable_logMaxDiv_mul {Ω E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} [SeminormedAddCommGroup E] (f : Ω →ᵇ E) {δ : ℝ}
    (hδ : 0 < δ) {w : Ω → ℝ} (hw_int : Integrable w μ) :
    Integrable (fun s ↦ TauCeti.logMaxDiv f δ s * w s) μ :=
  hw_int.bdd_mul (c := Real.log (max ‖f‖ δ / δ))
    (TauCeti.continuous_logMaxDiv f.continuous hδ).aestronglyMeasurable (ae_of_all _ fun s ↦ by
      rw [Real.norm_of_nonneg (TauCeti.logMaxDiv_nonneg f hδ s), TauCeti.logMaxDiv_def]
      exact Real.log_le_log (div_pos (hδ.trans_le (le_max_right _ _)) hδ)
        (div_le_div_of_nonneg_right (max_le_max (f.norm_coe_le_norm s) le_rfl) hδ.le))

/-- Splitting identity for a clipped weighted logarithmic integral of `f : Ω →ᵇ E` with threshold
`δ > 0` and integrable weight `w`:
`∫ Real.log (max ‖f s‖ δ) * w s ∂μ =`
`(∫ Real.log δ * w s ∂μ) + (∫ TauCeti.logMaxDiv f δ s * w s ∂μ)`. -/
theorem integral_log_max_mul_eq {Ω E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} [SeminormedAddCommGroup E] (f : Ω →ᵇ E) {δ : ℝ}
    (hδ : 0 < δ) {w : Ω → ℝ} (hw_int : Integrable w μ) : (∫ s, Real.log (max ‖f s‖ δ) * w s ∂μ) =
      (∫ s, Real.log δ * w s ∂μ) + (∫ s, TauCeti.logMaxDiv f δ s * w s ∂μ) := by
  rw [show (fun s ↦ Real.log (max ‖f s‖ δ) * w s) =
      fun s ↦ Real.log δ * w s + TauCeti.logMaxDiv f δ s * w s from
      funext fun s ↦ by rw [← add_mul, TauCeti.log_add_logMaxDiv f hδ],
    integral_add (hw_int.const_mul _) (f.integrable_logMaxDiv_mul hδ hw_int)]

/-- Weighted logarithmic Jensen inequality for a clipped bounded continuous function `f : Ω →ᵇ E`:
for `δ > 0` and an almost everywhere nonnegative integrable weight `w` of total mass
`∫ w ∂μ = α > 0`,
`α⁻¹ * ∫ Real.log (max ‖f s‖ δ) * w s ∂μ ≤ Real.log (α⁻¹ * ∫ max ‖f s‖ δ * w s ∂μ)`. -/
theorem inv_mul_integral_log_max_le {Ω E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} [SeminormedAddCommGroup E] (f : Ω →ᵇ E)
    {w : Ω → ℝ} {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) (hw_int : Integrable w μ)
    (hw_nonneg : 0 ≤ᵐ[μ] w) (hw_sum : ∫ s, w s ∂μ = α) :
    α⁻¹ * ∫ s, Real.log (max ‖f s‖ δ) * w s ∂μ ≤ Real.log (α⁻¹ * ∫ s, max ‖f s‖ δ * w s ∂μ) :=
  MeasureTheory.inv_mul_integral_log_mul_le hα (ae_of_all _ fun _ ↦ hδ.trans_le (le_max_right _ _))
    hw_int hw_nonneg hw_sum (f.integrable_max_norm_mul δ hw_int)
    (((hw_int.const_mul (Real.log δ)).add (f.integrable_logMaxDiv_mul hδ hw_int)).congr
      (ae_of_all _ fun s ↦ by rw [Pi.add_apply, ← add_mul, TauCeti.log_add_logMaxDiv f hδ]))

/-- Weighted logarithmic mean bound for a clipped bounded continuous function `f : Ω →ᵇ E`: for a
threshold `δ > 0` and an almost everywhere nonnegative integrable weight `w` of total mass
`∫ w ∂μ = α > 0`, `exp (∫ Real.log (max ‖f s‖ δ) * w s ∂μ) ≤ (α⁻¹ * ∫ ‖f s‖ * w s ∂μ + δ) ^ α`. -/
theorem exp_integral_log_max_le_rpow {Ω E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} [SeminormedAddCommGroup E] (f : Ω →ᵇ E)
    {w : Ω → ℝ} {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) (hw_int : Integrable w μ)
    (hw_nonneg : 0 ≤ᵐ[μ] w) (hw_sum : ∫ s, w s ∂μ = α) :
    Real.exp (∫ s, Real.log (max ‖f s‖ δ) * w s ∂μ) ≤ (α⁻¹ * (∫ s, ‖f s‖ * w s ∂μ) + δ) ^ α := by
  have hjensen := f.inv_mul_integral_log_max_le hα hδ hw_int hw_nonneg hw_sum
  have hmax_pos : 0 < α⁻¹ * ∫ s, max ‖f s‖ δ * w s ∂μ := hδ.trans_le <| by
    rw [le_inv_mul_iff₀ hα, mul_comm α δ, ← hw_sum, ← integral_const_mul]
    exact integral_mono_ae (hw_int.const_mul δ) (f.integrable_max_norm_mul δ hw_int)
      (hw_nonneg.mono fun _ hs ↦ mul_le_mul_of_nonneg_right (le_max_right _ _) hs)
  refine ((Real.exp_le_exp.2 ((inv_mul_le_iff₀ hα).1 hjensen)).trans_eq
    (by rw [Real.rpow_def_of_pos hmax_pos, mul_comm α])).trans
    (Real.rpow_le_rpow hmax_pos.le (f.inv_mul_integral_max_le hδ.le hw_int hw_nonneg hw_sum) hα.le)

end BoundedContinuousFunction
