/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Bochner.PiLp
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic
import TauCeti.Analysis.Normed.Lp.PiLp.Basic

/-!
# Weighted `PiLp` integrals of functions vanishing at infinity

Specializing `TauCeti.norm_toLp_integral_le` to coordinate norms of a map `f : C₀(Ω, PiLp p β)`
and an almost everywhere nonnegative integrable weight `w` of total mass `∫ w ∂μ = α > 0` yields
`‖WithLp.toLp p (fun i ↦ α⁻¹ * ∫ t, ‖f t i‖ * w t ∂μ)‖ ≤ ‖f‖`
(`ZeroAtInftyContinuousMap.norm_toLp_integral_weighted_le`).
-/

public section

open MeasureTheory
open scoped ENNReal ZeroAtInfty

namespace ZeroAtInftyContinuousMap

/-- Weighted integral norm bound in `PiLp`: for `f : C₀(Ω, PiLp p β)` with `1 ≤ p ≤ ∞` and
normed additive commutative group fibers `β i`, and an almost everywhere nonnegative integrable
weight `w` of total mass `∫ w ∂μ = α > 0`, `‖toLp p (i ↦ α⁻¹ * ∫ ‖f t i‖ * w t ∂μ)‖ ≤ ‖f‖`. -/
theorem norm_toLp_integral_weighted_le {Ω ι : Type*} [Fintype ι] [TopologicalSpace Ω]
    [MeasurableSpace Ω] [OpensMeasurableSpace Ω] {μ : Measure Ω} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {β : ι → Type*} [∀ i, NormedAddCommGroup (β i)] (f : C₀(Ω, PiLp p β)) {w : Ω → ℝ} {α : ℝ}
    (hα : 0 < α) (hw_int : Integrable w μ) (hw_nonneg : 0 ≤ᵐ[μ] w)
    (hw_sum : ∫ t, w t ∂μ = α) :
    ‖WithLp.toLp p (fun i ↦ α⁻¹ * ∫ t, ‖f t i‖ * w t ∂μ)‖ ≤ ‖f‖ := by
  let w' : Ω → ℝ := fun t ↦ max (w t) 0
  have hw' : w =ᵐ[μ] w' := hw_nonneg.mono fun _ ht ↦ (max_eq_left ht).symm
  have hw'_int : Integrable w' μ := hw_int.congr hw'
  have hw'_sum : ∫ t, w' t ∂μ = α := (integral_congr_ae hw'.symm).trans hw_sum
  have hint_eq (i : ι) : ∫ t, ‖f t i‖ * w t ∂μ = ∫ t, ‖f t i‖ * w' t ∂μ :=
    integral_congr_ae (hw'.mono fun _ ht ↦ by dsimp only; rw [ht])
  simp_rw [hint_eq]
  have hint (i : ι) : Integrable (fun t ↦ ‖f t i‖ * w' t) μ :=
    hw'_int.bdd_mul ((PiLp.continuous_apply p β i).comp f.continuous).norm.aestronglyMeasurable
      (ae_of_all _ fun t ↦ by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact (PiLp.norm_apply_le (f t) i).trans (norm_coe_le_norm f t))
  rw [show WithLp.toLp p (fun i ↦ α⁻¹ * ∫ t, ‖f t i‖ * w' t ∂μ) =
      α⁻¹ • WithLp.toLp p (fun i ↦ ∫ t, ‖f t i‖ * w' t ∂μ) from (WithLp.toLp_smul p α⁻¹ _).symm,
    norm_smul, Real.norm_of_nonneg (inv_pos.2 hα).le]
  calc α⁻¹ * ‖WithLp.toLp p (fun i ↦ ∫ t, ‖f t i‖ * w' t ∂μ)‖
      ≤ α⁻¹ * ∫ t, ‖WithLp.toLp p (fun i ↦ ‖f t i‖ * w' t)‖ ∂μ :=
        mul_le_mul_of_nonneg_left (TauCeti.norm_toLp_integral_le _ hint) (inv_pos.2 hα).le
    _ ≤ α⁻¹ * ∫ t, ‖f‖ * w' t ∂μ := mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
        (ae_of_all _ fun _ ↦ norm_nonneg _) (hw'_int.const_mul ‖f‖) (ae_of_all _ fun t ↦ by
          dsimp only
          rw [show WithLp.toLp p (fun i ↦ ‖f t i‖ * w' t) =
              w' t • WithLp.toLp p (fun i ↦ ‖f t i‖) from PiLp.ext fun _ ↦ by simp [mul_comm],
            norm_smul, Real.norm_of_nonneg (le_max_right _ _), PiLp.norm_norm (f t), mul_comm]
          exact mul_le_mul_of_nonneg_right (norm_coe_le_norm f t) (le_max_right _ _)))
        (inv_pos.2 hα).le
    _ = ‖f‖ := by rw [integral_const_mul, hw'_sum, mul_comm ‖f‖, inv_mul_cancel_left₀ hα.ne']

end ZeroAtInftyContinuousMap
