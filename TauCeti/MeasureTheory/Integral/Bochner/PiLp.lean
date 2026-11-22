/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import TauCeti.Analysis.Normed.Lp.PiLp.Basic

/-!
# Bochner integrals and finite `Lᵖ` norms

For finite `Lᵖ` spaces `PiLp p E` (`1 ≤ p ≤ ∞`) with complete real normed fibers `E i` and
integrable coordinate functions `f i : Ω → E i`, Bochner–Minkowski gives
`‖toLp p (i ↦ ∫ t, f i t ∂μ)‖ ≤ ∫ t, ‖toLp p (i ↦ f i t)‖ ∂μ` (`PiLp.norm_toLp_integral_le`).
Specializing to coordinate norms of a map `f : C₀(Ω, PiLp p β)` and a nonnegative integrable
weight `w` of total mass `∫ w ∂μ = α > 0` yields the normalized weighted norm bound
`‖toLp p (i ↦ α⁻¹ * ∫ t, ‖f t i‖ * w t ∂μ)‖ ≤ ‖f‖`
(`ZeroAtInftyContinuousMap.norm_toLp_integral_weighted_le`).
-/

public section

open MeasureTheory
open scoped ENNReal ZeroAtInfty

namespace PiLp

/-- Bochner–Minkowski integral inequality for `PiLp p`: for `1 ≤ p ≤ ∞`, complete real normed
fibers `E i`, and integrable coordinate functions `f i`, the `PiLp` norm of the coordinatewise
Bochner integral is at most the Bochner integral of the `PiLp` norm. -/
theorem norm_toLp_integral_le {Ω ι : Type*} [Fintype ι] [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] [∀ i, CompleteSpace (E i)]
    (f : ∀ i, Ω → E i) (hf : ∀ i, Integrable (f i) μ) :
    ‖WithLp.toLp p (fun i ↦ ∫ t, f i t ∂μ)‖ ≤ ∫ t, ‖WithLp.toLp p (fun i ↦ f i t)‖ ∂μ := by
  let F : Ω → PiLp p E := fun t ↦ WithLp.toLp p (fun i ↦ f i t)
  have hF : WithLp.toLp p (fun i ↦ ∫ t, f i t ∂μ) = ∫ t, F t ∂μ :=
    PiLp.ext fun i ↦ (MeasureTheory.eval_integral_piLp (f := F) hf i).symm
  rw [hF]
  exact norm_integral_le_integral_norm F

end PiLp

namespace ZeroAtInftyContinuousMap

/-- Weighted integral norm bound in `PiLp`: for `f : C₀(Ω, PiLp p β)` with `1 ≤ p ≤ ∞` and
normed additive commutative group fibers `β i`, and a nonnegative integrable weight `w` of total
mass `∫ w ∂μ = α > 0`, `‖toLp p (i ↦ α⁻¹ * ∫ ‖f t i‖ * w t ∂μ)‖ ≤ ‖f‖`. -/
theorem norm_toLp_integral_weighted_le {Ω ι : Type*} [Fintype ι] [TopologicalSpace Ω]
    [MeasurableSpace Ω] [OpensMeasurableSpace Ω] {μ : Measure Ω} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {β : ι → Type*} [∀ i, NormedAddCommGroup (β i)] (f : C₀(Ω, PiLp p β)) {w : Ω → ℝ} {α : ℝ}
    (hα : 0 < α) (hw_int : Integrable w μ) (hw_nonneg : ∀ t, 0 ≤ w t)
    (hw_sum : ∫ t, w t ∂μ = α) :
    ‖WithLp.toLp p (fun i ↦ α⁻¹ * ∫ t, ‖f t i‖ * w t ∂μ)‖ ≤ ‖f‖ := by
  have hint (i : ι) : Integrable (fun t ↦ ‖f t i‖ * w t) μ :=
    hw_int.bdd_mul ((PiLp.continuous_apply p β i).comp f.continuous).norm.aestronglyMeasurable
      (ae_of_all _ fun t ↦ by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact (PiLp.norm_apply_le (f t) i).trans
          (ZeroAtInftyContinuousMap.norm_coe_le_norm f t))
  have hsmul : WithLp.toLp p (fun i ↦ α⁻¹ * ∫ t, ‖f t i‖ * w t ∂μ) =
      α⁻¹ • WithLp.toLp p (fun i ↦ ∫ t, ‖f t i‖ * w t ∂μ) :=
    (WithLp.toLp_smul p α⁻¹ (fun i ↦ ∫ t, ‖f t i‖ * w t ∂μ)).symm
  rw [hsmul, norm_smul, Real.norm_of_nonneg (inv_pos.2 hα).le]
  calc α⁻¹ * ‖WithLp.toLp p (fun i ↦ ∫ t, ‖f t i‖ * w t ∂μ)‖
      ≤ α⁻¹ * ∫ t, ‖WithLp.toLp p (fun i ↦ ‖f t i‖ * w t)‖ ∂μ :=
        mul_le_mul_of_nonneg_left (PiLp.norm_toLp_integral_le _ hint) (inv_pos.2 hα).le
    _ ≤ α⁻¹ * ∫ t, ‖f‖ * w t ∂μ := by
        refine mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
          (ae_of_all _ fun _ ↦ norm_nonneg _) (hw_int.const_mul ‖f‖)
          (ae_of_all _ fun t ↦ ?_)) (inv_pos.2 hα).le
        have hfactor : WithLp.toLp p (fun i ↦ ‖f t i‖ * w t) =
            w t • WithLp.toLp p (fun i ↦ ‖f t i‖) :=
          (PiLp.ext fun i ↦ mul_comm _ _).trans
            (WithLp.toLp_smul p (w t) (fun i ↦ ‖f t i‖))
        dsimp only
        rw [hfactor, norm_smul, Real.norm_of_nonneg (hw_nonneg t), PiLp.norm_norm (f t), mul_comm]
        exact mul_le_mul_of_nonneg_right (ZeroAtInftyContinuousMap.norm_coe_le_norm f t)
          (hw_nonneg t)
    _ = ‖f‖ := by rw [integral_const_mul, hw_sum, mul_comm ‖f‖, inv_mul_cancel_left₀ hα.ne']

end ZeroAtInftyContinuousMap
