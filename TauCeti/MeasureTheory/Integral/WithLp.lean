/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import TauCeti.Analysis.Calculus.FDeriv.WithLp
import TauCeti.Analysis.Normed.Lp.PiLp

/-!
# Integrals and energy of maps into `WithLp` spaces

For maps `f` and `g`, the derivative of `w ↦ (f w, g w)` into the Euclidean product
`WithLp 2 (F × E)` in a direction `v` has squared length `‖df v‖² + ‖dg v‖²`
(`TauCeti.norm_fderiv_toLp_prodMk_apply_sq`). Integrating over a set, the energy of the pair in
the direction `v` is the sum of the energies of `f` and `g`
(`TauCeti.setIntegral_norm_fderiv_toLp_prodMk_apply_sq`). For the graph `w ↦ (w, u w)` of a map
`u` and a unit vector `v`, this says that the energy of the graph is the measure of the set plus
the energy of `u`, the energy identity of Gromov's graph construction.

For finite `Lᵖ` spaces `PiLp p E` (`1 ≤ p ≤ ∞`), Bochner–Minkowski gives
`‖toLp p (i ↦ ∫ f i t ∂μ)‖ ≤ ∫ ‖toLp p (i ↦ f i t)‖ ∂μ` (`PiLp.norm_toLp_integral_le`), with a
weighted bound for `f : C₀(Ω, PiLp p β)` (`PiLp.norm_toLp_integral_weighted_le`).
-/

public section

open MeasureTheory
open scoped ENNReal ZeroAtInfty

namespace TauCeti

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [MeasurableSpace G] {μ : Measure G}

/-- On a measurable set where `f` and `g` are differentiable, the energy in the direction `v` of
the map `w ↦ (f w, g w)` into the Euclidean product is the sum of the energies of `f` and `g`. -/
theorem setIntegral_norm_fderiv_toLp_prodMk_apply_sq {f : G → F} {g : G → E} {S : Set G}
    (hS : MeasurableSet S) (hf : ∀ y ∈ S, DifferentiableAt 𝕜 f y)
    (hg : ∀ y ∈ S, DifferentiableAt 𝕜 g y) (v : G)
    (hfi : IntegrableOn (fun y ↦ ‖fderiv 𝕜 f y v‖ ^ 2) S μ)
    (hgi : IntegrableOn (fun y ↦ ‖fderiv 𝕜 g y v‖ ^ 2) S μ) :
    ∫ y in S, ‖fderiv 𝕜 (fun w ↦ WithLp.toLp 2 (f w, g w)) y v‖ ^ 2 ∂μ =
      ∫ y in S, ‖fderiv 𝕜 f y v‖ ^ 2 ∂μ + ∫ y in S, ‖fderiv 𝕜 g y v‖ ^ 2 ∂μ := by
  rw [setIntegral_congr_fun hS fun y hy ↦ norm_fderiv_toLp_prodMk_apply_sq (hf y hy) (hg y hy) v,
    integral_add hfi hgi]

end TauCeti

namespace PiLp

/-- Bochner–Minkowski integral inequality for `PiLp p`: the `PiLp` norm of the coordinatewise
integral is at most the integral of the `PiLp` norm. -/
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

/-- Weighted integral norm bound in `PiLp`: if `f : C₀(Ω, PiLp p β)` and `w ≥ 0` is integrable with
`∫ w ∂μ = α > 0`, then `‖toLp p (i ↦ α⁻¹ * ∫ ‖f t i‖ * w t ∂μ)‖ ≤ ‖f‖`. -/
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
        mul_le_mul_of_nonneg_left (norm_toLp_integral_le _ hint) (inv_pos.2 hα).le
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

end PiLp
