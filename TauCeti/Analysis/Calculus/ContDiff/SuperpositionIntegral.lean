/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
import TauCeti.Analysis.Calculus.FDeriv.BoundedContinuousFunction

/-!
# Smooth integral functionals of superpositions

Let `F u` be a family of bounded continuous functions `α → X`, depending smoothly on a parameter
`u` for the sup norm, let `G : X → ℝ` be smooth and let `w` be an integrable weight on `α`. This
file shows that `u ↦ ∫ w (G ∘ F u)` is smooth, and more precisely `C^n` when `F` and `G` are
(`BoundedContinuousFunction.contDiff_integral_mul_comp`).

The superposition operator `f ↦ G ∘ f` is `C^n` near every bounded continuous function whose values
stay in a compact set (`BoundedContinuousFunction.exists_contDiffAt_forall_apply_eq`), and
integration against `w` is a continuous linear functional on bounded continuous functions
(`BoundedContinuousFunction.integralMulCLM`). Such functionals compute, for instance, the moments
of a nonlinear function of a field, such as `log |α|²` for a section `α` away from its zeros,
smoothly in the field.
-/

public section

open MeasureTheory Metric
open scoped BoundedContinuousFunction ContDiff

namespace BoundedContinuousFunction

variable {α E X : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
  {μ : Measure α} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X]
  [NormedSpace ℝ X] [ProperSpace X]

/-- Integration against an integrable weight `w`, as a continuous linear functional
`g ↦ ∫ w g` on real bounded continuous functions, of norm at most `∫ ‖w‖`. -/
@[expose] noncomputable def integralMulCLM {w : α → ℝ} (hw : Integrable w μ) : (α →ᵇ ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun g := ∫ t, w t * g t ∂μ
      map_add' g g' := by
        simp only [add_apply, mul_add]
        exact integral_add (hw.mul_bdd g.continuous.aestronglyMeasurable
          (ae_of_all _ fun t ↦ g.norm_coe_le_norm t)) (hw.mul_bdd
          g'.continuous.aestronglyMeasurable (ae_of_all _ fun t ↦ g'.norm_coe_le_norm t))
      map_smul' c g := by
        simp only [smul_apply, smul_eq_mul, RingHom.id_apply, mul_left_comm (w _),
          integral_const_mul] }
    (∫ t, ‖w t‖ ∂μ) fun g ↦ by
      refine (norm_integral_le_of_norm_le (hw.norm.mul_const ‖g‖)
        (ae_of_all _ fun t ↦ ?_)).trans_eq (by rw [integral_mul_const, mul_comm])
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm t) (norm_nonneg _)

/-- `integralMulCLM hw` integrates `g` against the weight `w`. -/
@[simp]
theorem integralMulCLM_apply {w : α → ℝ} (hw : Integrable w μ) (g : α →ᵇ ℝ) :
    integralMulCLM hw g = ∫ t, w t * g t ∂μ :=
  rfl

/-- The operator norm of integration against `w` is at most the `L¹` norm `∫ ‖w‖` of `w`. -/
theorem norm_integralMulCLM_le {w : α → ℝ} (hw : Integrable w μ) :
    ‖integralMulCLM hw‖ ≤ ∫ t, ‖w t‖ ∂μ :=
  LinearMap.mkContinuous_norm_le _ (integral_nonneg fun _ ↦ norm_nonneg _) _

/-- **Smooth integral functionals of superpositions.** If `F` is a `C^n` family of bounded
continuous functions `α → X`, `G : X → ℝ` is `C^n` and `w` is integrable, then
`u ↦ ∫ w (G ∘ F u)` is `C^n`. -/
theorem contDiff_integral_mul_comp {n : ℕ∞} {F : E → α →ᵇ X} (hF : ContDiff ℝ n F) {G : X → ℝ}
    (hG : ContDiff ℝ n G) {w : α → ℝ} (hw : Integrable w μ) :
    ContDiff ℝ n fun u ↦ ∫ t, w t * G (F u t) ∂μ := by
  refine contDiff_iff_forall_nat_le.2 fun j hj ↦ contDiff_iff_contDiffAt.2 fun u₀ ↦ ?_
  -- Near `F u₀` the superposition by `G` is a `Cʲ` operator on bounded continuous functions.
  obtain ⟨Θ, hΘ, hΘeq⟩ := exists_contDiffAt_forall_apply_eq
    (hG.of_le (by exact_mod_cast hj) : ContDiff ℝ j G) (isCompact_closedBall (0 : X)
      (‖F u₀‖ + 1)) one_pos fun t y hy ↦ mem_closedBall_zero_iff.2 <| by
        linarith [(F u₀).norm_coe_le_norm t, norm_sub_norm_le y (F u₀ t),
          (mem_ball_iff_norm.1 hy).le]
  refine (((integralMulCLM hw).contDiff.contDiffAt.comp _ (hΘ.comp u₀
    (hF.of_le (by exact_mod_cast hj)).contDiffAt))).congr_of_eventuallyEq ?_
  filter_upwards [hF.continuous.continuousAt.eventually (ball_mem_nhds (F u₀) one_pos)] with u hu
  simp only [Function.comp_apply, integralMulCLM_apply, hΘeq _ hu]

end BoundedContinuousFunction
