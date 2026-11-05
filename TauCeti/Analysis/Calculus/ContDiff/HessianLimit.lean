/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import TauCeti.Analysis.Holder.Interpolation
import TauCeti.Topology.MetricSpace.Holder

/-!
# Differentiability of locally uniform limits with Hölder derivatives

Locally uniform convergence of differentiable maps with uniformly Hölder derivatives preserves
differentiability, the Hölder bound and any uniform derivative norm bound. Applying this to
gradients gives the corresponding C² limit step for the difference quotient method.

The proof is adapted from the [KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/IteratedDerivative/QuotientLimit.lean).
-/

public section

open Filter Topology Metric
open scoped NNReal

namespace TauCeti

section FirstDerivative

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Set E} {f : E → F} {v : ℕ → E → F} {K α : ℝ≥0}

omit [FiniteDimensional ℝ E] in
private theorem norm_sub_fderiv_le_of_holderOnWith
    (hα : 0 < α) (hU : IsOpen U) {u : E → F} (hu : DifferentiableOn ℝ u U)
    (hhol : HolderOnWith K α (fderiv ℝ u) U)
    {x y : E} {r : ℝ} (hr : ball x r ⊆ U) (hy : y ∈ ball x r) :
    ‖u y - u x - fderiv ℝ u x (y - x)‖ ≤ (K : ℝ) * ‖y - x‖ ^ (α : ℝ) * ‖y - x‖ := by
  have hseg : segment ℝ x (x + (y - x)) ⊆ ball x r := by
    rw [add_sub_cancel]
    have hrpos := lt_of_le_of_lt dist_nonneg (mem_ball.mp hy)
    exact (convex_ball x r).segment_subset (mem_ball_self hrpos) hy
  have hTaylor := (hhol.mono hr).norm_image_sub_sub_le_of_hasFDerivWithinAt
    (fun z hz => ((hu z (hr hz)).differentiableAt (hU.mem_nhds (hr hz))).hasFDerivAt
      |>.hasFDerivWithinAt) hseg
  rw [add_sub_cancel, add_comm 1, Real.rpow_add' (norm_nonneg _) (by positivity),
    Real.rpow_one] at hTaylor
  simpa only [mul_assoc] using hTaylor

private theorem cauchySeq_fderiv_of_tendstoLocallyUniformlyOn
    (hα : 0 < α) (hU : IsOpen U) (hv : ∀ m, DifferentiableOn ℝ (v m) U)
    (hD : TendstoLocallyUniformlyOn v f atTop U)
    (hhol : ∀ m, HolderOnWith K α (fderiv ℝ (v m)) U) :
    ∀ x ∈ U, CauchySeq (fun m => fderiv ℝ (v m) x) := by
  intro x hx
  obtain ⟨r, hr0, hrU⟩ := Metric.isOpen_iff.1 hU x hx
  refine (Metric.cauchySeq_iff (α := E →L[ℝ] F)).2 fun ε hε => ?_
  have hαreal : 0 < (α : ℝ) := by exact_mod_cast hα
  have hgauge : Tendsto (fun δ : ℝ => 2 * (K : ℝ) * δ ^ (α : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, id_eq] using
      (((tendsto_id : Tendsto (fun δ : ℝ => δ) (𝓝 0) (𝓝 0)).rpow_const_nhds_zero
        hαreal).const_mul (2 * (K : ℝ))).mono_left nhdsWithin_le_nhds
  -- Choose δ so the derivative Hölder error is below ε / 2.
  obtain ⟨δ, hδsmall, hδ0, hδr⟩ :=
    ((hgauge.eventually (gt_mem_nhds (half_pos hε))).and (Ioo_mem_nhdsGT hr0)).exists
  have hsub : closedBall x δ ⊆ ball x r := closedBall_subset_ball hδr
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hD _
    (hsub.trans hrU) (ProperSpace.isCompact_closedBall x δ)
  -- This function-error tolerance gives the interpolation error 8 η / δ = ε / 4.
  set η := ε * δ / 32 with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hunif η hη)
  refine ⟨N, fun m hm l hl => ?_⟩
  have hb : ball x δ ⊆ U := ball_subset_closedBall.trans (hsub.trans hrU)
  -- Apply the local interpolation estimate to the difference of the two approximants.
  have hH : HolderOnWith (K + K) α
      (fun y => fderiv ℝ (v m) y - fderiv ℝ (v l) y) (ball x δ) :=
    ((hhol m).sub (hhol l)).mono hb
  have herr (y : E) (hy : y ∈ ball x δ) : ‖v m y - v l y‖ ≤ 2 * η := by
    rw [← dist_eq_norm]
    calc
      dist (v m y) (v l y) ≤ dist (v m y) (f y) + dist (f y) (v l y) :=
        dist_triangle _ _ _
      _ ≤ η + η := add_le_add
        (by simpa only [dist_comm] using (hN m hm y (ball_subset_closedBall hy)).le)
        (hN l hl y (ball_subset_closedBall hy)).le
      _ = 2 * η := (two_mul η).symm
  have hop := hH.norm_le_of_hasFDerivWithinAt_ball
    (g := fun y => v m y - v l y)
    (fun y hy => (((hv m y (hb hy)).differentiableAt (hU.mem_nhds (hb hy))).hasFDerivAt.sub
      ((hv l y (hb hy)).differentiableAt (hU.mem_nhds (hb hy))).hasFDerivAt).hasFDerivWithinAt)
    herr hδ0
  have hop' : ‖fderiv ℝ (v m) x - fderiv ℝ (v l) x‖ ≤
      2 * (K : ℝ) * δ ^ (α : ℝ) + 8 * η / δ := by
    simp only [NNReal.coe_add] at hop
    calc
      _ ≤ 4 * (2 * η) / δ + ((K : ℝ) + (K : ℝ)) * δ ^ (α : ℝ) := hop
      _ = _ := by ring
  have h8 : 8 * η / δ = ε / 4 := by rw [hη_def]; field_simp; ring
  have hlt : 2 * (K : ℝ) * δ ^ (α : ℝ) + 8 * η / δ < ε := by linarith
  calc dist (fderiv ℝ (v m) x) (fderiv ℝ (v l) x)
      = ‖fderiv ℝ (v m) x - fderiv ℝ (v l) x‖ :=
        dist_eq_norm (fderiv ℝ (v m) x) (fderiv ℝ (v l) x)
    _ ≤ 2 * (K : ℝ) * δ ^ (α : ℝ) + 8 * η / δ := hop'
    _ < ε := hlt
omit [FiniteDimensional ℝ E] in
private theorem hasFDerivAt_of_tendsto_fderiv_of_tendstoLocallyUniformlyOn
    (hα : 0 < α) (hU : IsOpen U) (hv : ∀ m, DifferentiableOn ℝ (v m) U)
    (hD : TendstoLocallyUniformlyOn v f atTop U)
    (hhol : ∀ m, HolderOnWith K α (fderiv ℝ (v m)) U)
    {x : E} (hx : x ∈ U) {A : E →L[ℝ] F}
    (hA : Tendsto (fun m => fderiv ℝ (v m) x) atTop (𝓝 A)) : HasFDerivAt f A x := by
  obtain ⟨r, hr0, hrU⟩ := Metric.isOpen_iff.1 hU x hx
  have hαreal : 0 < (α : ℝ) := by exact_mod_cast hα
  have hgauge : Tendsto (fun y : E => (K : ℝ) * ‖y - x‖ ^ (α : ℝ)) (𝓝 x) (𝓝 0) := by
    have hnorm : Tendsto (fun y : E => ‖y - x‖) (𝓝 x) (𝓝 0) := by
      have hc : Continuous (fun y : E => ‖y - x‖) := by fun_prop
      simpa only [sub_self, norm_zero] using hc.tendsto x
    simpa only [mul_zero] using (hnorm.rpow_const_nhds_zero hαreal).const_mul (K : ℝ)
  refine HasFDerivAt.of_isLittleO (Asymptotics.isLittleO_iff.2 fun c hc => ?_)
  filter_upwards [ball_mem_nhds x hr0, hgauge.eventually (gt_mem_nhds hc)] with y hy hyc
  have happ : Tendsto (fun m => fderiv ℝ (v m) x (y - x)) atTop (𝓝 (A (y - x))) :=
    ((ContinuousLinearMap.apply ℝ F (y - x)).continuous.tendsto A).comp hA
  have hlim := ((hD.tendsto_at (hrU hy)).sub (hD.tendsto_at hx)).sub happ
  have hTaylor := le_of_tendsto' hlim.norm
    (fun m => norm_sub_fderiv_le_of_holderOnWith hα hU (hv m) (hhol m) hrU hy)
  exact hTaylor.trans (mul_le_mul_of_nonneg_right hyc.le (norm_nonneg _))

variable [CompleteSpace F]

/-- Uniform Hölder control of the derivatives upgrades locally uniform function convergence
on an open set to pointwise convergence of the derivatives. No global norm bound is needed. -/
theorem tendsto_fderiv_of_tendstoLocallyUniformlyOn_of_holderOnWith
    (hα : 0 < α) (hU : IsOpen U) (hv : ∀ m, DifferentiableOn ℝ (v m) U)
    (hD : TendstoLocallyUniformlyOn v f atTop U)
    (hhol : ∀ m, HolderOnWith K α (fderiv ℝ (v m)) U) {x : E} (hx : x ∈ U) :
    Tendsto (fun m => fderiv ℝ (v m) x) atTop (𝓝 (fderiv ℝ f x)) := by
  have hc := cauchySeq_fderiv_of_tendstoLocallyUniformlyOn hα hU hv hD hhol x hx
  have hderiv := hasFDerivAt_of_tendsto_fderiv_of_tendstoLocallyUniformlyOn
    hα hU hv hD hhol hx hc.tendsto_limUnder
  rw [hderiv.fderiv]
  exact hc.tendsto_limUnder

/-- A locally uniform limit of differentiable functions with uniformly Hölder derivatives on
an open set is C¹ and inherits the Hölder bound, without a global derivative norm bound. -/
theorem contDiffOn_one_and_holderOnWith_fderiv_of_tendstoLocallyUniformlyOn
    (hα : 0 < α) (hU : IsOpen U) (hv : ∀ m, DifferentiableOn ℝ (v m) U)
    (hD : TendstoLocallyUniformlyOn v f atTop U)
    (hhol : ∀ m, HolderOnWith K α (fderiv ℝ (v m)) U) :
    ContDiffOn ℝ 1 f U ∧ HolderOnWith K α (fderiv ℝ f) U := by
  have hlim (x : E) (hx : x ∈ U) :=
    tendsto_fderiv_of_tendstoLocallyUniformlyOn_of_holderOnWith hα hU hv hD hhol hx
  have hH : HolderOnWith K α (fderiv ℝ f) U := by
    refine HolderOnWith.of_dist_le fun x hx y hy => ?_
    exact le_of_tendsto' ((hlim x hx).dist (hlim y hy)) (fun m => (hhol m).dist_le hx hy)
  refine ⟨?_, hH⟩
  apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) hU).2
  refine ⟨fun x hx => ?_, by simp, ?_⟩
  · exact (hasFDerivAt_of_tendsto_fderiv_of_tendstoLocallyUniformlyOn
      hα hU hv hD hhol hx (hlim x hx)).differentiableAt.differentiableWithinAt
  · simpa only [contDiffOn_zero] using hH.continuousOn hα

/-- A uniform derivative norm bound passes to the locally uniform limit when the derivatives
have a common positive Hölder exponent. -/
theorem norm_fderiv_le_of_tendstoLocallyUniformlyOn_of_holderOnWith
    (hα : 0 < α) (hU : IsOpen U) (hv : ∀ m, DifferentiableOn ℝ (v m) U)
    (hD : TendstoLocallyUniformlyOn v f atTop U)
    (hhol : ∀ m, HolderOnWith K α (fderiv ℝ (v m)) U) {M : ℝ}
    (hbound : ∀ m, ∀ x ∈ U, ‖fderiv ℝ (v m) x‖ ≤ M) {x : E} (hx : x ∈ U) :
    ‖fderiv ℝ f x‖ ≤ M :=
  le_of_tendsto'
    (tendsto_fderiv_of_tendstoLocallyUniformlyOn_of_holderOnWith hα hU hv hD hhol hx).norm
    (fun m => hbound m x hx)

/-- A differentiable function is C² with Hölder second derivative when its first derivative
is a locally uniform limit of first derivatives with a common Hölder second-derivative bound.
The second derivatives need not have a global norm bound. -/
theorem contDiffOn_two_and_holderOnWith_fderiv_fderiv_of_tendstoLocallyUniformlyOn_fderiv
    (hα : 0 < α) (hU : IsOpen U) (hv : ∀ m, ContDiffOn ℝ 2 (v m) U)
    (hf : DifferentiableOn ℝ f U)
    (hD : TendstoLocallyUniformlyOn (fun m => fderiv ℝ (v m)) (fderiv ℝ f) atTop U)
    (hhol : ∀ m, HolderOnWith K α (fderiv ℝ (fderiv ℝ (v m))) U) :
    ContDiffOn ℝ 2 f U ∧ HolderOnWith K α (fderiv ℝ (fderiv ℝ f)) U := by
  have hv' (m : ℕ) : DifferentiableOn ℝ (fderiv ℝ (v m)) U :=
    ((hv m).fderiv_of_isOpen hU (m := 1) (by norm_num)).differentiableOn one_ne_zero
  obtain ⟨hC, hK⟩ := contDiffOn_one_and_holderOnWith_fderiv_of_tendstoLocallyUniformlyOn
    hα hU hv' hD hhol
  exact ⟨(contDiffOn_succ_iff_fderiv_of_isOpen (n := 1) hU).2 ⟨hf, by simp, hC⟩, hK⟩

/-- A uniform second-derivative norm bound passes to the limit under locally uniform
convergence of the first derivatives and a common positive Hölder exponent. -/
theorem norm_fderiv_fderiv_le_of_tendstoLocallyUniformlyOn_fderiv_of_holderOnWith
    (hα : 0 < α) (hU : IsOpen U) (hv : ∀ m, ContDiffOn ℝ 2 (v m) U)
    (hD : TendstoLocallyUniformlyOn (fun m => fderiv ℝ (v m)) (fderiv ℝ f) atTop U)
    (hhol : ∀ m, HolderOnWith K α (fderiv ℝ (fderiv ℝ (v m))) U) {M : ℝ}
    (hbound : ∀ m, ∀ x ∈ U, ‖fderiv ℝ (fderiv ℝ (v m)) x‖ ≤ M) {x : E} (hx : x ∈ U) :
    ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M := by
  exact norm_fderiv_le_of_tendstoLocallyUniformlyOn_of_holderOnWith hα hU
    (fun m => ((hv m).fderiv_of_isOpen hU (m := 1) (by norm_num)).differentiableOn one_ne_zero)
    hD hhol hbound hx

end FirstDerivative

end TauCeti
