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

private theorem norm_six_le {F : Type*} [NormedAddCommGroup F] (a b c d e f : F) :
    ‖a - b + c + d - e - f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  have h1 := norm_sub_le (a - b + c + d - e) f
  have h2 := norm_sub_le (a - b + c + d) e
  have h3 := norm_add_le (a - b + c) d
  have h4 := norm_add_le (a - b) c
  have h5 := norm_sub_le a b
  linarith

private theorem tendsto_mul_rpow_zero (C : ℝ) {α : ℝ} (hα : 0 < α) :
    Tendsto (fun t : ℝ => C * t ^ α) (𝓝 0) (𝓝 0) := by
  have hc : ContinuousAt (fun t : ℝ => C * t ^ α) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 α (Or.inr hα.le))
  simpa only [Real.zero_rpow hα.ne', mul_zero] using hc.tendsto

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
  have hgauge : Tendsto (fun δ : ℝ => 2 * (K : ℝ) * δ ^ (α : ℝ)) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_mul_rpow_zero _ hαreal).mono_left nhdsWithin_le_nhds
  obtain ⟨δ, hδsmall, hδ0, hδr⟩ :=
    ((hgauge.eventually (gt_mem_nhds (half_pos hε))).and (Ioo_mem_nhdsGT hr0)).exists
  have hsub : closedBall x δ ⊆ ball x r := closedBall_subset_ball hδr
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hD _
    (hsub.trans hrU) (ProperSpace.isCompact_closedBall x δ)
  set η := ε * δ / 32 with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hunif η hη)
  refine ⟨N, fun m hm l hl => ?_⟩
  have hshell : ∀ h : E, δ / ‖(2 : ℝ)‖ ≤ ‖h‖ → ‖h‖ < δ →
      ‖(fderiv ℝ (v m) x - fderiv ℝ (v l) x) h‖ ≤
        (2 * (K : ℝ) * δ ^ (α : ℝ) + 8 * η / δ) * ‖h‖ := by
    intro h hh1 hh2
    rw [Real.norm_two] at hh1
    have hyb : x + h ∈ closedBall x δ := by
      rw [mem_closedBall_iff_norm, add_sub_cancel_left]; exact hh2.le
    have hxb : x ∈ closedBall x δ := mem_closedBall_self hδ0.le
    have hyr : x + h ∈ ball x r := hsub hyb
    have tm := norm_sub_fderiv_le_of_holderOnWith hα hU (hv m) (hhol m) hrU hyr
    have tl := norm_sub_fderiv_le_of_holderOnWith hα hU (hv l) (hhol l) hrU hyr
    rw [add_sub_cancel_left] at tm tl
    have um := hN m hm (x + h) hyb
    have ul := hN l hl (x + h) hyb
    have um0 := hN m hm x hxb
    have ul0 := hN l hl x hxb
    rw [dist_eq_norm] at um ul um0 ul0
    rw [norm_sub_rev] at um um0
    set Dm := v m
    set Dl := v l
    set Dg := f
    set Hm := fderiv ℝ Dm x
    set Hl := fderiv ℝ Dl x
    have e : (Hm - Hl) h = (Dl (x + h) - Dl x - Hl h) - (Dm (x + h) - Dm x - Hm h) +
        (Dm (x + h) - Dg (x + h)) + (Dg (x + h) - Dl (x + h)) - (Dm x - Dg x) -
        (Dg x - Dl x) := by
      rw [sub_apply]; abel
    have hpow : ‖h‖ ^ (α : ℝ) ≤ δ ^ (α : ℝ) := Real.rpow_le_rpow (norm_nonneg _) hh2.le α.coe_nonneg
    have hKh : (K : ℝ) * ‖h‖ ^ (α : ℝ) * ‖h‖ ≤ (K : ℝ) * δ ^ (α : ℝ) * ‖h‖ := by gcongr
    have h4η : 4 * η ≤ 8 * η / δ * ‖h‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ0]; nlinarith
    rw [e]
    refine (norm_six_le _ _ _ _ _ _).trans ?_
    nlinarith
  have hC : 0 ≤ 2 * (K : ℝ) * δ ^ (α : ℝ) + 8 * η / δ := by positivity
  have hop := ContinuousLinearMap.opNorm_le_of_shell (𝕜 := ℝ) (c := (2 : ℝ)) hδ0 hC
    (by norm_num) hshell
  have h8 : 8 * η / δ = ε / 4 := by rw [hη_def]; field_simp; ring
  have hlt : 2 * (K : ℝ) * δ ^ (α : ℝ) + 8 * η / δ < ε := by linarith
  calc dist (fderiv ℝ (v m) x) (fderiv ℝ (v l) x)
      = ‖fderiv ℝ (v m) x - fderiv ℝ (v l) x‖ :=
        dist_eq_norm (fderiv ℝ (v m) x) (fderiv ℝ (v l) x)
    _ ≤ 2 * (K : ℝ) * δ ^ (α : ℝ) + 8 * η / δ := hop
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
    exact (tendsto_mul_rpow_zero _ hαreal).comp hnorm
  refine HasFDerivAt.of_isLittleO (Asymptotics.isLittleO_iff.2 fun c hc => ?_)
  filter_upwards [ball_mem_nhds x hr0, hgauge.eventually (gt_mem_nhds hc)] with y hy hyc
  have happ : Tendsto (fun m => fderiv ℝ (v m) x (y - x)) atTop (𝓝 (A (y - x))) :=
    ((ContinuousLinearMap.apply ℝ F (y - x)).continuous.tendsto A).comp hA
  have hlim := ((hD.tendsto_at (hrU hy)).sub (hD.tendsto_at hx)).sub happ
  have hTaylor := le_of_tendsto' hlim.norm
    (fun m => norm_sub_fderiv_le_of_holderOnWith hα hU (hv m) (hhol m) hrU hy)
  exact hTaylor.trans (mul_le_mul_of_nonneg_right hyc.le (norm_nonneg _))

variable [CompleteSpace F]

/-- A locally uniform limit of differentiable functions with uniformly Hölder derivatives on
an open set is C¹ and inherits the derivative norm and Hölder bounds. -/
theorem contDiffOn_one_and_norm_fderiv_le_and_holderOnWith_fderiv_of_tendstoLocallyUniformlyOn
    (hα : 0 < α) (hU : IsOpen U) (hv : ∀ m, DifferentiableOn ℝ (v m) U)
    (hD : TendstoLocallyUniformlyOn v f atTop U) {M : ℝ}
    (hbound : ∀ m, ∀ x ∈ U, ‖fderiv ℝ (v m) x‖ ≤ M)
    (hhol : ∀ m, HolderOnWith K α (fderiv ℝ (v m)) U) :
    ContDiffOn ℝ 1 f U ∧ (∀ x ∈ U, ‖fderiv ℝ f x‖ ≤ M) ∧
      HolderOnWith K α (fderiv ℝ f) U := by
  have hc := cauchySeq_fderiv_of_tendstoLocallyUniformlyOn hα hU hv hD hhol
  have hderiv (x : E) (hx : x ∈ U) : HasFDerivAt f (limUnder atTop (fun m => fderiv ℝ (v m) x)) x :=
    hasFDerivAt_of_tendsto_fderiv_of_tendstoLocallyUniformlyOn hα hU hv hD hhol hx
      (hc x hx).tendsto_limUnder
  have hlim (x : E) (hx : x ∈ U) :
      Tendsto (fun m => fderiv ℝ (v m) x) atTop (𝓝 (fderiv ℝ f x)) := by
    rw [(hderiv x hx).fderiv]
    exact (hc x hx).tendsto_limUnder
  have hH : HolderOnWith K α (fderiv ℝ f) U := by
    refine HolderOnWith.of_dist_le fun x hx y hy => ?_
    exact le_of_tendsto' ((hlim x hx).dist (hlim y hy)) (fun m => (hhol m).dist_le hx hy)
  refine ⟨?_, fun x hx => le_of_tendsto' (hlim x hx).norm (fun m => hbound m x hx), hH⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num, contDiffOn_succ_iff_fderiv_of_isOpen hU]
  refine ⟨fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  simpa only [contDiffOn_zero] using hH.continuousOn hα

/-- A function is C² when its first derivative is a locally uniform limit of first derivatives
with uniformly bounded and Hölder second derivatives. The bounds pass to the second derivative. -/
theorem contDiffOn_two_and_hessian_bounds_of_tendstoLocallyUniformlyOn_fderiv
    (hα : 0 < α) (hU : IsOpen U) (hv : ∀ m, ContDiffOn ℝ 2 (v m) U)
    (hf : DifferentiableOn ℝ f U)
    (hD : TendstoLocallyUniformlyOn (fun m => fderiv ℝ (v m)) (fderiv ℝ f) atTop U) {M : ℝ}
    (hbound : ∀ m, ∀ x ∈ U, ‖fderiv ℝ (fderiv ℝ (v m)) x‖ ≤ M)
    (hhol : ∀ m, HolderOnWith K α (fderiv ℝ (fderiv ℝ (v m))) U) :
    ContDiffOn ℝ 2 f U ∧ (∀ x ∈ U, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) ∧
      HolderOnWith K α (fderiv ℝ (fderiv ℝ f)) U := by
  have hv' (m : ℕ) : DifferentiableOn ℝ (fderiv ℝ (v m)) U := by
    intro x hx
    have hvAt := (hv m).contDiffAt (hU.mem_nhds hx)
    have hd : ContDiffAt ℝ 1 (fderiv ℝ (v m)) x := hvAt.fderiv_right (by norm_num)
    exact (hd.differentiableAt one_ne_zero).differentiableWithinAt
  obtain ⟨hC, hM, hK⟩ :=
    contDiffOn_one_and_norm_fderiv_le_and_holderOnWith_fderiv_of_tendstoLocallyUniformlyOn
      hα hU hv' hD hbound hhol
  refine ⟨?_, hM, hK⟩
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiffOn_succ_iff_fderiv_of_isOpen hU]
  exact ⟨hf, by simp, hC⟩

end FirstDerivative

end TauCeti
