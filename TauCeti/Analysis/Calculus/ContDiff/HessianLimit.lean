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
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import TauCeti.Analysis.Holder.Interpolation
import TauCeti.Topology.MetricSpace.Holder

/-!
# Limits of gradients with uniformly Hölder Hessians

Local uniform convergence of gradients and uniform bounds on their Hessians and Hölder moduli
give a twice differentiable limit with the same bounds. In the difference quotient method this
passes an interior Schauder bound to the directional derivative.

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

private theorem tendsto_holder_gauge {E : Type*} [NormedAddCommGroup E] (K : ℝ) {α : ℝ}
    (hα : 0 < α) (x : E) : Tendsto (fun y => K * ‖y - x‖ ^ α) (𝓝 x) (𝓝 0) := by
  have hc : Continuous (fun y => K * ‖y - x‖ ^ α) :=
    continuous_const.mul ((continuous_id.sub continuous_const).norm.rpow_const
      fun _ => Or.inr hα.le)
  simpa [Real.zero_rpow hα.ne'] using hc.tendsto x

private theorem continuousOn_of_holder {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {U : Set E} {G : E → F} {K α : ℝ} (hα : 0 < α)
    (hG : ∀ x ∈ U, ∀ y ∈ U, ‖G x - G y‖ ≤ K * ‖x - y‖ ^ α) : ContinuousOn G U := by
  intro x hx
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    ((tendsto_holder_gauge K hα x).mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with y hy using hG y hy x hx

/-- **C² limits with uniformly Hölder Hessians.** Let `U` be open in a finite-dimensional real
normed space, `v m` of class `C²` on `U` with Hessians bounded by `K` and `α`-Hölder with constant
`K` on `U` (`0 < α`), and suppose `fderiv ℝ (v m) → fderiv ℝ g` locally uniformly on `U`, where `g`
is `C¹` on `U`. Then `g` is `C²` on `U`, `‖D²g‖ ≤ K` on `U` and
`‖D²g x - D²g y‖ ≤ K ‖x - y‖ ^ α` for `x, y ∈ U`. -/
theorem contDiffOn_two_of_hessian_limit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) (g : E → ℝ) (v : ℕ → E → ℝ) (K : ℝ) {α : ℝ} (hα : 0 < α)
    (hv : ∀ m, ContDiffOn ℝ 2 (v m) U)
    (hg : ContDiffOn ℝ 1 g U)
    (hD : TendstoLocallyUniformlyOn (fun m => fderiv ℝ (v m)) (fderiv ℝ g) Filter.atTop U)
    (hbound : ∀ m, ∀ x ∈ U, ‖fderiv ℝ (fderiv ℝ (v m)) x‖ ≤ K)
    (hhol : ∀ m, ∀ x ∈ U, ∀ y ∈ U,
      ‖fderiv ℝ (fderiv ℝ (v m)) x - fderiv ℝ (fderiv ℝ (v m)) y‖ ≤ K * ‖x - y‖ ^ α) :
    ContDiffOn ℝ 2 g U ∧ (∀ x ∈ U, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ K) ∧
      ∀ x ∈ U, ∀ y ∈ U, ‖fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ g) y‖ ≤ K * ‖x - y‖ ^ α := by
  -- the gradients `v m` are differentiable on `U` with derivative the Hessian
  have hdiff : ∀ m, ∀ z ∈ U, HasFDerivAt (fderiv ℝ (v m)) (fderiv ℝ (fderiv ℝ (v m)) z) z := by
    intro m z hz
    have h1 : ContDiffAt ℝ 2 (v m) z := (hv m).contDiffAt (hU.mem_nhds hz)
    have h2 : ContDiffAt ℝ 1 (fderiv ℝ (v m)) z := h1.fderiv_right (by norm_num)
    exact (h2.differentiableAt one_ne_zero).hasFDerivAt
  -- Taylor remainder of each gradient on balls inside `U`
  have htaylor : ∀ m, ∀ x ∈ U, ∀ r, ball x r ⊆ U → ∀ y ∈ ball x r,
      ‖fderiv ℝ (v m) y - fderiv ℝ (v m) x - fderiv ℝ (fderiv ℝ (v m)) x (y - x)‖ ≤
        K * ‖y - x‖ ^ α * ‖y - x‖ := by
    intro m x hx r hr y hy
    have hK : 0 ≤ K := (ContinuousLinearMap.opNorm_nonneg _).trans (hbound m x hx)
    have hH : HolderOnWith K.toNNReal α.toNNReal (fderiv ℝ (fderiv ℝ (v m))) (ball x r) :=
      HolderOnWith.of_dist_le fun z hz w hw => by
        simpa only [dist_eq_norm, Real.coe_toNNReal K hK, Real.coe_toNNReal α hα.le] using
          hhol m z (hr hz) w (hr hw)
    have hseg : segment ℝ x (x + (y - x)) ⊆ ball x r := by
      rw [add_sub_cancel]
      have hrpos := lt_of_le_of_lt dist_nonneg (mem_ball.mp hy)
      exact (convex_ball x r).segment_subset (mem_ball_self hrpos) hy
    have hTaylor := hH.norm_image_sub_sub_le_of_hasFDerivWithinAt
      (fun z hz => (hdiff m z (hr hz)).hasFDerivWithinAt) hseg
    simp only [add_sub_cancel, Real.coe_toNNReal K hK, Real.coe_toNNReal α hα.le] at hTaylor
    rw [add_comm 1 α, Real.rpow_add' (norm_nonneg _) (by positivity),
      Real.rpow_one] at hTaylor
    simpa only [mul_assoc] using hTaylor
  -- the Hessians converge pointwise in operator norm
  have hcauchy : ∀ x ∈ U, CauchySeq (fun m => fderiv ℝ (fderiv ℝ (v m)) x) := by
    intro x hx
    have hK : 0 ≤ K := (ContinuousLinearMap.opNorm_nonneg _).trans (hbound 0 x hx)
    obtain ⟨r, hr0, hrU⟩ := Metric.isOpen_iff.1 hU x hx
    refine (Metric.cauchySeq_iff (α := E →L[ℝ] E →L[ℝ] ℝ)).2 fun ε hε => ?_
    have hgauge : Tendsto (fun δ : ℝ => 2 * K * δ ^ α) (𝓝[>] 0) (𝓝 0) := by
      have hc : ContinuousAt (fun δ : ℝ => 2 * K * δ ^ α) 0 :=
        continuousAt_const.mul (Real.continuousAt_rpow_const 0 α (Or.inr hα.le))
      have h0 : 2 * K * (0 : ℝ) ^ α = 0 := by simp [Real.zero_rpow hα.ne']
      have ht := hc.tendsto
      simp only [h0] at ht
      exact ht.mono_left nhdsWithin_le_nhds
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
        ‖(fderiv ℝ (fderiv ℝ (v m)) x - fderiv ℝ (fderiv ℝ (v l)) x) h‖ ≤
          (2 * K * δ ^ α + 8 * η / δ) * ‖h‖ := by
      intro h hh1 hh2
      rw [Real.norm_two] at hh1
      have hyb : x + h ∈ closedBall x δ := by
        rw [mem_closedBall_iff_norm, add_sub_cancel_left]; exact hh2.le
      have hxb : x ∈ closedBall x δ := mem_closedBall_self hδ0.le
      have hyr : x + h ∈ ball x r := hsub hyb
      have tm := htaylor m x hx r hrU (x + h) hyr
      have tl := htaylor l x hx r hrU (x + h) hyr
      rw [add_sub_cancel_left] at tm tl
      have um := hN m hm (x + h) hyb
      have ul := hN l hl (x + h) hyb
      have um0 := hN m hm x hxb
      have ul0 := hN l hl x hxb
      rw [dist_eq_norm] at um ul um0 ul0
      rw [norm_sub_rev] at um um0
      set Dm := fderiv ℝ (v m)
      set Dl := fderiv ℝ (v l)
      set Dg := fderiv ℝ g
      set Hm := fderiv ℝ Dm x
      set Hl := fderiv ℝ Dl x
      have e : (Hm - Hl) h = (Dl (x + h) - Dl x - Hl h) - (Dm (x + h) - Dm x - Hm h) +
          (Dm (x + h) - Dg (x + h)) + (Dg (x + h) - Dl (x + h)) - (Dm x - Dg x) -
          (Dg x - Dl x) := by
        rw [sub_apply]; abel
      have hpow : ‖h‖ ^ α ≤ δ ^ α := Real.rpow_le_rpow (norm_nonneg _) hh2.le hα.le
      have hKh : K * ‖h‖ ^ α * ‖h‖ ≤ K * δ ^ α * ‖h‖ := by gcongr
      have h4η : 4 * η ≤ 8 * η / δ * ‖h‖ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδ0]; nlinarith
      rw [e]
      refine (norm_six_le _ _ _ _ _ _).trans ?_
      nlinarith
    have hC : 0 ≤ 2 * K * δ ^ α + 8 * η / δ := by positivity
    have hop := ContinuousLinearMap.opNorm_le_of_shell (𝕜 := ℝ) (c := (2 : ℝ)) hδ0 hC
      (by norm_num) hshell
    have h8 : 8 * η / δ = ε / 4 := by rw [hη_def]; field_simp; ring
    have hlt : 2 * K * δ ^ α + 8 * η / δ < ε := by linarith
    calc dist (fderiv ℝ (fderiv ℝ (v m)) x) (fderiv ℝ (fderiv ℝ (v l)) x)
        = ‖fderiv ℝ (fderiv ℝ (v m)) x - fderiv ℝ (fderiv ℝ (v l)) x‖ :=
          dist_eq_norm (fderiv ℝ (fderiv ℝ (v m)) x) (fderiv ℝ (fderiv ℝ (v l)) x)
      _ ≤ 2 * K * δ ^ α + 8 * η / δ := hop
      _ < ε := hlt
  set G : E → E →L[ℝ] E →L[ℝ] ℝ := fun x => limUnder atTop (fun m => fderiv ℝ (fderiv ℝ (v m)) x)
    with hG_def
  have hG : ∀ x ∈ U, Tendsto (fun m => fderiv ℝ (fderiv ℝ (v m)) x) atTop (𝓝 (G x)) :=
    fun x hx => (hcauchy x hx).tendsto_limUnder
  have hGbound : ∀ x ∈ U, ‖G x‖ ≤ K := by
    intro x hx
    have hn := Filter.Tendsto.norm (E := E →L[ℝ] E →L[ℝ] ℝ) (hG x hx)
    exact le_of_tendsto' hn (fun m => hbound m x hx)
  have hGhol : ∀ x ∈ U, ∀ y ∈ U, ‖G x - G y‖ ≤ K * ‖x - y‖ ^ α := by
    intro x hx y hy
    have hn := Filter.Tendsto.norm (E := E →L[ℝ] E →L[ℝ] ℝ) ((hG x hx).sub (hG y hy))
    exact le_of_tendsto' hn (fun m => hhol m x hx y hy)
  -- Taylor remainder of the limit gradient
  have hlimTaylor : ∀ x ∈ U, ∀ r, ball x r ⊆ U → ∀ y ∈ ball x r,
      ‖fderiv ℝ g y - fderiv ℝ g x - G x (y - x)‖ ≤ K * ‖y - x‖ ^ α * ‖y - x‖ := by
    intro x hx r hrU y hy
    have happ : Tendsto (fun m => fderiv ℝ (fderiv ℝ (v m)) x (y - x)) atTop
        (𝓝 (G x (y - x))) :=
      ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (y - x)).continuous.tendsto (G x)).comp
        (hG x hx)
    have hlim := ((hD.tendsto_at (hrU hy)).sub (hD.tendsto_at hx)).sub happ
    exact le_of_tendsto' hlim.norm (fun m => htaylor m x hx r hrU y hy)
  -- the limit gradient is differentiable with derivative `G`
  have hGderiv : ∀ x ∈ U, HasFDerivAt (fderiv ℝ g) (G x) x := by
    intro x hx
    obtain ⟨r, hr0, hrU⟩ := Metric.isOpen_iff.1 hU x hx
    refine HasFDerivAt.of_isLittleO (Asymptotics.isLittleO_iff.2 fun c hc => ?_)
    filter_upwards [ball_mem_nhds x hr0,
      (tendsto_holder_gauge K hα x).eventually (gt_mem_nhds hc)] with y hy hyc
    calc ‖fderiv ℝ g y - fderiv ℝ g x - G x (y - x)‖
        ≤ K * ‖y - x‖ ^ α * ‖y - x‖ := hlimTaylor x hx r hrU y hy
      _ ≤ c * ‖y - x‖ := mul_le_mul_of_nonneg_right hyc.le (norm_nonneg _)
  have hHess : ∀ x ∈ U, fderiv ℝ (fderiv ℝ g) x = G x := fun x hx => (hGderiv x hx).fderiv
  refine ⟨?_, fun x hx => hHess x hx ▸ hGbound x hx, fun x hx y hy => ?_⟩
  · rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨hg.differentiableOn one_ne_zero, by simp, ?_⟩
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (hGderiv x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    exact (continuousOn_of_holder (F := E →L[ℝ] E →L[ℝ] ℝ) hα hGhol).congr hHess
  · rw [hHess x hx, hHess y hy]; exact hGhol x hx y hy

end TauCeti
