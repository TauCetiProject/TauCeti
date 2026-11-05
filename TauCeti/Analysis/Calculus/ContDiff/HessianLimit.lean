/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.Holder.Interpolation

/-!
# Differentiability of locally uniform limits with Hölder derivatives

Locally uniform convergence of maps that are eventually differentiable with a common
derivative Hölder bound preserves differentiability and that bound. A derivative norm
bound at a fixed point passes to the limit if it holds eventually along the filter.
Approximating the gradient by differentiable linear-map-valued fields gives the C² limit
step for the difference quotient method. The family is indexed by any nontrivial filter,
so regularity need only hold for small nonzero parameters in a real-parameter limit `h →
0`.

The proof is adapted from the [KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/IteratedDerivative/QuotientLimit.lean).
-/

public section

open Filter Topology Metric
open scoped NNReal

namespace TauCeti

section FirstDerivative

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} {l : Filter ι} [l.NeBot]
  {U : Set E} {f : E → F} {v : ι → E → F} {K α : ℝ≥0}

private theorem cauchy_map_fderiv_of_tendstoLocallyUniformlyOn
    (hα : 0 < α) (hU : IsOpen U) (hv : ∀ᶠ m in l, DifferentiableOn ℝ (v m) U)
    (hD : TendstoLocallyUniformlyOn v f l U)
    (hhol : ∀ᶠ m in l, HolderOnWith K α (fderiv ℝ (v m)) U) :
    ∀ x ∈ U, Cauchy (map (fun m => fderiv ℝ (v m) x) l) := by
  intro x hx
  obtain ⟨r, hr0, hrU⟩ := Metric.isOpen_iff.1 hU x hx
  refine Metric.cauchy_iff.2 ⟨by infer_instance, fun ε hε => ?_⟩
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
  let S : Set ι := {m | (∀ y ∈ closedBall x δ, dist (f y) (v m y) < η) ∧
    DifferentiableOn ℝ (v m) U ∧ HolderOnWith K α (fderiv ℝ (v m)) U}
  have hS : S ∈ l := (Metric.tendstoUniformlyOn_iff.1 hunif η hη).and (hv.and hhol)
  refine ⟨(fun m => fderiv ℝ (v m) x) '' S,
    mem_map_iff_exists_image.2 ⟨S, hS, Set.Subset.rfl⟩, ?_⟩
  rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩
  have hb : ball x δ ⊆ U := ball_subset_closedBall.trans (hsub.trans hrU)
  have herr (y : E) (hy : y ∈ ball x δ) : ‖v m y - v n y‖ ≤ 2 * η := by
    rw [← dist_eq_norm]
    calc
      dist (v m y) (v n y) ≤ dist (v m y) (f y) + dist (f y) (v n y) :=
        dist_triangle _ _ _
      _ ≤ η + η := add_le_add
        (by simpa only [dist_comm] using (hm.1 y (ball_subset_closedBall hy)).le)
        (hn.1 y (ball_subset_closedBall hy)).le
      _ = 2 * η := (two_mul η).symm
  have hop := (hm.2.2.mono hb).norm_fderiv_sub_fderiv_le_of_norm_sub_le_ball
    (hn.2.2.mono hb) (hm.2.1.mono hb) (hn.2.1.mono hb) herr hδ0
  have hop' : ‖fderiv ℝ (v m) x - fderiv ℝ (v n) x‖ ≤
      2 * (K : ℝ) * δ ^ (α : ℝ) + 8 * η / δ := by
    calc
      _ ≤ 4 * (2 * η) / δ + ((K : ℝ) + (K : ℝ)) * δ ^ (α : ℝ) := hop
      _ = _ := by ring
  have h8 : 8 * η / δ = ε / 4 := by rw [hη_def]; field_simp; ring
  have hlt : 2 * (K : ℝ) * δ ^ (α : ℝ) + 8 * η / δ < ε := by linarith
  calc dist (fderiv ℝ (v m) x) (fderiv ℝ (v n) x)
      = ‖fderiv ℝ (v m) x - fderiv ℝ (v n) x‖ :=
        dist_eq_norm (fderiv ℝ (v m) x) (fderiv ℝ (v n) x)
    _ ≤ 2 * (K : ℝ) * δ ^ (α : ℝ) + 8 * η / δ := hop'
    _ < ε := hlt

omit [FiniteDimensional ℝ E] in
private theorem hasFDerivAt_of_tendsto_fderiv_of_tendstoLocallyUniformlyOn
    (hα : 0 < α) (hU : IsOpen U) (hv : ∀ᶠ m in l, DifferentiableOn ℝ (v m) U)
    (hD : TendstoLocallyUniformlyOn v f l U)
    (hhol : ∀ᶠ m in l, HolderOnWith K α (fderiv ℝ (v m)) U)
    {x : E} (hx : x ∈ U) {A : E →L[ℝ] F}
    (hA : Tendsto (fun m => fderiv ℝ (v m) x) l (𝓝 A)) : HasFDerivAt f A x := by
  obtain ⟨r, hr0, hrU⟩ := Metric.isOpen_iff.1 hU x hx
  have hαreal : 0 < (α : ℝ) := by exact_mod_cast hα
  have hgauge : Tendsto (fun y : E => (K : ℝ) * ‖y - x‖ ^ (α : ℝ)) (𝓝 x) (𝓝 0) := by
    simpa only [mul_zero] using
      ((tendsto_norm_sub_self x).rpow_const_nhds_zero hαreal).const_mul (K : ℝ)
  refine HasFDerivAt.of_isLittleO (Asymptotics.isLittleO_iff.2 fun c hc => ?_)
  filter_upwards [ball_mem_nhds x hr0, hgauge.eventually (gt_mem_nhds hc)] with y hy hyc
  have happ : Tendsto (fun m => fderiv ℝ (v m) x (y - x)) l (𝓝 (A (y - x))) :=
    ((ContinuousLinearMap.apply ℝ F (y - x)).continuous.tendsto A).comp hA
  have hlim := ((hD.tendsto_at (hrU hy)).sub (hD.tendsto_at hx)).sub happ
  have hTaylor := le_of_tendsto hlim.norm
    ((hv.and hhol).mono fun m hm =>
      (hm.2.mono hrU).norm_sub_fderiv_le_of_mem_ball (hm.1.mono hrU) hy)
  exact hTaylor.trans (mul_le_mul_of_nonneg_right hyc.le (norm_nonneg _))

variable [CompleteSpace F]

/-- Eventual differentiability and uniform Hölder control of the derivatives upgrade locally
uniform function convergence on an open set to pointwise convergence of the derivatives.
No global norm bound is needed. -/
theorem tendsto_fderiv_of_tendstoLocallyUniformlyOn_of_holderOnWith
    (hα : 0 < α) (hU : IsOpen U) (hv : ∀ᶠ m in l, DifferentiableOn ℝ (v m) U)
    (hD : TendstoLocallyUniformlyOn v f l U)
    (hhol : ∀ᶠ m in l, HolderOnWith K α (fderiv ℝ (v m)) U) {x : E} (hx : x ∈ U) :
    Tendsto (fun m => fderiv ℝ (v m) x) l (𝓝 (fderiv ℝ f x)) := by
  have hc := cauchy_map_fderiv_of_tendstoLocallyUniformlyOn hα hU hv hD hhol x hx
  obtain ⟨A, hA⟩ := cauchy_map_iff_exists_tendsto.1 hc
  have hderiv := hasFDerivAt_of_tendsto_fderiv_of_tendstoLocallyUniformlyOn
    hα hU hv hD hhol hx hA
  rw [hderiv.fderiv]
  exact hA

/-- A locally uniform limit of functions that are eventually differentiable with uniformly Hölder
derivatives on an open set is C¹ and inherits that bound, without a global derivative norm bound. -/
theorem contDiffOn_one_and_holderOnWith_fderiv_of_tendstoLocallyUniformlyOn
    (hα : 0 < α) (hU : IsOpen U) (hv : ∀ᶠ m in l, DifferentiableOn ℝ (v m) U)
    (hD : TendstoLocallyUniformlyOn v f l U)
    (hhol : ∀ᶠ m in l, HolderOnWith K α (fderiv ℝ (v m)) U) :
    ContDiffOn ℝ 1 f U ∧ HolderOnWith K α (fderiv ℝ f) U := by
  have hlim (x : E) (hx : x ∈ U) :=
    tendsto_fderiv_of_tendstoLocallyUniformlyOn_of_holderOnWith hα hU hv hD hhol hx
  have hH : HolderOnWith K α (fderiv ℝ f) U := by
    refine HolderOnWith.of_dist_le fun x hx y hy => ?_
    exact le_of_tendsto ((hlim x hx).dist (hlim y hy))
      (hhol.mono fun m hm => hm.dist_le hx hy)
  refine ⟨?_, hH⟩
  apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) hU).2
  refine ⟨fun x hx => ?_, by simp, ?_⟩
  · exact (hasFDerivAt_of_tendsto_fderiv_of_tendstoLocallyUniformlyOn
      hα hU hv hD hhol hx (hlim x hx)).differentiableAt.differentiableWithinAt
  · simpa only [contDiffOn_zero] using hH.continuousOn hα

/-- A derivative norm bound at one point that holds eventually along the filter passes to
the locally uniform limit there, when the derivatives have a common positive Hölder exponent. -/
theorem norm_fderiv_le_of_tendstoLocallyUniformlyOn_of_holderOnWith
    (hα : 0 < α) (hU : IsOpen U) (hv : ∀ᶠ m in l, DifferentiableOn ℝ (v m) U)
    (hD : TendstoLocallyUniformlyOn v f l U)
    (hhol : ∀ᶠ m in l, HolderOnWith K α (fderiv ℝ (v m)) U) {M : ℝ} {x : E}
    (hbound : ∀ᶠ m in l, ‖fderiv ℝ (v m) x‖ ≤ M) (hx : x ∈ U) :
    ‖fderiv ℝ f x‖ ≤ M :=
  le_of_tendsto
    (tendsto_fderiv_of_tendstoLocallyUniformlyOn_of_holderOnWith hα hU hv hD hhol hx).norm
    hbound

/-- A differentiable function is C² with Hölder second derivative when its derivative is a
locally uniform limit of eventually differentiable linear-map-valued fields with a common
derivative Hölder bound. The fields need not themselves be derivatives of other functions. -/
theorem contDiffOn_two_and_holderOnWith_fderiv_fderiv_of_tendstoLocallyUniformlyOn
    {g : ι → E → E →L[ℝ] F}
    (hα : 0 < α) (hU : IsOpen U) (hv : ∀ᶠ m in l, DifferentiableOn ℝ (g m) U)
    (hf : DifferentiableOn ℝ f U)
    (hD : TendstoLocallyUniformlyOn g (fderiv ℝ f) l U)
    (hhol : ∀ᶠ m in l, HolderOnWith K α (fderiv ℝ (g m)) U) :
    ContDiffOn ℝ 2 f U ∧ HolderOnWith K α (fderiv ℝ (fderiv ℝ f)) U := by
  obtain ⟨hC, hK⟩ := contDiffOn_one_and_holderOnWith_fderiv_of_tendstoLocallyUniformlyOn
    hα hU hv hD hhol
  exact ⟨(contDiffOn_succ_iff_fderiv_of_isOpen (n := 1) hU).2 ⟨hf, by simp, hC⟩, hK⟩

end FirstDerivative

end TauCeti
