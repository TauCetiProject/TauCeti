/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Hessian.Eikonal
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The gradient of the distance on a normal ball

Let `U` be a normal domain at `p` containing the open tangent ball of radius `r`. On the metric
ball of radius `r` about `p`, the distance from `p` is the norm of the Riemannian logarithm, so it
is smooth away from `p`. By the Gauss lemma, its gradient at `exp_p v`, `v ≠ 0`, is the unit radial
velocity `‖v‖⁻¹ • d(exp_p)_v v`. In particular the gradient of the distance has unit norm away
from `p`, and the Hessian of the distance vanishes in the radial direction. Completeness is not
assumed.

## Main results

In the namespace `TauCeti.Manifold.IsNormalDomain`:

* `contMDiffAt_dist`: the distance from the centre is smooth away from the centre of a metric
  normal ball.
* `mvfderiv_dist_sq_riemannianExp`: the differential of the squared distance at `exp_p v` is
  `w ↦ 2 ⟪d(exp_p)_v v, w⟫`.
* `mgradient_dist_riemannianExp`: the gradient of the distance at `exp_p v` is the unit radial
  velocity `‖v‖⁻¹ • d(exp_p)_v v`.
* `norm_mgradient_dist`: the gradient of the distance has unit norm away from the centre.
* `hessian_dist_mgradient`: the radial direction lies in the kernel of the Hessian of the
  distance.

In the namespace `TauCeti.Manifold`:

* `mgradient_dist_self`: the gradient of the distance from `p` vanishes at `p`, where the distance
  is not differentiable unless the tangent space is trivial.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Springer, 2018, Chapters 6
  and 11.
-/

public section

open Bundle Filter Metric Set
open scoped ContDiff InnerProductSpace Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  {p q : M} {U : Set (TangentSpace I p)} {r : ℝ}

/-- The gradient of the distance from `p` vanishes at `p`: the distance is not differentiable
there unless the tangent space at `p` is trivial. -/
@[simp] theorem mgradient_dist_self (p : M) : mgradient I (fun x ↦ dist p x) p = 0 := by
  by_contra hne
  have hd : MDifferentiableAt I 𝓘(ℝ) (fun x ↦ dist p x) p := by
    by_contra hnd
    exact hne (mgradient_eq_zero_iff.2
      (by simp [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hnd]))
  set w := mgradient I (fun x ↦ dist p x) p
  obtain ⟨r, hr, h⟩ := exists_isNormalDomain_ball (I := I) p
  have hw : 0 < ‖w‖ := norm_pos_iff.2 hne
  have habs : (fun t : ℝ ↦ dist p (riemannianExp I M p (t • w))) =ᶠ[𝓝 0]
      fun t ↦ |t| * ‖w‖ := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, t • w ∈ Metric.ball 0 r :=
      ((continuous_id.smul continuous_const).tendsto' 0 0 (zero_smul ℝ w)).eventually
        (isOpen_ball.mem_nhds (mem_ball_self hr))
    filter_upwards [hmem] with t ht
    rw [h.dist_riemannianExp_eq_of_mem_ball subset_rfl ht, norm_smul, Real.norm_eq_abs]
  have hcomp : DifferentiableAt ℝ (fun t : ℝ ↦ dist p (riemannianExp I M p (t • w))) 0 := by
    have hexp := (contMDiffAt_riemannianExp_smul_zero p w).mdifferentiableAt (by simp)
    have hd' : MDifferentiableAt I 𝓘(ℝ) (fun x ↦ dist p x)
        (riemannianExp I M p ((0 : ℝ) • w)) := by
      rwa [zero_smul, riemannianExp_zero]
    exact mdifferentiableAt_iff_differentiableAt.1 (hd'.comp 0 hexp)
  have hmul : DifferentiableAt ℝ (fun t : ℝ ↦ |t| * ‖w‖ * ‖w‖⁻¹) 0 :=
    (habs.differentiableAt_iff.1 hcomp).mul_const _
  simp only [mul_assoc, mul_inv_cancel₀ hw.ne', mul_one] at hmul
  exact not_differentiableAt_abs_zero hmul

namespace IsNormalDomain

/-- The distance from the centre is smooth at each noncentral point of a metric normal ball. -/
theorem contMDiffAt_dist (h : IsNormalDomain I M p U) (hU : Metric.ball 0 r ⊆ U)
    (hq : q ∈ Metric.ball p r) (hne : q ≠ p) :
    ContMDiffAt I 𝓘(ℝ) ∞ (fun x ↦ dist p x) q := by
  have hq' : q ∈ riemannianExp I M p '' U := by
    apply image_mono hU
    rwa [h.image_riemannianExp_ball_eq_ball hU]
  have hlog := h.contMDiffOn_riemannianLog.contMDiffAt (h.isOpen_image.mem_nhds hq')
  have hzero : riemannianLog I M p U q ≠ 0 := by
    intro hz
    apply hne
    rw [← riemannianExp_riemannianLog hq', hz, riemannianExp_zero]
  apply ((contDiffAt_norm ℝ hzero).contMDiffAt.comp q hlog).congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds hq] with x hx
  exact h.dist_eq_norm_riemannianLog_of_mem_ball hU hx

/-- The differential of the squared distance from the centre of a metric normal ball at
`exp_p v` is dual to twice the radial velocity `d(exp_p)_v v`. -/
theorem mvfderiv_dist_sq_riemannianExp (h : IsNormalDomain I M p U)
    (hU : Metric.ball 0 r ⊆ U) {v : TangentSpace I p} (hv : v ∈ Metric.ball 0 r)
    (w : TangentSpace I (riemannianExp I M p v)) :
    mvfderiv I (fun x ↦ dist p x ^ 2) (riemannianExp I M p v) w =
      2 * ⟪mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v v, w⟫_ℝ := by
  have hvU := hU hv
  have hq : riemannianExp I M p v ∈ Metric.ball p r := by
    rw [mem_ball', h.dist_riemannianExp_eq_of_mem_ball hU hv]
    simpa only [mem_ball_zero_iff] using hv
  have heq : (fun x ↦ dist p x ^ 2) =ᶠ[𝓝 (riemannianExp I M p v)]
      (fun x ↦ ‖riemannianLog I M p U x‖ ^ 2) := by
    filter_upwards [isOpen_ball.mem_nhds hq] with x hx
    rw [h.dist_eq_norm_riemannianLog_of_mem_ball hU hx]
  rw [heq.mvfderiv_eq]
  have hi := DFunLike.congr_fun (h.mfderiv_riemannianExp_comp_mfderiv_riemannianLog hvU) w
  have hg := inner_mfderiv_riemannianExp_radial (I := I) (M := M) (p := p) (v := v)
    (h.subset_expDomain hvU)
    (w := mfderiv I 𝓘(ℝ, TangentSpace I p) (riemannianLog I M p U)
      (riemannianExp I M p v) w)
  change mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v
    (mfderiv I 𝓘(ℝ, TangentSpace I p) (riemannianLog I M p U)
      (riemannianExp I M p v) w) = w at hi
  rw [hi] at hg
  rw [show (fun x ↦ ‖riemannianLog I M p U x‖ ^ 2) =
      (fun z : TangentSpace I p ↦ ‖z‖ ^ 2) ∘ riemannianLog I M p U from rfl,
    mvfderiv_comp_apply_of_differentiableAt
      ((contDiff_norm_sq ℝ (n := ∞)).differentiable (by simp)).differentiableAt
      (h.mdifferentiableAt_riemannianLog (mem_image_of_mem _ hvU)),
    fderiv_norm_sq_apply, h.riemannianLog_riemannianExp hvU]
  simp only [two_smul, mvfderiv_apply_eq_mfderiv_apply, hg, two_mul]
  rfl

/-- The gradient of the distance from the centre of a metric normal ball at `exp_p v` is the
unit radial velocity `‖v‖⁻¹ • d(exp_p)_v v`. For `v = 0` both sides vanish. -/
theorem mgradient_dist_riemannianExp (h : IsNormalDomain I M p U)
    (hU : Metric.ball 0 r ⊆ U) {v : TangentSpace I p} (hv : v ∈ Metric.ball 0 r) :
    mgradient I (fun x ↦ dist p x) (riemannianExp I M p v) =
      ‖v‖⁻¹ • mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v v := by
  rcases eq_or_ne v 0 with rfl | hv0
  · rw [norm_zero, inv_zero, zero_smul]
    generalize hq : riemannianExp I M p 0 = q
    rw [riemannianExp_zero] at hq
    subst hq
    exact mgradient_dist_self p
  have hq : riemannianExp I M p v ∈ Metric.ball p r := by
    rw [mem_ball', h.dist_riemannianExp_eq_of_mem_ball hU hv]
    simpa only [mem_ball_zero_iff] using hv
  have hne : riemannianExp I M p v ≠ p := by
    intro heq
    have hdist := h.dist_riemannianExp_eq_of_mem_ball hU hv
    rw [heq, dist_self] at hdist
    exact hv0 (norm_eq_zero.1 hdist.symm)
  have hd := (h.contMDiffAt_dist hU hq hne).mdifferentiableAt (by simp)
  symm
  apply eq_mgradient_iff.2
  intro w
  have hm := DFunLike.congr_fun (mvfderiv_mul hd hd) w
  have hs := h.mvfderiv_dist_sq_riemannianExp hU hv w
  rw [show (fun x ↦ dist p x ^ 2) =
    (fun x ↦ dist p x) * (fun x ↦ dist p x) from funext fun x ↦ pow_two _] at hs
  rw [hm, h.dist_riemannianExp_eq_of_mem_ball hU hv] at hs
  simp only [add_apply, smul_apply, smul_eq_mul] at hs
  rw [real_inner_smul_left]
  apply mul_left_cancel₀ (norm_ne_zero_iff.2 hv0)
  rw [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 hv0), one_mul]
  linarith

/-- The gradient of the distance from the centre of a metric normal ball has unit norm away
from the centre. -/
theorem norm_mgradient_dist (h : IsNormalDomain I M p U) (hU : Metric.ball 0 r ⊆ U)
    (hq : q ∈ Metric.ball p r) (hne : q ≠ p) :
    ‖mgradient I (fun x ↦ dist p x) q‖ = 1 := by
  rw [← h.image_riemannianExp_ball_eq_ball hU] at hq
  obtain ⟨v, hv, rfl⟩ := hq
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hne (riemannianExp_zero p)
  rw [h.mgradient_dist_riemannianExp hU hv, norm_smul,
    norm_mfderiv_riemannianExp_radial (h.subset_expDomain (hU hv)), norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)]

/-- The radial direction, the gradient of the distance from the centre, lies in the kernel of the
Hessian of the distance on a metric normal ball. -/
theorem hessian_dist_mgradient (h : IsNormalDomain I M p U) (hU : Metric.ball 0 r ⊆ U)
    (hq : q ∈ Metric.ball p r) (w : TangentSpace I q) :
    hessian I (fun x ↦ dist p x) q (mgradient I (fun x ↦ dist p x) q) w = 0 := by
  rcases eq_or_ne q p with rfl | hne
  · simp [hessian_def]
  apply hessian_mgradient_eq_zero_of_eventually_norm_sq_eq_const
    ((h.contMDiffAt_dist hU hq hne).of_le (by simp)) (c := 1)
  filter_upwards [(isOpen_ball.sdiff isClosed_singleton).mem_nhds
    (show q ∈ Metric.ball p r \ {p} from ⟨hq, hne⟩)] with x hx
  rw [h.norm_mgradient_dist hU hx.1 hx.2, one_pow]

end IsNormalDomain

end TauCeti.Manifold
