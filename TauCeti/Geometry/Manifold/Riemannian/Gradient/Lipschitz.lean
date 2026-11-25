/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Defs
import TauCeti.Geometry.Manifold.Riemannian.ArcLength
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Differential bounds for Lipschitz functions on Riemannian manifolds

Let `M` be a Riemannian manifold whose distance is the Riemannian distance. Along a curve that is
`C¹` near `t`, the derivative of a `C`-Lipschitz map `f` is bounded by `C` times the Riemannian
speed: on a short interval around `t` the speed is below any `d` exceeding the speed at `t`, so
the curve is `d`-Lipschitz there. Every tangent vector of a boundaryless manifold is the velocity
of such a curve, so the differential of a `C`-Lipschitz map, and the Riemannian gradient of a
`C`-Lipschitz function, have norm at most `C` (both vanish where the map is not differentiable).
Only a `C¹` manifold and a continuous metric are used.

## Main results

* `LipschitzWith.norm_deriv_comp_le_mul_norm_curveVelocity`: `‖(f ∘ γ)'(t)‖ ≤ C ‖γ'(t)‖`.
* `LipschitzWith.norm_mvfderiv_le`: `‖df_x‖ ≤ C` for a `C`-Lipschitz map `f`.
* `LipschitzWith.norm_mgradient_le`: `‖∇g(x)‖ ≤ C` for a `C`-Lipschitz function `g`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Springer, 2018, Chapter 2
  (gradients) and Chapter 6 (the Riemannian distance).
-/

public section

open Bundle Filter Set
open scoped ContDiff NNReal Manifold Topology
namespace LipschitzWith

open TauCeti
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : M → F} {C : ℝ≥0} {γ : ℝ → M} {t : ℝ}
/-- Along a curve that is `C¹` near `t`, a `C`-Lipschitz map has derivative of norm at most `C`
times the Riemannian speed. -/
theorem norm_deriv_comp_le_mul_norm_curveVelocity (hf : LipschitzWith C f)
    (hγ : ContMDiffAt 𝓘(ℝ) I 1 γ t) :
    ‖deriv (f ∘ γ) t‖ ≤ C * ‖TauCeti.Manifold.curveVelocity I γ t‖ := by
  let U := {q | ContMDiffAt 𝓘(ℝ) I 1 γ q}
  have hU : IsOpen U := isOpen_setOfPred_contMDiffAt (by simp)
  have hCU : ContMDiffOn 𝓘(ℝ) I 1 γ U := fun q hq ↦ hq.contMDiffWithinAt
  have hnormU := hCU.continuousOn_norm_curveVelocity hU
  have hUevent : ∀ᶠ q in 𝓝 t, q ∈ U := hU.mem_nhds hγ
  have hnorm : ContinuousAt (fun q ↦ ‖TauCeti.Manifold.curveVelocity I γ q‖) t :=
    hnormU.continuousAt (hU.mem_nhds hγ)
  have hlim : Tendsto (fun d : ℝ ↦ (C : ℝ) * d)
      (𝓝[>] ‖TauCeti.Manifold.curveVelocity I γ t‖)
      (𝓝 ((C : ℝ) * ‖TauCeti.Manifold.curveVelocity I γ t‖)) :=
    (continuous_const.mul continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with d hd
  have hd' : ‖TauCeti.Manifold.curveVelocity I γ t‖ < d := hd
  have hdpos : 0 < d := (norm_nonneg (TauCeti.Manifold.curveVelocity I γ t)).trans_lt hd'
  have hspeed : ∀ᶠ q in 𝓝 t, ‖TauCeti.Manifold.curveVelocity I γ q‖ < d :=
    hnorm.eventually (gt_mem_nhds hd')
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hUevent.and hspeed)
  have hγLip : LipschitzOnWith (Real.toNNReal d) γ (Metric.ball t r) := by
    apply TauCeti.IsRiemannianManifold.lipschitzOnWith_of_norm_curveVelocity_le (I := I)
      (convex_ball t r).ordConnected
    · intro q hq
      exact (hball q hq).1
    · intro q hq
      rw [Real.coe_toNNReal d hdpos.le]
      exact (hball q hq).2.le
  have hb := norm_deriv_le_of_lipschitzOn (Metric.ball_mem_nhds t hr)
    (hf.comp_lipschitzOnWith hγLip)
  simpa only [NNReal.coe_mul, Real.coe_toNNReal d hdpos.le] using hb

variable [I.Boundaryless] {x : M}

/-- The differential of a `C`-Lipschitz map on a boundaryless Riemannian manifold has operator
norm at most `C` at every point (it is `0` where the map is not differentiable). -/
theorem norm_mvfderiv_le (hf : LipschitzWith C f) (x : M) : ‖mvfderiv I f x‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ C.coe_nonneg
  intro w
  by_cases hg : MDifferentiableAt I 𝓘(ℝ, F) f x
  swap
  · have h0 : mvfderiv I f x = 0 := by simp [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hg]
    rw [h0, zero_apply, norm_zero]
    positivity
  obtain ⟨γ, hγ₀, hγ, hw⟩ :=
    TauCeti.Manifold.exists_contMDiffAt_curveVelocity_eq (I := I) (n := 1) x
      BoundarylessManifold.isInteriorPoint w (0 : ℝ)
  subst hγ₀
  have hd := TauCeti.Manifold.hasDerivAt_comp_curve hg
    (TauCeti.Manifold.hasMFDerivAt_curveVelocity (hγ.mdifferentiableAt one_ne_zero))
  have hd' : HasDerivAt (f ∘ γ) (mvfderiv I f (γ 0) w) 0 :=
    hd.congr_deriv (by rw [hw])
  have hvelnorm : ‖TauCeti.Manifold.curveVelocity I γ 0‖ = ‖w‖ := congrArg norm hw
  have hn := hf.norm_deriv_comp_le_mul_norm_curveVelocity hγ
  rwa [hd'.deriv, hvelnorm] at hn

/-- The Riemannian gradient of a `C`-Lipschitz function on a boundaryless Riemannian manifold has
norm at most `C` at every point. -/
theorem norm_mgradient_le [FiniteDimensional ℝ E] {g : M → ℝ} (hf : LipschitzWith C g)
    (x : M) :
    ‖TauCeti.Manifold.mgradient I g x‖ ≤ C := by
  rw [TauCeti.Manifold.norm_mgradient_eq_norm_mvfderiv]
  exact hf.norm_mvfderiv_le x

end LipschitzWith

