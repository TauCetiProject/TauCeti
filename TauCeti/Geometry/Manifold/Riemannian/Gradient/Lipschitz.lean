/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.ContMDiff.Defs
import TauCeti.Geometry.Manifold.Riemannian.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Convex.Topology

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
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
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
  have hnormU : ContinuousOn (fun q ↦ ‖TauCeti.Manifold.curveVelocity I γ q‖) U :=
    (hCU.continuousOn_norm_mfderiv (le_refl _) hU (1 : ℝ)).congr
      (fun q _ ↦ congrArg norm (TauCeti.Manifold.curveVelocity_apply (I := I) (γ := γ) (t := q)))
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
    TauCeti.Manifold.exists_contMDiffAt_curveVelocity_eq (I := I) (n := 1) le_rfl x w (0 : ℝ)
  have hgγ : MDifferentiableAt I 𝓘(ℝ, F) f (γ 0) := by simpa only [hγ₀] using hg
  have hd := TauCeti.Manifold.hasDerivAt_comp_curve hgγ
    (TauCeti.Manifold.hasMFDerivAt_curveVelocity (hγ.mdifferentiableAt one_ne_zero))
  have hd' : HasDerivAt (f ∘ γ) (mvfderiv I f x w) 0 := by
    apply hd.congr_deriv
    rw [hw]
    exact congrArg (fun p : M ↦ mvfderiv I f p (show TangentSpace I p from w)) hγ₀
  have hvelnorm : ‖TauCeti.Manifold.curveVelocity I γ 0‖ = ‖w‖ := by
    have hb := congrArg (fun p : M ↦
      ‖(show TangentSpace I p from TauCeti.Manifold.curveVelocity I γ 0)‖) hγ₀
    exact hb.trans (congrArg (fun z : TangentSpace I x ↦ ‖z‖) hw)
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

