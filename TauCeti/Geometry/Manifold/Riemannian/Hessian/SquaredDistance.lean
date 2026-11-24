/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension
import TauCeti.Geometry.Manifold.MFDeriv.Inner
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Distortion
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Expansion
import TauCeti.Geometry.Manifold.Riemannian.Hessian.NormSq
import TauCeti.Geometry.Manifold.Riemannian.Hessian.Regularity
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Squared distance on a normal ball

Let `U` be a normal domain at `p` containing the open tangent ball of radius `r`. On the metric
ball of radius `r > 0` about `p`, the distance from `p` is the norm of the Riemannian logarithm.
The logarithm is smooth across `p`, as is the squared norm on the tangent space, so the squared
distance `q ↦ dist p q ^ 2` is smooth on that ball. Since the logarithm vanishes
at `p` with identity differential there, and every point is the centre of such a ball, the
Hessian of the squared distance from any point `p` at `p` is twice the Riemannian metric.

Being smooth across `p`, the Hessian of the squared distance is therefore `2 g` up to an error
`O(d(p, q))` near `p`, uniformly in the tangent vectors. This is first proved in normal
coordinates, where the defect is a `C¹` family of bilinear forms on the fixed space `T_p M`
vanishing at the origin, and then transported to the manifold along `d log_p`.

## Main results

* `TauCeti.Manifold.hessian_dist_sq_self`: the Hessian of the squared distance from any point at
  that point is `2 g_p`.
* `TauCeti.Manifold.exists_abs_hessian_dist_sq_riemannianExp_sub_le`: pulled back along `exp_p`,
  the Hessian of `d²` is twice the exponential pullback metric up to `O(‖v‖)`.
* `TauCeti.Manifold.exists_abs_hessian_dist_sq_sub_le`: near `p`, `Hess d² = 2 g + O(d)`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Chs. 5–6 and 11.
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
  {p : M} {U : Set (TangentSpace I p)} {r : ℝ}

/-- The Hessian of the squared distance from `p` at `p` is twice the Riemannian inner product. -/
@[simp] theorem hessian_dist_sq_self (p : M) (v w : TangentSpace I p) :
    hessian I (fun q ↦ dist p q ^ 2) p v w = 2 * inner ℝ v w := by
  obtain ⟨r, hr, h⟩ := exists_isNormalDomain_ball (I := I) p
  have hlog : ContMDiffAt I 𝓘(ℝ, TangentSpace I p) 2 (riemannianLog I M p (Metric.ball 0 r)) p :=
    (h.contMDiffOn_riemannianLog.contMDiffAt
      (h.isOpen_image.mem_nhds h.self_mem_image)).of_le (by simp)
  have heq := h.dist_sq_eventuallyEq_norm_riemannianLog_sq subset_rfl hr
  have hdist : ContMDiffAt I 𝓘(ℝ) 2 (fun q ↦ dist p q ^ 2) p :=
    (contMDiffAt_dist_sq_self p).of_le (by simp)
  have hnorm : ContMDiffAt I 𝓘(ℝ) 2
      (fun q ↦ ‖riemannianLog I M p (Metric.ball 0 r) q‖ ^ 2) p :=
    (contDiff_norm_sq ℝ).contDiffAt.contMDiffAt.comp p hlog
  have hcrit := mvfderiv_norm_sq_comp_eq_zero_of_eq_zero (hlog.mdifferentiableAt (by simp))
    h.riemannianLog_self
  rw [hessian_eq_criticalHessian hdist BoundarylessManifold.isInteriorPoint
      (mvfderiv_dist_sq_self p),
    criticalHessian_congr_of_eventuallyEq heq,
    ← hessian_eq_criticalHessian hnorm BoundarylessManifold.isInteriorPoint hcrit,
    hessian_norm_sq_comp_of_eq_zero hlog BoundarylessManifold.isInteriorPoint
      h.riemannianLog_self]
  simp only [h.mvfderiv_riemannianLog_self, ContinuousLinearMap.id_apply]

/-- The Hessian of the squared distance from `p`, paired with the images of two fixed vectors under
`d exp_p` at `v`, is a `C¹` function of `v` near the origin. -/
private theorem contMDiffAt_hessian_dist_sq_riemannianExp (p : M) (ξ ζ : TangentSpace I p) :
    ContMDiffAt 𝓘(ℝ, TangentSpace I p) 𝓘(ℝ) 1 (fun v ↦
      hessian I (fun x ↦ dist p x ^ 2) (riemannianExp I M p v)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v ξ)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v ζ)) 0 := by
  obtain ⟨r₀, hr₀, hn⟩ := exists_isNormalDomain_ball (I := I) p
  have hdom := (isOpen_expDomain (I := I) (M := M) p).mem_nhds (zero_mem_expDomain p)
  have hP (ξ : TangentSpace I p) := ((contMDiffOn_riemannianExp (I := I) (M := M)
    p).contMDiffOn_totalSpaceMk_mfderiv_apply (m := 1) (by simp) (isOpen_expDomain p)
      ξ).contMDiffAt hdom
  exact contMDiffAt_hessian_pair (n := 1) (m := ∞) (k := ∞) (by simp) (by simp)
    isOpen_ball ((hn.contMDiffOn_dist_sq subset_rfl).of_le (by simp))
    (by simpa using hr₀) (hP ξ) (hP ζ)

/-- **The Hessian of the squared distance in normal coordinates.** Pulled back along `exp_p`, the
Hessian of `q ↦ d(p, q)²` differs from twice the exponential pullback metric by `O(‖v‖)` near the
origin, uniformly in the tangent vectors. -/
theorem exists_abs_hessian_dist_sq_riemannianExp_sub_le (p : M) :
    ∃ r > 0, ∃ C ≥ 0, ∀ v ∈ ball (0 : TangentSpace I p) r, ∀ ξ ζ : TangentSpace I p,
      |hessian I (fun x ↦ dist p x ^ 2) (riemannianExp I M p v)
            (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v ξ)
            (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v ζ) -
          2 * ⟪mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v ξ,
            mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v ζ⟫_ℝ| ≤
        C * ‖v‖ * ‖ξ‖ * ‖ζ‖ := by
  -- Cache the norms on the dual and on bilinear forms of `T_p M`: nested synthesis of the norm on
  -- bilinear forms otherwise exceeds the default instance-search limits.
  let _ : NormedAddCommGroup (TangentSpace I p →L[ℝ] ℝ) := inferInstance
  let _ : NormedSpace ℝ (TangentSpace I p →L[ℝ] ℝ) := inferInstance
  let _ : NormedAddCommGroup (TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ) := inferInstance
  let _ : NormedSpace ℝ (TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ) := inferInstance
  set f : M → ℝ := fun x ↦ dist p x ^ 2
  set L : (v : TangentSpace I p) → TangentSpace I p →L[ℝ] TangentSpace I (riemannianExp I M p v) :=
    fun v ↦ mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v
  -- The defect `S v (ξ, ζ) = Hess f (L v ξ, L v ζ) - 2 ⟪L v ξ, L v ζ⟫`, as a bilinear form on the
  -- fixed space `T_p M`: the Hessian pairing `H` minus twice the exponential pullback metric.
  let H : TangentSpace I p → TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ := fun v ↦
    (innerSL ℝ).bilinearComp
      ((CovariantDerivative.leviCivitaConnection I M (mgradient I f)
        (riemannianExp I M p v)).comp (L v)) (L v)
  let S := fun v ↦ H v - (2 : ℝ) • riemannianExpPullbackMetric I M p v
  -- `H` unfolds to the Hessian pairing: the Hessian is the pairing of `∇ grad f` with the metric.
  have hH (v ξ ζ : TangentSpace I p) :
      H v ξ ζ = hessian I f (riemannianExp I M p v) (L v ξ) (L v ζ) := by
    simp only [H, I.hessian_eq_inner_leviCivitaConnection_mgradient,
      ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply, ContinuousLinearMap.comp_apply]
  have hP (v ξ ζ : TangentSpace I p) : riemannianExpPullbackMetric I M p v ξ ζ = ⟪L v ξ, L v ζ⟫_ℝ :=
    riemannianExpPullbackMetric_apply p v ξ ζ
  have hS (v ξ ζ : TangentSpace I p) : S v ξ ζ =
      hessian I f (riemannianExp I M p v) (L v ξ) (L v ζ) - 2 * ⟪L v ξ, L v ζ⟫_ℝ := by
    simp only [S, sub_apply, smul_apply, hH, hP, smul_eq_mul]
  -- `S` is differentiable at the origin, where it vanishes since `Hess f_p = 2 g_p`.
  have hSd : DifferentiableAt ℝ S 0 := by
    have hHd : ContDiffAt ℝ 1 H 0 := contMDiffAt_iff_contDiffAt.mp <|
      contMDiffAt_clm_apply.mpr fun ξ ↦ contMDiffAt_clm_apply.mpr fun ζ ↦ by
        rw [funext fun v ↦ hH v ξ ζ]; exact contMDiffAt_hessian_dist_sq_riemannianExp p ξ ζ
    exact (hHd.differentiableAt (by simp)).sub
      ((contDiffAt_riemannianExpPullbackMetric p).differentiableAt (by simp) |>.const_smul (2 : ℝ))
  have hS0 : S 0 = 0 := by
    ext ξ ζ
    have hL0 (ξ : TangentSpace I p) : L 0 ξ = ξ := mfderiv_riemannianExp_apply_zero p ξ
    simp only [S, sub_apply, smul_apply, hH, hL0, riemannianExpPullbackMetric_zero]
    rw [riemannianExp_zero, innerSL_apply_apply]
    simp [f]
  obtain ⟨C, hC0, hC⟩ := hSd.isBigO_sub.exists_nonneg
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hC.bound
  refine ⟨r, hr, C, hC0, fun v hv ξ ζ ↦ ?_⟩
  have hSv := hball v hv
  rw [hS0, sub_zero, sub_zero] at hSv
  -- Restate the goal through `L`, whose domain is typed as `T_p M`, to match `hS`.
  change |hessian I f (riemannianExp I M p v) (L v ξ) (L v ζ) - 2 * ⟪L v ξ, L v ζ⟫_ℝ| ≤ _
  rw [← hS, ← Real.norm_eq_abs]
  calc ‖S v ξ ζ‖ ≤ ‖S v‖ * ‖ξ‖ * ‖ζ‖ := (S v).le_opNorm₂ ξ ζ
    _ ≤ C * ‖v‖ * ‖ξ‖ * ‖ζ‖ := by gcongr

/-- **The Hessian of the squared distance near the centre.** Near `p`, the Hessian of
`q ↦ d(p, q)²` is twice the Riemannian metric up to an error `O(d(p, q))`, uniformly in the
tangent vectors. -/
theorem exists_abs_hessian_dist_sq_sub_le (p : M) :
    ∃ r > 0, ∃ C ≥ 0, ∀ q, dist p q < r → ∀ v w : TangentSpace I q,
      |hessian I (fun x ↦ dist p x ^ 2) q v w - 2 * ⟪v, w⟫_ℝ| ≤
        C * dist p q * ‖v‖ * ‖w‖ := by
  obtain ⟨r₀, hr₀, hn, -, hlog⟩ :=
    exists_isNormalDomain_ball_norm_mfderiv_bounds (I := I) p one_lt_two
  obtain ⟨r₁, hr₁, C, hC0, hC⟩ := exists_abs_hessian_dist_sq_riemannianExp_sub_le (I := I) p
  have hU : ball (0 : TangentSpace I p) (min r₀ r₁) ⊆ ball 0 r₀ :=
    ball_subset_ball (min_le_left _ _)
  refine ⟨min r₀ r₁, lt_min hr₀ hr₁, 4 * C, by positivity, fun q hq v' w' ↦ ?_⟩
  obtain ⟨v, hv, rfl⟩ := hn.mem_image_riemannianExp_ball hU hq
  rw [hn.dist_riemannianExp_eq_of_mem_ball hU hv]
  -- `v'` and `w'` are the images under `d exp_p` of `ℓ v'` and `ℓ w'`, where `ℓ = d log_p` at most
  -- doubles norms.
  set ℓ := mfderiv I 𝓘(ℝ, TangentSpace I p) (riemannianLog I M p (ball 0 r₀))
    (riemannianExp I M p v)
  have hexpℓ (y : TangentSpace I (riemannianExp I M p v)) :
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v (ℓ y) = y :=
    DFunLike.congr_fun (hn.mfderiv_riemannianExp_comp_mfderiv_riemannianLog (hU hv)) y
  have hℓ (y) : ‖ℓ y‖ ≤ 2 * ‖y‖ := (hlog _ (mem_image_of_mem _ (hU hv)) y).2
  have h := hC v (ball_subset_ball (min_le_right _ _) hv) (ℓ v') (ℓ w')
  rw [hexpℓ, hexpℓ] at h
  calc _ ≤ C * ‖v‖ * ‖ℓ v'‖ * ‖ℓ w'‖ := h
    _ ≤ C * ‖v‖ * (2 * ‖v'‖) * (2 * ‖w'‖) := by gcongr <;> exact hℓ _
    _ = _ := by ring

end TauCeti.Manifold
