/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Hessian.Eikonal
import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Distortion
import TauCeti.Geometry.Manifold.Riemannian.Hessian.ChainRule
import TauCeti.Geometry.Manifold.Riemannian.Hessian.Regularity
import TauCeti.Geometry.Manifold.Riemannian.Hessian.SquaredDistance

/-!
# The Hessian of the distance on a normal ball

On a metric normal ball the distance from the centre is smooth away from the centre, and its
gradient is the unit radial velocity. These first-order results are developed in
`TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance`. The constant norm of the gradient
implies that the Hessian of the distance vanishes in the radial direction. At the centre the
gradient vanishes, so the radial Hessian also vanishes there. Completeness is not assumed.

Near the centre `p` the Hessian of `d = d(p, ·)` is also controlled in the other directions. The
Hessian of `d²` is smooth across `p`, where it equals `2 g_p`
(`TauCeti.Manifold.hessian_dist_sq_self`). Read in normal coordinates it is therefore `2 g` up to
an error `O(d)`, uniformly in the tangent vectors. Since `Hess d² = 2 d Hess d + 2 dd ⊗ dd`, this
gives `Hess d = (g - dd ⊗ dd) / d + O(1)` on the punctured ball. On the tangent space of the
geodesic sphere of radius `ρ = d(p, q)` through `q`, the orthogonal complement of `grad d`, the
Hessian of `d` is thus `g / ρ + O(1)`, with a constant independent of `ρ`. Since the second
fundamental form of that sphere with respect to its outward unit normal `grad d` is minus the
restriction of `Hess d` (an identification not formalized here), this is the estimate that all
principal curvatures of small geodesic spheres are `-1 / ρ + O(1)`, the case of a point in the
tube estimates for the Gromov–Lawson surgery construction.

## Main results

* `TauCeti.Manifold.IsNormalDomain.hessian_dist_mgradient_eq_zero`: the radial direction lies
  in the kernel of the Hessian of the distance on a metric normal ball.
* `TauCeti.Manifold.exists_abs_hessian_dist_sq_riemannianExp_sub_le`: pulled back along `exp_p`,
  the Hessian of `d²` is twice the exponential pullback metric up to `O(‖v‖)`.
* `TauCeti.Manifold.exists_abs_hessian_dist_sq_sub_le`: near `p`, `Hess d² = 2 g + O(d)`.
* `TauCeti.Manifold.exists_abs_hessian_dist_sub_le`: near `p` and off `p`,
  `Hess d = (g - dd ⊗ dd) / d + O(1)`.
* `TauCeti.Manifold.exists_abs_hessian_dist_sub_inner_div_le`: on vectors orthogonal to `grad d`,
  `Hess d = g / d + O(1)`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Springer, 2018, Chapters 6
  and 11.
* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive scalar
  curvature*, Ann. of Math. 111 (1980), 423–434, proof of Theorem A (the principal curvatures of
  small distance tubes).
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

namespace IsNormalDomain

/-- The radial direction, the gradient of the distance from the centre, lies in the kernel of the
Hessian of the distance on a metric normal ball. -/
theorem hessian_dist_mgradient_eq_zero (h : IsNormalDomain I M p U) (hU : Metric.ball 0 r ⊆ U)
    (hq : q ∈ Metric.ball p r) (w : TangentSpace I q) :
    hessian I (fun x ↦ dist p x) q (mgradient I (fun x ↦ dist p x) q) w = 0 := by
  rcases eq_or_ne q p with rfl | hne
  · simp [hessian_def]
  apply hessian_mgradient_eq_zero_of_eventually_norm_sq_eq_const
    ((h.contMDiffAt_dist hU hq hne).of_le (by simp)) (c := 1)
  have hq' : q ∈ Metric.ball p r \ {p} := ⟨hq, hne⟩
  filter_upwards [(isOpen_ball.sdiff isClosed_singleton).mem_nhds hq'] with x hx
  rw [h.norm_mgradient_dist hU hx.1 hx.2, one_pow]

end IsNormalDomain

/-- The defect `Hess d² - 2 g` of the squared distance from `p`, paired with the images of two
fixed vectors under `d exp_p` at `v`, is a `C¹` function of `v` near the origin. -/
private theorem contMDiffAt_hessian_dist_sq_riemannianExp_sub (p : M) (ξ ζ : TangentSpace I p) :
    ContMDiffAt 𝓘(ℝ, TangentSpace I p) 𝓘(ℝ) 1 (fun v ↦
      hessian I (fun x ↦ dist p x ^ 2) (riemannianExp I M p v)
          (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v ξ)
          (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v ζ) -
        2 * ⟪mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v ξ,
          mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v ζ⟫_ℝ) 0 := by
  obtain ⟨r₀, hr₀, hn⟩ := exists_isNormalDomain_ball (I := I) p
  have hexp := contMDiffOn_riemannianExp (I := I) (M := M) p
  have hdom := (isOpen_expDomain (I := I) (M := M) p).mem_nhds (zero_mem_expDomain p)
  have hP (ξ : TangentSpace I p) := (hexp.contMDiffOn_totalSpaceMk_mfderiv_apply (m := 1)
    (by simp) (isOpen_expDomain p) ξ).contMDiffAt hdom
  refine (contMDiffAt_hessian_pair (n := 1) (m := ∞) (k := ∞) (by simp) (by simp)
    isOpen_ball ((hn.contMDiffOn_dist_sq subset_rfl).of_le (by simp))
    (by simpa using hr₀) (hP ξ) (hP ζ)).sub (contMDiffAt_const.mul ?_)
  exact ((hexp.contDiffOn_inner_mfderiv (m := 1) (by simp) (isOpen_expDomain p) ξ
    ζ).contDiffAt hdom).contMDiffAt

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
  set L := fun v : TangentSpace I p ↦ mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v
  -- The defect `S v (ξ, ζ) = Hess f (L v ξ, L v ζ) - 2 ⟪L v ξ, L v ζ⟫`, as a bilinear form on the
  -- fixed space `T_p M`.
  let S : TangentSpace I p → TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ := fun v ↦
    (innerSL ℝ).bilinearComp
        ((CovariantDerivative.leviCivitaConnection I M (mgradient I f)
          (riemannianExp I M p v)).comp (L v)) (L v) -
      (2 : ℝ) • (innerSL ℝ).bilinearComp (L v) (L v)
  -- `S` unfolds to the defect: the Hessian is the pairing of `∇ grad f` with the metric.
  have hS (v ξ ζ : TangentSpace I p) : S v ξ ζ =
      hessian I f (riemannianExp I M p v) (L v ξ) (L v ζ) - 2 * ⟪L v ξ, L v ζ⟫_ℝ := by
    rw [hessian_def]
    rfl
  -- `S` is differentiable at the origin, where it vanishes since `Hess f_p = 2 g_p`.
  have hSd : DifferentiableAt ℝ S 0 := by
    have : ContMDiffAt 𝓘(ℝ, TangentSpace I p)
        𝓘(ℝ, TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ) 1 S 0 := by
      refine contMDiffAt_clm_apply.mpr fun ξ ↦ contMDiffAt_clm_apply.mpr fun ζ ↦ ?_
      rw [funext fun v ↦ hS v ξ ζ]
      exact contMDiffAt_hessian_dist_sq_riemannianExp_sub p ξ ζ
    exact contMDiffAt_iff_contDiffAt.mp this |>.differentiableAt (by simp)
  have hS0 : S 0 = 0 := by
    ext ξ ζ
    rw [hS]
    simp only [L, mfderiv_riemannianExp_apply_zero]
    rw [riemannianExp_zero]
    simp [f]
  obtain ⟨C, hC0, hC⟩ := hSd.isBigO_sub.exists_nonneg
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hC.bound
  refine ⟨r, hr, C, hC0, fun v hv ξ ζ ↦ ?_⟩
  have hSv := hball v hv
  rw [hS0, sub_zero, sub_zero] at hSv
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

/-- **The Hessian of the distance near the centre.** Away from `p` but near it, the Hessian of the
distance `d = d(p, ·)` is `(g - dd ⊗ dd) / d` up to a bounded error. This leading term is `g / d`
on the tangent space of the geodesic sphere through `q` and vanishes in the radial direction. -/
theorem exists_abs_hessian_dist_sub_le (p : M) :
    ∃ r > 0, ∃ C ≥ 0, ∀ q, q ≠ p → dist p q < r → ∀ v w : TangentSpace I q,
      |hessian I (fun x ↦ dist p x) q v w -
          (⟪v, w⟫_ℝ - mvfderiv I (fun x ↦ dist p x) q v * mvfderiv I (fun x ↦ dist p x) q w) /
            dist p q| ≤ C * ‖v‖ * ‖w‖ := by
  obtain ⟨r₀, hr₀, hn⟩ := exists_isNormalDomain_ball (I := I) p
  obtain ⟨r₁, hr₁, C, hC0, hC⟩ := exists_abs_hessian_dist_sq_sub_le (I := I) p
  refine ⟨min r₀ r₁, lt_min hr₀ hr₁, C / 2, by positivity, fun q hne hq v w ↦ ?_⟩
  have hd : 0 < dist p q := dist_pos.mpr hne.symm
  have hq₀ : q ∈ ball p r₀ := by
    rw [mem_ball, dist_comm]
    exact hq.trans_le (min_le_left _ _)
  have hsq := hessian_sq ((hn.contMDiffAt_dist subset_rfl hq₀ hne).of_le (by simp)) v w
  have hb := hC q (hq.trans_le (min_le_right _ _)) v w
  rw [hsq] at hb
  -- The defect for the distance is that for its square, divided by `2 d`.
  have heq : hessian I (fun x ↦ dist p x) q v w -
      (⟪v, w⟫_ℝ - mvfderiv I (fun x ↦ dist p x) q v * mvfderiv I (fun x ↦ dist p x) q w) /
        dist p q =
      (2 * mvfderiv I (fun x ↦ dist p x) q v * mvfderiv I (fun x ↦ dist p x) q w +
          2 * dist p q * hessian I (fun x ↦ dist p x) q v w - 2 * ⟪v, w⟫_ℝ) / (2 * dist p q) := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos (mul_pos two_pos hd), div_le_iff₀ (mul_pos two_pos hd)]
  calc _ ≤ C * dist p q * ‖v‖ * ‖w‖ := hb
    _ = C / 2 * ‖v‖ * ‖w‖ * (2 * dist p q) := by ring

/-- **The Hessian of the distance on small geodesic spheres.** On vectors orthogonal to the radial
direction `grad d`, that is, tangent to the geodesic sphere through `q` about `p`, the Hessian of
the distance `d = d(p, ·)` is `g / d` up to a bounded error. This is the form in which the
principal curvatures `-1 / d + O(1)` of small geodesic spheres enter (see the module docstring). -/
theorem exists_abs_hessian_dist_sub_inner_div_le (p : M) :
    ∃ r > 0, ∃ C ≥ 0, ∀ q, q ≠ p → dist p q < r → ∀ v w : TangentSpace I q,
      ⟪mgradient I (fun x ↦ dist p x) q, v⟫_ℝ = 0 →
        |hessian I (fun x ↦ dist p x) q v w - ⟪v, w⟫_ℝ / dist p q| ≤ C * ‖v‖ * ‖w‖ := by
  obtain ⟨r, hr, C, hC0, hC⟩ := exists_abs_hessian_dist_sub_le (I := I) p
  refine ⟨r, hr, C, hC0, fun q hne hq v w hv ↦ ?_⟩
  have hv' : mvfderiv I (fun x ↦ dist p x) q v = 0 := by
    rw [← inner_mgradient]
    exact hv
  simpa only [hv', zero_mul, sub_zero] using hC q hne hq v w

end TauCeti.Manifold
