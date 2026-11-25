/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Hessian.Eikonal
import TauCeti.Geometry.Manifold.Riemannian.Hessian.ChainRule
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
(`TauCeti.Manifold.hessian_dist_sq_self`), so it is `2 g` up to an error `O(d)`, uniformly in
the tangent vectors (`TauCeti.Manifold.exists_abs_hessian_dist_sq_sub_le`). Since
`Hess d² = 2 d Hess d + 2 dd ⊗ dd`, this gives `Hess d = (g - dd ⊗ dd) / d + O(1)` on the
punctured ball. On the tangent space of the geodesic sphere of radius `ρ = d(p, q)` through
`q`, the orthogonal complement of `grad d`, the Hessian of `d` is thus `g / ρ + O(1)`, with a
constant independent of `ρ`. Since the second fundamental form of that sphere with respect to its
outward unit normal `grad d` is minus the restriction of `Hess d` (an identification not
formalized here), this is the estimate that all principal curvatures of small geodesic spheres are
`-1 / ρ + O(1)`, the case of a point in the tube estimates for the Gromov–Lawson surgery
construction.

## Main results

* `TauCeti.Manifold.IsNormalDomain.hessian_dist_mgradient_eq_zero`: the radial direction lies
  in the kernel of the Hessian of the distance on a metric normal ball.
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
  · simp [I.hessian_eq_inner_leviCivitaConnection_mgradient]
  apply hessian_mgradient_eq_zero_of_eventually_norm_sq_eq_const
    ((h.contMDiffAt_dist hU hq hne).of_le (by simp)) (c := 1)
  have hq' : q ∈ Metric.ball p r \ {p} := ⟨hq, hne⟩
  filter_upwards [(isOpen_ball.sdiff isClosed_singleton).mem_nhds hq'] with x hx
  rw [h.norm_mgradient_dist hU hx.1 hx.2, one_pow]

end IsNormalDomain

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
