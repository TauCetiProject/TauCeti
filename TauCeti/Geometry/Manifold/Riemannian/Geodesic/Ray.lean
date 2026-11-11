/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Minimizing

/-!
# Rays in complete noncompact Riemannian manifolds

A *ray* from `p` is a unit-speed geodesic `γ : [0, ∞) → M` with `γ 0 = p` that minimizes the
distance between any two of its points: `dist (γ s) (γ t) = |s - t|` for all `s, t ≥ 0`, so that
its restriction to `[0, ∞)` is an isometric embedding. This file proves that a complete
noncompact Riemannian manifold has a ray from every point.

The argument is the standard compactness argument. Call a tangent vector `v` at `p`
*minimizing* when `dist p (exp_p v) = ‖v‖`. The minimizing vectors form a closed set, since the
exponential map of a complete manifold is continuous on all of `T_p M`, and they are
star-shaped about `0`, since a subsegment of a minimizing segment is minimizing. A noncompact
proper space is unbounded, so for every `n` there is a minimizing vector of norm at least `n`,
the initial velocity of a minimizing segment to a point at distance at least `n`. The unit
vectors `u` with `n • u` minimizing therefore form a decreasing sequence of nonempty compact
subsets of the unit sphere of `T_p M`. A unit vector `u` in their intersection has `t • u`
minimizing for every `t ≥ 0`, and the geodesic `t ↦ exp_p (t • u)` is a ray.

## Main results

In the namespace `TauCeti.Manifold`:

* `isometry_riemannianExp_smul_of_forall_dist_eq`: if `‖u‖ = 1` and `t • u` is minimizing for
  every `t ≥ 0`, then `t ↦ exp_p (t • u)` is an isometric embedding of `[0, ∞)`.
* `exists_norm_eq_one_isometry_riemannianExp_smul`: in a complete noncompact Riemannian manifold
  there is such a unit vector at every point.
* `exists_isGeodesicCurveOn_isometry_domRestrict_Ici`: **rays exist**: in a complete noncompact
  Riemannian manifold, every point is the origin of a geodesic defined for all time whose
  restriction to `[0, ∞)` is an isometric embedding.

## References

* J. Cheeger and D. Gromoll, *The splitting theorem for manifolds of nonnegative Ricci
  curvature*, J. Differential Geometry 6 (1971), 119–128.
* P. Petersen, *Riemannian Geometry*, 3rd ed., Springer GTM 171 (2016), the construction of rays
  and lines for the splitting theorem.
-/

public section

open Bundle Manifold Metric Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] {p : M}

/-- **A radial geodesic that minimizes on every initial segment is a ray.** If `‖u‖ = 1` and
`dist p (exp_p (t • u)) = t` for every `t ≥ 0`, then `t ↦ exp_p (t • u)` is an isometric
embedding of `[0, ∞)`: `dist (exp_p (s • u)) (exp_p (t • u)) = |s - t|` for all `s, t ≥ 0`. -/
theorem isometry_riemannianExp_smul_of_forall_dist_eq {u : TangentSpace I p} (hu : ‖u‖ = 1)
    (h : ∀ t, 0 ≤ t → dist p (riemannianExp I M p (t • u)) = t) :
    Isometry (fun t : Ici (0 : ℝ) ↦ riemannianExp I M p ((t : ℝ) • u)) := by
  -- For `a > 0` the vector `a • u` is minimizing, so `exp_p (· • u)` is isometric on `[0, a]`.
  have key (a s t : ℝ) (ha : 0 < a) (hs : s ∈ Icc 0 a) (ht : t ∈ Icc 0 a) :
      dist (riemannianExp I M p (s • u)) (riemannianExp I M p (t • u)) = |s - t| := by
    have hnorm : ‖a • u‖ = a := by rw [norm_smul, hu, mul_one, Real.norm_of_nonneg ha.le]
    simpa [hu] using dist_riemannianExp_smul_riemannianExp_smul_of_mem_Icc (v := u)
      (by rw [hnorm, h a ha.le]) hs ht
  refine Isometry.of_dist_eq fun s t ↦ ?_
  -- Both times lie in `[0, a]` for `a = max s t + 1 > 0`.
  have hs : (s : ℝ) ≤ max s t + 1 := (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  have ht : (t : ℝ) ≤ max s t + 1 := (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
  rw [Subtype.dist_eq, Real.dist_eq]
  exact key _ _ _ ((mem_Ici.1 s.2).trans_lt ((le_max_left _ _).trans_lt (lt_add_one _)))
    ⟨s.2, hs⟩ ⟨t.2, ht⟩

/-- In a complete noncompact Riemannian manifold, every point `p` has a unit tangent vector `u`
such that `t ↦ exp_p (t • u)` is an isometric embedding of `[0, ∞)`. -/
theorem exists_norm_eq_one_isometry_riemannianExp_smul [CompleteSpace M] [NoncompactSpace M]
    (p : M) : ∃ u : TangentSpace I p, ‖u‖ = 1 ∧
      Isometry (fun t : Ici (0 : ℝ) ↦ riemannianExp I M p ((t : ℝ) • u)) := by
  have ha := expDomain_eq_univ_of_completeSpace (I := I) (M := M) p
  have : ProperSpace M := properSpace_of_completeSpace I
  have hS := isClosed_setOf_dist_riemannianExp_eq_norm ha
  -- The unit vectors `u` with `n • u` minimizing.
  set K : ℕ → Set (TangentSpace I p) := fun n ↦
    sphere 0 1 ∩ (fun u ↦ (n : ℝ) • u) ⁻¹' {v | dist p (riemannianExp I M p v) = ‖v‖} with hK
  have hKclosed (n : ℕ) : IsClosed (K n) :=
    isClosed_sphere.inter (hS.preimage (continuous_const_smul _))
  have hKmono (n : ℕ) : K (n + 1) ⊆ K n := by
    rintro u ⟨hu, hnu⟩
    exact ⟨hu, dist_riemannianExp_smul_eq_norm_of_le hnu (Nat.cast_nonneg n)
      (Nat.cast_le.2 n.le_succ)⟩
  -- A minimizing segment to a point at distance more than `n` gives an element of `K n`.
  have hKne (n : ℕ) : (K n).Nonempty := by
    obtain ⟨q, hq⟩ : ∃ q : M, (n : ℝ) < dist p q := by
      by_contra! hle
      exact noncompact_univ M ((isCompact_closedBall p n).of_isClosed_subset isClosed_univ
        fun q _ ↦ mem_closedBall'.2 (hle q))
    obtain ⟨w, hwq, hw⟩ := exists_riemannianExp_eq_and_norm_eq_dist ha q
    have hw0 : 0 < ‖w‖ := hw ▸ (Nat.cast_nonneg n).trans_lt hq
    refine ⟨‖w‖⁻¹ • w, by simp [norm_smul, hw0.ne'], ?_⟩
    have hw' : ‖w‖ • ‖w‖⁻¹ • w = w := smul_inv_smul₀ hw0.ne' w
    exact dist_riemannianExp_smul_eq_norm_of_le (by rw [hw', hwq, hw])
      (Nat.cast_nonneg n) (hw ▸ hq.le)
  obtain ⟨u, hu⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hKmono
    hKne ((isCompact_sphere 0 1).of_isClosed_subset (hKclosed 0) inter_subset_left) hKclosed
  rw [mem_iInter] at hu
  have hu1 : ‖u‖ = 1 := mem_sphere_zero_iff_norm.1 (hu 0).1
  refine ⟨u, hu1, isometry_riemannianExp_smul_of_forall_dist_eq hu1 fun t ht ↦ ?_⟩
  -- Every `t ≥ 0` is at most some `n` with `n • u` minimizing.
  obtain ⟨n, hn⟩ := exists_nat_ge t
  have hnorm : ‖t • u‖ = t := by rw [norm_smul, hu1, mul_one, Real.norm_of_nonneg ht]
  exact (dist_riemannianExp_smul_eq_norm_of_le (hu n).2 ht hn).trans hnorm

/-- **Rays exist.** In a complete noncompact Riemannian manifold, every point `p` is the origin of
a geodesic `γ`, defined for all time, whose restriction to `[0, ∞)` is an isometric embedding:
`dist (γ s) (γ t) = |s - t|` for all `s, t ≥ 0`. -/
theorem exists_isGeodesicCurveOn_isometry_domRestrict_Ici [CompleteSpace M] [NoncompactSpace M]
    (p : M) : ∃ γ : ℝ → M, IsGeodesicCurveOn I γ univ ∧ γ 0 = p ∧
      Isometry ((Ici (0 : ℝ)).domRestrict γ) := by
  obtain ⟨u, -, hiso⟩ := exists_norm_eq_one_isometry_riemannianExp_smul (I := I) p
  have hJ : geodesicInterval I M p u = univ := by
    rw [geodesicInterval_eq_preimage_expDomain, expDomain_eq_univ_of_completeSpace, preimage_univ]
  refine ⟨maximalGeodesic I M p u,
    hJ ▸ (isGeodesicCurveOnFrom_maximalGeodesic p u).isGeodesicCurveOn,
    maximalGeodesic_zero p u, ?_⟩
  convert hiso using 2 with t
  rw [domRestrict_apply, riemannianExp_smul]

end TauCeti.Manifold
