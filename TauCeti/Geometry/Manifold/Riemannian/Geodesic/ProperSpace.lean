/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Completeness

/-!
# Properness from an everywhere-defined minimizing exponential map

The Riemannian distance from `p` to `exp_p v` is at most `‖v‖` (`dist_riemannianExp_le`), so
`exp_p` maps the closed ball of radius `r` in `T_p M` into the closed ball of radius `r` about `p`.
Suppose in addition that every point `q` of the latter ball is reached from `p` by a *minimizing*
initial velocity, one with `exp_p v = q` and `‖v‖ ≤ dist p q` (equality then follows from the
distance bound).  The closed ball of radius `r` about `p` is then exactly the image under `exp_p`
of the closed ball of radius `r` in `T_p M`.  When moreover `exp_p` is defined on all of `T_p M`,
it is continuous there, so each closed ball about `p` is the continuous image of a compact ball of
the finite-dimensional tangent space and is compact; the closed balls about other points are closed
subsets of these, and the manifold is a proper metric space.

This is the step from assertions (a) and (f) to assertion (b) of do Carmo's Hopf–Rinow theorem,
in a Riemannian manifold whose ambient distance is the Riemannian one.  Existence of minimizing
initial velocities is a hypothesis of these results, not a consequence of the distance bound, and
properness does not follow from it alone: continuity of `exp_p` on the whole tangent space, that
is assertion (a), is what makes the closed balls compact.  Metric completeness then follows from
Mathlib's `complete_of_proper`.

## Main results

In the namespace `TauCeti.Manifold`:

* `image_riemannianExp_closedBall_subset`: `exp_p` maps the closed tangent ball of radius `r` into
  the closed ball of radius `r` about `p`.
* `closedBall_eq_image_riemannianExp`: with minimizing initial velocities, the closed ball of
  radius `r` about `p` is the image of the closed tangent ball of radius `r`.
* `isCompact_closedBall_of_expDomain_eq_univ_of_exists_riemannianExp_eq_and_norm_le_dist`: it is
  compact when moreover `exp_p` is everywhere defined.
* `properSpace_of_expDomain_eq_univ_of_exists_riemannianExp_eq_and_norm_le_dist`: **an
  everywhere-defined exponential map with minimizing initial velocities makes the manifold
  proper.**

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §2, Thm. 2.8, the implication
  from assertions (a) and (f) to assertion (b).
* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Ch. 6, Thm. 6.19.
-/

public section

open Bundle Filter Manifold Metric Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [T2Space (TangentBundle I M)] [IsRiemannianManifold I M]

/-! ### Closed balls as images of tangent balls

The results with a minimizing hypothesis assume that every point `q` of the closed ball of radius
`r` about `p` is reached from `p` by a *minimizing initial velocity*: a tangent vector `v` with
`exp_p v = q` and `‖v‖ ≤ dist p q`, so that `‖v‖ = dist p q` by `dist_riemannianExp_le`.  This is
assertion (f) of the Hopf–Rinow theorem at the base point `p`, read on the initial velocities of
the minimizing geodesics. -/

/-- The exponential map sends the closed tangent ball of radius `r` into the closed ball of
radius `r` about the base point. -/
theorem image_riemannianExp_closedBall_subset (p : M) (r : ℝ) :
    riemannianExp I M p '' closedBall 0 r ⊆ closedBall p r := by
  rintro _ ⟨v, hv, rfl⟩
  rw [mem_closedBall, dist_comm]
  exact (dist_riemannianExp_le p v).trans (mem_closedBall_zero_iff.1 hv)

variable {p : M} {r : ℝ}

omit [I.Boundaryless] [T2Space (TangentBundle I M)] [IsRiemannianManifold I M] in
/-- If every point of the closed ball of radius `r` about `p` is reached from `p` by a minimizing
initial velocity, that ball is contained in the image under `exp_p` of the closed tangent ball of
radius `r`. -/
theorem closedBall_subset_image_riemannianExp
    (hmin : ∀ q ∈ closedBall p r, ∃ v : TangentSpace I p,
      riemannianExp I M p v = q ∧ ‖v‖ ≤ dist p q) :
    closedBall p r ⊆ riemannianExp I M p '' closedBall 0 r := by
  intro q hq
  obtain ⟨v, hvq, hv⟩ := hmin q hq
  exact ⟨v, mem_closedBall_zero_iff.2 (hv.trans (dist_comm p q ▸ mem_closedBall.1 hq)), hvq⟩

/-- **Closed balls are exponential images of tangent balls.**  If every point of the closed ball
of radius `r` about `p` is reached from `p` by a minimizing initial velocity, that ball is the
image under `exp_p` of the closed tangent ball of radius `r`.  No injectivity of `exp_p` on that
ball is asserted. -/
theorem closedBall_eq_image_riemannianExp
    (hmin : ∀ q ∈ closedBall p r, ∃ v : TangentSpace I p,
      riemannianExp I M p v = q ∧ ‖v‖ ≤ dist p q) :
    closedBall p r = riemannianExp I M p '' closedBall 0 r :=
  (closedBall_subset_image_riemannianExp hmin).antisymm
    (image_riemannianExp_closedBall_subset p r)

/-! ### Properness -/

/-- If the exponential map at `p` is defined on all of `T_p M` and every point of the closed ball
of radius `r` about `p` is reached from `p` by a minimizing initial velocity, that ball is
compact. -/
theorem isCompact_closedBall_of_expDomain_eq_univ_of_exists_riemannianExp_eq_and_norm_le_dist
    (ha : expDomain I M p = univ)
    (hmin : ∀ q ∈ closedBall p r, ∃ v : TangentSpace I p,
      riemannianExp I M p v = q ∧ ‖v‖ ≤ dist p q) :
    IsCompact (closedBall p r) := by
  have : FiniteDimensional ℝ (TangentSpace I p) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) p
  rw [closedBall_eq_image_riemannianExp hmin]
  exact (isCompact_closedBall (0 : TangentSpace I p) r).image_of_continuousOn
    ((continuousOn_riemannianExp (I := I) (M := M) p).mono (ha ▸ subset_univ _))

/-- **An everywhere-defined exponential map with minimizing initial velocities makes the manifold
proper.**  If `exp_p` is defined on all of `T_p M` and every point is reached from `p` by a
minimizing initial velocity, then every closed bounded subset of `M` is compact.  This is the
implication from assertions (a) and (f) to assertion (b) of do Carmo's Hopf–Rinow theorem; metric
completeness of `M` follows by `complete_of_proper`. -/
theorem properSpace_of_expDomain_eq_univ_of_exists_riemannianExp_eq_and_norm_le_dist
    (ha : expDomain I M p = univ)
    (hmin : ∀ q : M, ∃ v : TangentSpace I p, riemannianExp I M p v = q ∧ ‖v‖ ≤ dist p q) :
    ProperSpace M :=
  ProperSpace.of_seq_closedBall (x := p) (r := fun n : ℕ ↦ (n : ℝ)) tendsto_natCast_atTop_atTop
    (Eventually.of_forall fun n ↦
      isCompact_closedBall_of_expDomain_eq_univ_of_exists_riemannianExp_eq_and_norm_le_dist
        (r := n) ha fun q _ ↦ hmin q)

end TauCeti.Manifold

end
