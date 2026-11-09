/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic
public import TauCeti.Geometry.Manifold.Riemannian.EVariationComparison

/-!
# Local distance in open Riemannian submanifolds

Let `U` be an open subset of a Riemannian manifold `M` whose distance is the Riemannian distance,
and give `U` the restricted metric. Restriction cannot decrease distances
(`TopologicalSpace.Opens.riemannianEDist_le_riemannianEDist_subtype`), and the converse holds
locally: if the ambient ball `B(p, r)` lies in `U` and `d(p, q) < r`, then the Riemannian distance
of `U` between `p` and `q` is `d(p, q)`. Indeed, an ambient curve from `p` to `q` of length less
than `r` stays in `B(p, r)`, so it is a curve in `U` of the same length. No completeness of `U`
or of `M` is used.

## Main results

* `TauCeti.Manifold.riemannianEDist_open_eq_edist_of_ball_subset`: the distance of `U` from `p`
  is the ambient distance on an ambient ball around `p` contained in `U`.
* `TauCeti.Manifold.eventually_riemannianEDist_open_eq_edist`: the distance of `U` from `p` is the
  ambient distance near `p`.
* `TauCeti.Manifold.exists_ball_riemannianEDist_open_eq_edist`: the distance of `U` is the
  ambient distance between any two points of a small ball around `p`.
-/

public noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open scoped Manifold Topology TauCeti

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

/-- If the ambient ball `B(p, r)` lies in the open set `U` and `d(p, q) < r`, then the Riemannian
distance of `U` between `p` and `q` is their ambient distance. -/
theorem riemannianEDist_open_eq_edist_of_ball_subset (U : Opens M) (p q : U) {r : ℝ}
    (hball : Metric.ball (p : M) r ⊆ U) (hq : dist (p : M) q < r) :
    riemannianEDist I p q = edist (p : M) q := by
  refine le_antisymm (le_of_forall_gt fun c hc ↦ ?_) ?_
  · have hdr : edist (p : M) q < ENNReal.ofReal r := by
      rw [edist_dist]
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt dist_nonneg hq)).2 hq
    have hnear : riemannianEDist I (p : M) q < min c (ENNReal.ofReal r) := by
      rw [← IsRiemannianManifold.out (I := I) (M := M)]
      exact lt_min hc hdr
    obtain ⟨γ, h0, h1, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hnear
    have hmap : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U := by
      intro t ht
      apply hball
      rw [Metric.mem_ball, ← ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt dist_nonneg hq),
        ← edist_dist, ← h0, edist_comm]
      exact ((eVariationOn.edist_le γ (x := 0) (y := t) (s := Icc 0 1) (by simp) ht).trans
        (eVariationOn_le_pathELength hγ)).trans_lt (lt_of_lt_of_le hlen (min_le_right _ _))
    let η : ℝ → U := fun t ↦ if ht : t ∈ Icc (0 : ℝ) 1 then ⟨γ t, hmap t ht⟩ else p
    have heq : EqOn ((Subtype.val : U → M) ∘ η) γ (Icc 0 1) := by
      intro t ht
      simp only [Function.comp_apply, η, ht, ↓reduceDIte]
    have hη : ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 1) := fun t ht ↦
      (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
        ((hγ t ht).congr_of_mem heq ht)
    have hη0 : η 0 = p := Subtype.ext ((heq (by simp : (0 : ℝ) ∈ Icc 0 1)).trans h0)
    have hη1 : η 1 = q := Subtype.ext ((heq (by simp : (1 : ℝ) ∈ Icc 0 1)).trans h1)
    have hηlen : pathELength I η 0 1 = pathELength I γ 0 1 := by
      rw [pathELength_subtypeVal_comp]
      exact pathELength_congr heq
    exact (riemannianEDist_le_pathELength hη hη0 hη1 zero_le_one).trans_lt
      (hηlen.trans_lt (lt_of_lt_of_le hlen (min_le_left _ _)))
  · rw [IsRiemannianManifold.out (I := I) (M := M)]
    exact U.riemannianEDist_le_riemannianEDist_subtype p q

/-- Near each point `p` of an open set `U`, the Riemannian distance of `U` from `p` is the ambient
distance, even when `U` is not complete. -/
theorem eventually_riemannianEDist_open_eq_edist (U : Opens M) (p : U) :
    ∀ᶠ q : U in 𝓝 p, riemannianEDist I p q = edist (p : M) q := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (U.isOpen.mem_nhds p.property)
  have hnear : ∀ᶠ q : U in 𝓝 p, dist (p : M) q < r :=
    (continuous_const.dist continuous_subtype_val).continuousAt.eventually
      (gt_mem_nhds (by simpa using hr))
  exact hnear.mono fun q hq ↦ riemannianEDist_open_eq_edist_of_ball_subset U p q hball hq

/-- Around each point `p` of an open set `U` there is a ball on which the Riemannian distance of
`U` between any two points is their ambient distance. -/
theorem exists_ball_riemannianEDist_open_eq_edist (U : Opens M) (p : U) :
    ∃ r > 0, ∀ x y : U, dist (x : M) p < r → dist (y : M) p < r →
      riemannianEDist I x y = edist (x : M) y := by
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (U.isOpen.mem_nhds p.property)
  refine ⟨R / 4, by positivity, fun x y hx hy ↦ ?_⟩
  have hsubset : Metric.ball (x : M) (R / 2) ⊆ U := by
    intro z hz
    apply hball
    rw [Metric.mem_ball]
    have htri := dist_triangle z (x : M) p
    have hzx : dist z (x : M) < R / 2 := hz
    linarith
  have hxy : dist (x : M) y < R / 2 := by
    have htri := dist_triangle (x : M) p (y : M)
    rw [dist_comm (p : M) (y : M)] at htri
    linarith
  exact riemannianEDist_open_eq_edist_of_ball_subset U x y hsubset hxy

end TauCeti.Manifold
