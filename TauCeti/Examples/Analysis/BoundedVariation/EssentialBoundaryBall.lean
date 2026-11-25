/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Ball
public import TauCeti.Analysis.Normed.Module.Ball.Punctured
public import TauCeti.Geometry.Euclidean.Volume.Sphere
public import TauCeti.MeasureTheory.Covering.EssentialBoundary.Ball

/-!
# Checks for Federer's theorem: the perimeter sees the essential boundary, not the frontier

In `ℝⁿ`, `n ≥ 1`, let `s` be the unit ball together with the points of rational coordinates
(`TauCeti.EuclideanSpace.rationalPoints`), a null dense set. Then:

* its perimeter is that of the ball, `P(s) = n ω_n` with `ω_n` the volume of the unit ball
  (`TauCeti.Examples.EssentialBoundaryBall.perimeter_ballUnionRational`);
* its essential boundary is the unit sphere (`TauCeti.essentialBoundary_ball_union_rational`),
  with `Hⁿ⁻¹ = n ω_n`, in accordance with `P(s) = Hⁿ⁻¹(∂ᵉs)`
  (`euclideanHausdorffMeasure_essentialBoundary_ballUnionRational`);
* its frontier is the complement of the open ball
  (`TauCeti.Examples.EssentialBoundaryBall.frontier_ballUnionRational`), of infinite `Hⁿ⁻¹`
  measure (`euclideanHausdorffMeasure_frontier_ballUnionRational`):
  the bound of the perimeter by the measure of the frontier holds and is far from equality.

Likewise the punctured ball has perimeter `n ω_n`
(`TauCeti.Examples.EssentialBoundaryBall.perimeter_ball_sdiff_singleton`), essential boundary the
sphere, and frontier the sphere with one extra point, its centre
(`TauCeti.frontier_ball_sdiff_singleton`).
-/

public section

noncomputable section

open Function MeasureTheory Metric Set
open scoped ENNReal

namespace TauCeti.Examples.EssentialBoundaryBall

variable {n : ℕ}

/-- The unit ball together with the points of rational coordinates. -/
abbrev ballUnionRational (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  ball 0 1 ∪ EuclideanSpace.rationalPoints n

/-- **The perimeter of the ball with the rational points** is that of the ball, `n ω_n`. -/
theorem perimeter_ballUnionRational [NeZero n] :
    perimeter volume ⊤ (ballUnionRational n) =
      n * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rw [perimeter_congr_ae (ae_restrict_of_ae (union_ae_eq_left_of_ae_eq_empty
    (ae_eq_empty.2 EuclideanSpace.volume_rationalPoints))), perimeter_ball one_pos]
  simp

/-- The essential boundary of the ball with the rational points is the unit sphere, of
`(n - 1)`-dimensional measure `n ω_n`, the perimeter. -/
theorem euclideanHausdorffMeasure_essentialBoundary_ballUnionRational [NeZero n] :
    μHE[n - 1] (essentialBoundary volume (ballUnionRational n)) =
      n * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rw [essentialBoundary_ball_union_rational one_ne_zero]
  simpa using euclideanHausdorffMeasure_sphere (0 : EuclideanSpace ℝ (Fin n)) one_pos

/-- The interior of the ball with the rational points is the open unit ball. -/
theorem interior_ballUnionRational [NeZero n] : interior (ballUnionRational n) = ball 0 1 :=
  ((interior_mono (union_subset_union_left _ ball_subset_closedBall)).trans_eq
    ((interior_union_isClosed_of_interior_empty isClosed_closedBall
      (Measure.interior_eq_empty_of_null EuclideanSpace.volume_rationalPoints)).trans
        (interior_closedBall 0 one_ne_zero))).antisymm
    (isOpen_ball.subset_interior_iff.2 subset_union_left)

/-- **The frontier of the ball with the rational points** is the complement of the open ball. -/
theorem frontier_ballUnionRational [NeZero n] : frontier (ballUnionRational n) = (ball 0 1)ᶜ := by
  rw [frontier, interior_ballUnionRational,
    (EuclideanSpace.dense_rationalPoints.mono subset_union_right).closure_eq,
    ← compl_eq_univ_sdiff]

/-- **The frontier of the ball with the rational points has infinite `Hⁿ⁻¹` measure**: it contains
the disjoint spheres of radii `1, 2, 3, …`, each of measure at least `n ω_n`. -/
theorem euclideanHausdorffMeasure_frontier_ballUnionRational [NeZero n] :
    μHE[n - 1] (frontier (ballUnionRational n)) = ∞ := by
  rw [frontier_ballUnionRational]
  have hsub : (⋃ k : ℕ, sphere (0 : EuclideanSpace ℝ (Fin n)) (k + 1)) ⊆ (ball 0 1)ᶜ :=
    iUnion_subset fun k z hz ↦ by
      rw [mem_sphere_zero_iff_norm] at hz
      rw [mem_compl_iff, mem_ball_zero_iff, hz, not_lt]
      linarith [k.cast_nonneg (α := ℝ)]
  have hdisj : Pairwise (Disjoint on fun k : ℕ ↦ sphere (0 : EuclideanSpace ℝ (Fin n)) (k + 1)) :=
    fun i j hij ↦ Set.disjoint_left.2 fun z hi hj ↦ hij <| by
      rw [mem_sphere_zero_iff_norm] at hi hj
      exact_mod_cast add_right_cancel (hi.symm.trans hj)
  have hpos : (0 : ℝ≥0∞) < n * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    ENNReal.mul_pos (by exact_mod_cast NeZero.ne n) (measure_ball_pos _ _ one_pos).ne'
  refine top_le_iff.1 ((?_ : ∞ ≤ _).trans (measure_mono hsub))
  rw [measure_iUnion hdisj fun _ ↦ isClosed_sphere.measurableSet,
    ← ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) hpos.ne']
  refine tsum_le_tsum fun k ↦ ?_
  have h := euclideanHausdorffMeasure_sphere (0 : EuclideanSpace ℝ (Fin n))
    (r := k + 1) (by positivity)
  rw [finrank_euclideanSpace_fin] at h
  rw [h]
  refine le_mul_of_one_le_right bot_le (one_le_pow₀ ?_)
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by linarith [k.cast_nonneg (α := ℝ)])

/-- The punctured ball has perimeter `n ω_n`, that of the ball. -/
theorem perimeter_ball_sdiff_singleton [NeZero n] :
    perimeter volume ⊤ (ball (0 : EuclideanSpace ℝ (Fin n)) 1 \ {0}) =
      n * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rw [perimeter_congr_ae (ae_restrict_of_ae (sdiff_null_ae_eq_self (measure_singleton _))),
    perimeter_ball one_pos]
  simp

-- The frontier of the punctured unit ball is the unit sphere together with the centre.
example [NeZero n] : frontier (ball (0 : EuclideanSpace ℝ (Fin n)) 1 \ {0}) = sphere 0 1 ∪ {0} :=
  frontier_ball_sdiff_singleton 0 one_pos

end TauCeti.Examples.EssentialBoundaryBall
