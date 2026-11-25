/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Ball
public import TauCeti.Analysis.BoundedVariation.EssentialBoundary
public import TauCeti.Geometry.Euclidean.Volume.Sphere
public import TauCeti.MeasureTheory.Covering.EssentialBoundary.Ball

/-!
# Checks for Federer's theorem: the perimeter sees the essential boundary, not the frontier

In `ℝⁿ`, `n ≥ 1`, let `s` be the unit ball together with the points of rational coordinates, a
null dense set. Then:

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
(`TauCeti.Examples.EssentialBoundaryBall.frontier_ball_sdiff_singleton`).
-/

public section

noncomputable section

open Function MeasureTheory Metric Set
open scoped ENNReal

namespace TauCeti.Examples.EssentialBoundaryBall

variable {n : ℕ}

/-- The points of rational coordinates in `ℝⁿ`. -/
abbrev rationalPoints (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  range fun q : Fin n → ℚ ↦ WithLp.toLp 2 fun i ↦ (q i : ℝ)

/-- The unit ball together with the points of rational coordinates. -/
abbrev ballUnionRational (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  ball 0 1 ∪ rationalPoints n

/-- The points of rational coordinates form a null set, for `n ≠ 0`. -/
theorem volume_rationalPoints [NeZero n] : volume (rationalPoints n) = 0 := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) := ⟨⟨EuclideanSpace.single 0 1, 0, by simp⟩⟩
  exact (countable_range _).measure_zero _

/-- The points of rational coordinates are dense in `ℝⁿ`. -/
theorem dense_rationalPoints : Dense (rationalPoints n) := by
  have h : DenseRange fun q : Fin n → ℚ ↦ fun i ↦ (q i : ℝ) :=
    DenseRange.piMap fun _ ↦ Rat.denseRange_cast
  exact ((PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n ↦ ℝ).symm.surjective.denseRange.comp h
    (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n ↦ ℝ).symm.continuous)

/-- **The perimeter of the ball with the rational points** is that of the ball, `n ω_n`. -/
theorem perimeter_ballUnionRational [NeZero n] :
    perimeter volume ⊤ (ballUnionRational n) =
      n * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rw [perimeter_congr_ae (ae_restrict_of_ae (union_ae_eq_left_of_ae_eq_empty
    (ae_eq_empty.2 volume_rationalPoints))), perimeter_ball one_pos]
  simp

/-- The essential boundary of the ball with the rational points is the unit sphere, of
`(n - 1)`-dimensional measure `n ω_n`, the perimeter. -/
theorem euclideanHausdorffMeasure_essentialBoundary_ballUnionRational [NeZero n] :
    μHE[n - 1] (essentialBoundary volume (ballUnionRational n)) =
      n * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rw [essentialBoundary_ball_union_rational one_ne_zero]
  simpa using euclideanHausdorffMeasure_sphere (0 : EuclideanSpace ℝ (Fin n)) one_pos

/-- A point outside the open unit ball is not in the interior of the ball with the rational
points: near it there is a small ball outside the closed unit ball, of positive volume, which the
null set of rational points cannot cover. -/
private theorem interior_ballUnionRational_subset [NeZero n] :
    interior (ballUnionRational n) ⊆ ball 0 1 := by
  intro x hx
  by_contra hx1
  rw [mem_ball_zero_iff, not_lt] at hx1
  obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  have hx0 : ‖x‖ ≠ 0 := by linarith
  set y : EuclideanSpace ℝ (Fin n) := (1 + ε / 2 / ‖x‖) • x
  have hy : ‖y‖ = ‖x‖ + ε / 2 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), add_mul, one_mul,
      div_mul_cancel₀ _ hx0]
  have hyx : dist y x = ε / 2 := by
    rw [dist_eq_norm, show y - x = (ε / 2 / ‖x‖) • x by simp [y, add_smul], norm_smul,
      Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ hx0]
  have hsub : ball y (ε / 2) ⊆ rationalPoints n := by
    intro z hz
    have hzs : z ∈ ballUnionRational n :=
      interior_subset (hεs (by rw [mem_ball] at hz ⊢; linarith [dist_triangle z y x]))
    refine hzs.resolve_left fun hz1 ↦ ?_
    rw [mem_ball_zero_iff] at hz1
    rw [mem_ball, dist_eq_norm] at hz
    linarith [norm_sub_norm_le y z, norm_sub_rev y z]
  have := measure_mono (μ := volume) hsub
  rw [volume_rationalPoints, nonpos_iff_eq_zero] at this
  exact (measure_ball_pos volume y (by positivity)).ne' this

/-- The interior of the ball with the rational points is the open unit ball. -/
theorem interior_ballUnionRational [NeZero n] : interior (ballUnionRational n) = ball 0 1 :=
  interior_ballUnionRational_subset.antisymm (isOpen_ball.subset_interior_iff.2 subset_union_left)

/-- **The frontier of the ball with the rational points** is the complement of the open ball. -/
theorem frontier_ballUnionRational [NeZero n] : frontier (ballUnionRational n) = (ball 0 1)ᶜ := by
  rw [frontier, interior_ballUnionRational,
    (dense_rationalPoints.mono subset_union_right).closure_eq, ← compl_eq_univ_sdiff]

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
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    ⟨⟨EuclideanSpace.single 0 1, 0, by simp⟩⟩
  rw [perimeter_congr_ae (ae_restrict_of_ae (sdiff_null_ae_eq_self (measure_singleton _))),
    perimeter_ball one_pos]
  simp

/-- **The frontier of the punctured ball** is the sphere together with the centre. -/
theorem frontier_ball_sdiff_singleton [NeZero n] :
    frontier (ball (0 : EuclideanSpace ℝ (Fin n)) 1 \ {0}) = sphere 0 1 ∪ {0} := by
  have h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ closure (ball 0 1 \ {0}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    set t := min ε 1 / 2 with ht_def
    have ht : 0 < t := by positivity
    have ht1 : t < 1 := by have := min_le_right ε 1; linarith
    have htε : t < ε := by have := min_le_left ε 1; linarith
    refine ⟨t • EuclideanSpace.single 0 1, ⟨?_, ?_⟩, ?_⟩
    · simp [norm_smul, abs_of_pos ht, ht1]
    · simp [ht.ne']
    · simp [norm_smul, abs_of_pos ht, htε]
  have hcl : closure (ball (0 : EuclideanSpace ℝ (Fin n)) 1 \ {0}) = closedBall 0 1 := by
    refine (closure_minimal (sdiff_subset.trans ball_subset_closedBall)
      isClosed_closedBall).antisymm ?_
    rw [← closure_ball (0 : EuclideanSpace ℝ (Fin n)) one_ne_zero]
    refine closure_minimal (fun x hx ↦ ?_) isClosed_closure
    by_cases hx0 : x = 0
    · exact hx0 ▸ h0
    · exact subset_closure ⟨hx, hx0⟩
  rw [frontier, hcl, (isOpen_ball.sdiff isClosed_singleton).interior_eq, sdiff_sdiff_right,
    closedBall_sdiff_ball, inter_eq_right.2 (by simp)]

end TauCeti.Examples.EssentialBoundaryBall
