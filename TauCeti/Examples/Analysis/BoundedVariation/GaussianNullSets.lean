/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Frontier
public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Examples.Analysis.BoundedVariation.GaussianPerimeterBall
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Checks: Gaussian perimeter ignores null sets, the frontier does not

In `ℝ²`, with `B` the open unit disc, of Gaussian perimeter `e^{−1/2}`
(`TauCeti.Examples.GaussianPerimeterBall.gaussianPerimeter_ball_fin_two`):

* Removing the origin leaves the Gaussian perimeter `e^{−1/2}`
  (`gaussianPerimeter_ball_diff_zero`) although the frontier gains the origin
  (`zero_mem_frontier_ball_diff_zero`).
* Adding the null set `A₀ = ℚ² ∖ B`, dense outside `B`, leaves the Gaussian perimeter `e^{−1/2}`
  (`gaussianPerimeter_ballAddRational`), while the closure becomes `ℝ²` and the interior stays
  `B`, so the frontier becomes `ℝ² ∖ B` (`frontier_ballAddRational`): the origin is not a
  frontier point and `(2, 0)` is.
* For that set the frontier bound `P_γ(U) ≤ γ^{n−1}(frontier U)` of §2.3 is `∞`
  (`setLIntegral_frontier_ballAddRational_eq_top`), so it is strict
  (`gaussianPerimeter_ballAddRational_lt_frontier`).
-/

open MeasureTheory Metric Set
open scoped ENNReal

public noncomputable section

namespace TauCeti.Examples.GaussianNullSets

/-- The Euclidean plane. -/
abbrev E2 : Type := EuclideanSpace ℝ (Fin 2)

/-- Sets that differ by a Lebesgue-null set have the same Gaussian perimeter. -/
private theorem gaussianPerimeter_congr_null {s t : Set E2} (h : volume (symmDiff s t) = 0) :
    gaussianPerimeter s = gaussianPerimeter t := by
  rw [gaussianPerimeter_def, gaussianPerimeter_def]
  exact weightedPerimeter_congr_ae (ae_restrict_of_ae (ae_eq_set.2
    ⟨measure_mono_null (subset_union_left) h, measure_mono_null (subset_union_right) h⟩))

/-! ### Removing the origin -/

/-- Removing the origin from the unit disc does not change its Gaussian perimeter. -/
theorem gaussianPerimeter_ball_diff_zero :
    gaussianPerimeter (ball (0 : E2) 1 \ {0}) = ENNReal.ofReal (Real.exp (-(1 / 2))) := by
  rw [← GaussianPerimeterBall.gaussianPerimeter_ball_fin_two]
  refine gaussianPerimeter_congr_null (measure_mono_null ?_ (measure_singleton (0 : E2)))
  rintro x (⟨⟨hb, -⟩, hnb⟩ | ⟨hb, hnb⟩)
  · exact absurd hb hnb
  · by_contra h
    exact hnb ⟨hb, h⟩

/-- The origin is a frontier point of the punctured disc. -/
theorem zero_mem_frontier_ball_diff_zero : (0 : E2) ∈ frontier (ball 0 1 \ {0}) := by
  refine ⟨?_, fun h => (interior_subset h).2 rfl⟩
  have := (dense_compl_singleton (0 : E2)).open_subset_closure_inter
    (isOpen_ball (x := (0 : E2)) (ε := 1)) (mem_ball_self one_pos)
  rwa [sdiff_eq]

/-! ### Adding a dense null set outside the disc -/

/-- The points of `ℝ²` with rational coordinates. -/
def rationalPoints : Set E2 :=
  range fun q : Fin 2 → ℚ => WithLp.toLp 2 fun i => (q i : ℝ)

theorem countable_rationalPoints : rationalPoints.Countable :=
  countable_range _

theorem dense_rationalPoints : Dense rationalPoints := by
  have h : DenseRange fun q : Fin 2 → ℚ => WithLp.toLp 2 fun i => (q i : ℝ) :=
    (WithLp.toLp_surjective 2).denseRange.comp
      (DenseRange.piMap fun _ => Rat.denseRange_cast) (PiLp.continuous_toLp 2 _)
  exact h

/-- The unit disc together with the rational points outside it. -/
def ballAddRational : Set E2 :=
  ball 0 1 ∪ (rationalPoints \ ball 0 1)

/-- Adding the rational points does not change the Gaussian perimeter of the disc. -/
theorem gaussianPerimeter_ballAddRational :
    gaussianPerimeter ballAddRational = ENNReal.ofReal (Real.exp (-(1 / 2))) := by
  rw [← GaussianPerimeterBall.gaussianPerimeter_ball_fin_two]
  refine gaussianPerimeter_congr_null (measure_mono_null ?_
    (countable_rationalPoints.measure_zero volume))
  rintro x (⟨hx, hx'⟩ | ⟨hx, hx'⟩)
  · rcases hx with hx | hx
    · exact absurd hx hx'
    · exact hx.1
  · exact absurd (Or.inl hx) hx'

/-- The interior of the disc with the rational points outside it is the open disc. -/
theorem interior_ballAddRational : interior ballAddRational = ball 0 1 := by
  refine subset_antisymm ?_ (interior_maximal subset_union_left isOpen_ball)
  calc interior ballAddRational ⊆ interior (closedBall 0 1 ∪ rationalPoints) :=
        interior_mono (union_subset_union ball_subset_closedBall sdiff_subset)
    _ = ball 0 1 := by
        rw [interior_union_isClosed_of_interior_empty isClosed_closedBall
          (Measure.interior_eq_empty_of_null (countable_rationalPoints.measure_zero volume)),
          interior_closedBall _ one_ne_zero]

/-- The disc with the rational points outside it is dense. -/
theorem closure_ballAddRational : closure ballAddRational = univ := by
  refine eq_univ_of_univ_subset ?_
  rw [← dense_rationalPoints.closure_eq]
  refine closure_mono fun x hx => ?_
  by_cases h : x ∈ ball (0 : E2) 1
  · exact Or.inl h
  · exact Or.inr ⟨hx, h⟩

/-- **The frontier jumps**: the frontier of the disc with the rational points outside it is the
complement of the open disc. -/
theorem frontier_ballAddRational : frontier ballAddRational = (ball (0 : E2) 1)ᶜ := by
  rw [frontier, closure_ballAddRational, interior_ballAddRational, compl_eq_univ_sdiff]

theorem zero_notMem_frontier_ballAddRational : (0 : E2) ∉ frontier ballAddRational := by
  rw [frontier_ballAddRational, notMem_compl_iff]
  exact mem_ball_self one_pos

theorem single_two_mem_frontier_ballAddRational :
    EuclideanSpace.single 0 2 ∈ frontier ballAddRational := by
  rw [frontier_ballAddRational, mem_compl_iff, mem_ball_zero_iff, PiLp.norm_single]
  norm_num

/-! ### The frontier bound is strict -/

/-- The weighted length `γ¹(frontier U)` of the frontier of the disc with the rational points
outside it is infinite. -/
theorem setLIntegral_frontier_ballAddRational_eq_top :
    ∫⁻ x in frontier ballAddRational ∩ (⊤ : TopologicalSpace.Opens E2),
      ENNReal.ofReal (Real.exp (-gaussianWeight E2 x)) ∂μHE[Module.finrank ℝ E2 - 1] = ∞ := by
  set c : E2 := EuclideanSpace.single 0 2
  set K : Set E2 := closedBall c (1 / 2)
  have hK : K ⊆ frontier ballAddRational ∩ (⊤ : TopologicalSpace.Opens E2) := by
    intro x hx
    refine ⟨?_, trivial⟩
    rw [frontier_ballAddRational, mem_compl_iff, mem_ball_zero_iff, not_lt]
    have hc : ‖c‖ = 2 := by simp [c, PiLp.norm_single]
    have := norm_sub_norm_le c x
    rw [mem_closedBall, dist_eq_norm] at hx
    linarith [norm_sub_rev x c]
  set m : ℝ := (2 * Real.pi) ^ (-((Module.finrank ℝ E2 : ℕ) : ℝ) / 2) * Real.exp (-(25 / 8))
  have hm : ∀ x ∈ K, ENNReal.ofReal m ≤ ENNReal.ofReal (Real.exp (-gaussianWeight E2 x)) := by
    intro x hx
    refine ENNReal.ofReal_le_ofReal ?_
    have hx' : ‖x‖ ≤ 5 / 2 := by
      have hc : ‖c‖ = 2 := by simp [c]
      rw [mem_closedBall, dist_eq_norm] at hx
      linarith [norm_le_norm_add_norm_sub' x c]
    rw [exp_neg_gaussianWeight_of_norm_eq rfl]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    nlinarith [norm_nonneg x]
  have hK1 : μHE[1] K = ∞ := by
    rcases Measure.euclideanHausdorffMeasure_zero_or_top (X := E2) one_lt_two K with h | h
    · have : (μHE[Module.finrank ℝ E2] : Measure E2) K ≠ 0 :=
        (Measure.measure_pos_of_nonempty_interior _ (by
          rw [interior_closedBall _ (by norm_num)]
          exact ⟨c, mem_ball_self (by norm_num)⟩)).ne'
      rw [finrank_euclideanSpace, Fintype.card_fin] at this
      exact absurd h this
    · exact h
  rw [finrank_euclideanSpace, Fintype.card_fin, eq_top_iff]
  calc ∞ = ENNReal.ofReal m * μHE[1] K := by
        rw [hK1, ENNReal.mul_top
          (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, m]; positivity)]
    _ = ∫⁻ _ in K, ENNReal.ofReal m ∂μHE[1] := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ x in K, ENNReal.ofReal (Real.exp (-gaussianWeight E2 x)) ∂μHE[1] :=
        setLIntegral_mono' isClosed_closedBall.measurableSet hm
    _ ≤ _ := lintegral_mono_set hK

/-- **The frontier bound is strict** for the disc with the rational points outside it. -/
theorem gaussianPerimeter_ballAddRational_lt_frontier :
    gaussianPerimeter ballAddRational <
      ∫⁻ x in frontier ballAddRational ∩ (⊤ : TopologicalSpace.Opens E2),
        ENNReal.ofReal (Real.exp (-gaussianWeight E2 x)) ∂μHE[Module.finrank ℝ E2 - 1] := by
  rw [setLIntegral_frontier_ballAddRational_eq_top, gaussianPerimeter_ballAddRational]
  exact ENNReal.ofReal_lt_top

end TauCeti.Examples.GaussianNullSets
