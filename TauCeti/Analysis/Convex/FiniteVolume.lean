/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Measure

/-!
# Convex sets of finite volume

A convex set with nonempty interior in a finite-dimensional real normed space has finite
Haar measure exactly when it is bounded. Consequently, a set of positive finite measure
which agrees almost everywhere with a convex set has a compact convex representative
with nonempty interior. No Borel measurability or closedness of the original set is needed.
This permits geometric arguments on compact convex sets to apply to essentially convex sets.

The boundedness argument uses `Convex.ofReal_dist_mul_pow_mul_addHaar_ball_le`, the
ball-and-point volume estimate. The representative is the closure of the convex set;
Mathlib's `Convex.addHaar_frontier` ensures that taking this closure changes only a null set.
-/

public section

open Set Metric MeasureTheory MeasureTheory.Measure Bornology
open Module (finrank)
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] {s : Set E}

/-- A convex set with nonempty interior has finite Haar measure if and only if it is bounded.
The interior hypothesis is essential: an unbounded proper subspace has zero ambient measure. -/
theorem isBounded_iff_measure_ne_top_of_convex (hs : Convex ℝ s)
    (hi : (interior s).Nonempty) : IsBounded s ↔ μ s ≠ ∞ := by
  refine ⟨fun hb ↦ hb.measure_lt_top.ne, fun hfin ↦ ?_⟩
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact (Set.toFinite s).isBounded
  obtain ⟨x, hx⟩ := hi
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx)
  have hunit : 0 < (μ (ball (0 : E) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 zero_lt_one).ne' measure_ball_ne_top
  have hcoeff : 0 < r ^ (finrank ℝ E - 1) * (μ (ball (0 : E) 1)).toReal :=
    mul_pos (pow_pos hr _) hunit
  refine (isBounded_iff_subset_closedBall x).2
    ⟨(2 ^ (finrank ℝ E + 1) * (μ s).toReal) /
      (r ^ (finrank ℝ E - 1) * (μ (ball (0 : E) 1)).toReal), fun y hy ↦ ?_⟩
  rw [mem_closedBall, le_div_iff₀ hcoeff]
  have h := ENNReal.toReal_mono (by finiteness :
      (2 : ℝ≥0∞) ^ (finrank ℝ E + 1) * μ s ≠ ∞)
    (hs.ofReal_dist_mul_pow_mul_addHaar_ball_le hr hball hy)
  simpa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal,
    dist_nonneg, le_of_lt hr, mul_assoc] using h

/-- Every positive finite-measure set that agrees almost everywhere with a convex set
has a compact convex representative with nonempty interior. In particular, this applies
to convex sets themselves. Equality is with respect to the given additive Haar measure. -/
theorem exists_isCompact_convex_ae_eq (hpos : 0 < μ s) (hfin : μ s ≠ ∞)
    (hc : ∃ C : Set E, Convex ℝ C ∧ s =ᵐ[μ] C) :
    ∃ K : Set E, IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty ∧ s =ᵐ[μ] K := by
  obtain ⟨C, hC, heq⟩ := hc
  have hvol : μ C = μ s := (measure_congr heq).symm
  have hi : (interior C).Nonempty := by
    by_contra hempty
    have hz : μ C = 0 := by
      rw [← measure_interior_of_null_frontier (hC.addHaar_frontier μ),
        Set.not_nonempty_iff_eq_empty.1 hempty, measure_empty]
    exact (hpos.ne' (hvol.symm.trans hz))
  have hb := (isBounded_iff_measure_ne_top_of_convex μ hC hi).2 (hvol.trans_ne hfin)
  exact ⟨closure C, isCompact_of_isClosed_isBounded isClosed_closure hb.closure, hC.closure,
    hi.mono (interior_mono subset_closure),
    heq.trans (closure_ae_eq_of_null_frontier (hC.addHaar_frontier μ)).symm⟩

end TauCeti
