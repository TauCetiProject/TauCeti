/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Measure

/-!
# Measure of convex sets

The frontier of a convex set in a finite-dimensional real normed space is null for any additive
Haar measure (`Convex.addHaar_frontier`). Consequently, almost every point of the set is in its
interior (`Convex.ae_mem_interior`).

A convex set containing a ball of radius `r > 0` and a point at distance `L` from its centre has
measure at least `2 ^ (-(n + 1)) * μ (ball 0 1) * L * r ^ (n - 1)`, which is the order of the
volume of the cone spanned by the ball and the point
(`Convex.ofReal_dist_mul_pow_mul_addHaar_ball_le`). This is the volume estimate behind the
Aleksandrov maximum principle for the Monge–Ampère equation.

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

open MeasureTheory MeasureTheory.Measure Set Metric Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsAddHaarMeasure μ] {s : Set E}

/-- Almost every point of a convex set in a finite-dimensional real normed space is an interior
point, since the frontier of the set is null for every additive Haar measure. -/
theorem Convex.ae_mem_interior (hs : Convex ℝ s) : ∀ᵐ x ∂μ, x ∈ s → x ∈ interior s :=
  (interior_ae_eq_of_null_frontier (hs.addHaar_frontier μ)).symm.le

/-- **A convex set containing a ball and a point is large.** In a finite-dimensional real normed
space `E` of dimension `n`, if a convex set `s` contains the ball of radius `r > 0` about `x` and
the point `y`, then `dist y x * r ^ (n - 1) * μ (ball 0 1) ≤ 2 ^ (n + 1) * μ s` for every
additive Haar measure `μ`. -/
theorem Convex.ofReal_dist_mul_pow_mul_addHaar_ball_le [Nontrivial E] (hs : Convex ℝ s) {x y : E}
    {r : ℝ} (hr : 0 < r) (hball : ball x r ⊆ s) (hy : y ∈ s) :
    ENNReal.ofReal (dist y x * r ^ (finrank ℝ E - 1)) * μ (ball 0 1) ≤
      2 ^ (finrank ℝ E + 1) * μ s := by
  set n := finrank ℝ E
  set L := dist y x
  have hL₀ : 0 ≤ L := dist_nonneg
  rcases hL₀.eq_or_lt with hL | hL
  · rw [← hL, zero_mul, ENNReal.ofReal_zero, zero_mul]
    exact bot_le
  -- The set `s` contains the balls of radius `r / 2` about the points of the segment from `x` to
  -- the midpoint of `x` and `y`. The centres `c j = x + (j * r / L) • (y - x)` for
  -- `j ≤ m = ⌊L / (2 * r)⌋` lie on that half-segment at mutual distance at least `r`, so the
  -- `m + 1 > L / (2 * r)` balls about them are pairwise disjoint.
  set m := ⌊L / (2 * r)⌋₊
  set c : ℕ → E := fun j => x + ((j : ℝ) * r / L) • (y - x)
  have hyx : ‖y - x‖ = L := (dist_eq_norm y x).symm
  have hdist : ∀ i j : ℕ, dist (c i) (c j) = |(i : ℝ) - j| * r := fun i j => by
    simp only [c, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hyx,
      Real.norm_eq_abs, ← sub_div, ← sub_mul, abs_div, abs_mul, abs_of_pos hr]
    rw [abs_of_pos hL]
    field_simp
  have hsub : ∀ j ∈ Finset.range (m + 1), ball (c j) (r / 2) ⊆ s := fun j hj z hz => by
    set t := (j : ℝ) * r / L
    have ht₀ : 0 ≤ t := by positivity
    have ht : t ≤ 1 / 2 := by
      have hj : (j : ℝ) ≤ L / (2 * r) :=
        (Nat.cast_le.2 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))).trans
          (Nat.floor_le (by positivity))
      rw [div_le_iff₀ hL]
      rw [le_div_iff₀ (by positivity)] at hj
      linarith
    -- `z = (1 - t) • b + t • y` with `b = x + (1 - t)⁻¹ • (z - c j)` in `ball x r`.
    have hb : x + (1 - t)⁻¹ • (z - c j) ∈ ball x r := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_pos (by linarith), ← dist_eq_norm, inv_mul_lt_iff₀ (by linarith)]
      rw [mem_ball] at hz
      nlinarith
    convert hs (hball hb) hy (by linarith : (0 : ℝ) ≤ 1 - t) ht₀ (by ring) using 1
    have hc : c j = x + t • (y - x) := rfl
    rw [smul_add, smul_smul, mul_inv_cancel₀ (by linarith : (1 - t) ≠ 0), one_smul, hc]
    module
  have hdisj : (Finset.range (m + 1) : Set ℕ).PairwiseDisjoint fun j => ball (c j) (r / 2) :=
    fun i _ j _ hij => ball_disjoint_ball <| by
      rw [hdist, add_halves]
      have : (1 : ℝ) ≤ |(i : ℝ) - j| := by
        rcases lt_or_gt_of_ne hij with h | h
        · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
          exact le_abs.2 (Or.inr (by linarith))
        · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
          exact le_abs.2 (Or.inl (by linarith))
      nlinarith
  have hn : 1 ≤ n := finrank_pos
  have hm : L / (2 * r) < m + 1 := Nat.lt_floor_add_one _
  calc ENNReal.ofReal (L * r ^ (n - 1)) * μ (ball 0 1)
      ≤ ENNReal.ofReal (2 ^ (n + 1) * ((m + 1) * (r / 2) ^ n)) * μ (ball 0 1) := by
        gcongr ENNReal.ofReal ?_ * _
        have hrn : r ^ n = r * r ^ (n - 1) := by rw [← pow_succ', Nat.sub_add_cancel hn]
        have h2 : (2 : ℝ) ^ (n + 1) * (r / 2) ^ n = 2 * r ^ n := by
          rw [div_pow, pow_succ]
          field_simp
        rw [div_lt_iff₀ (by positivity)] at hm
        calc L * r ^ (n - 1) ≤ (m + 1) * (2 * r) * r ^ (n - 1) := by gcongr
          _ = 2 ^ (n + 1) * ((m + 1) * (r / 2) ^ n) := by
            rw [mul_left_comm (2 ^ (n + 1) : ℝ), h2, hrn]
            ring
    _ = 2 ^ (n + 1) * ∑ j ∈ Finset.range (m + 1), μ (ball (c j) (r / 2)) := by
        simp only [addHaar_ball μ _ (by positivity : 0 ≤ r / 2), Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
        push_cast
        rw [ENNReal.ofReal_add (by positivity) zero_le_one]
        simp [mul_assoc, n]
    _ = 2 ^ (n + 1) * μ (⋃ j ∈ Finset.range (m + 1), ball (c j) (r / 2)) := by
        rw [measure_biUnion_finset hdisj fun _ _ => measurableSet_ball]
    _ ≤ 2 ^ (n + 1) * μ s := by
        gcongr
        exact iUnion₂_subset hsub

open Bornology
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
