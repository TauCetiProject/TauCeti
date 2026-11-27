/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Spreading

/-!
# Spanning by translates restricted to a large subspace

A spreading family admits a small set of maps whose images span most of the target. In the
covolume comparison for theta lifts one needs the images of *ramified* source forms instead.
Restricting to this subspace loses at most its codimension per selected map. The theorem below
combines these estimates at a scale `b`, where the ramified source misses at most a share `b⁻⁸`
of the source dimensions.

The constants are from `New.Data.enough_forms` in `New/Reduction/ShortAndEnough.lean` of
<https://github.com/lsernau/grh-lean> at commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

open Module Finset

namespace TauCeti

/-- The logarithmic cost of greedy selection fits the translate budget. -/
private theorem translate_log_budget {b : ℝ} (hb : b ≠ 0) :
    (5 / 2 : ℝ) * (1 + Real.log (b ^ 2 / 2)) ≤ 5 * Real.log (1 + 2 * b ^ 2) := by
  have hb₂ := sq_pos_of_ne_zero hb
  have hfour : (1 : ℝ) ≤ Real.log 4 := by
    have h := Real.le_log_one_add_of_nonneg (x := 3) (by norm_num)
    norm_num at h
    linarith
  have hlog : Real.log 4 + Real.log (b ^ 2 / 2) ≤ Real.log (1 + 2 * b ^ 2) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hn := Real.log_nonneg (by linarith : 1 ≤ 1 + 2 * b ^ 2)
  linarith

/-- At the translate budget, a missing share `b⁻⁸` costs at most `2/b²`. -/
private theorem translate_loss_budget {b : ℝ} (hb : 4 < b ^ 2) :
    5 * Real.log (1 + 2 * b ^ 2) * (b ^ 8)⁻¹ ≤ 2 / b ^ 2 := by
  have hb₀ : b ≠ 0 := by rintro rfl; norm_num at hb
  have hb₂ := sq_pos_of_ne_zero hb₀
  have hb₈ : 0 < (b ^ 2) ^ 4 := pow_pos hb₂ _
  norm_num only [← pow_mul, Nat.reduceMul] at hb₈
  rw [← div_eq_mul_inv, div_le_div_iff₀ hb₈ hb₂]
  have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 2 * b ^ 2)
  have hpow : 5 ≤ (b ^ 2) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hpow (sq_nonneg (b ^ 2))]

public section

/-- Select a finite set of maps from a spreading family so that their images of `U` span at least
`1 - 4/b²` of the target dimensions. The cost counts each selected map with weight `dim U`.
This applies to the ramified subspace when its codimension is at most `b⁻⁸ · dim V`. -/
theorem IsSpread.exists_card_mul_finrank_le_and_le_finrank_biSup_map
    {K V W Θ : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {B : Θ → V →ₗ[K] W} {b : ℝ}
    (hB : IsSpread B (3 / (16 * b ^ 2))) (hb : b ≠ 0) (hV : 0 < finrank K V)
    (U : Submodule K V) (hU : (finrank K V : ℝ) - finrank K U ≤ (b ^ 8)⁻¹ * finrank K V) :
    ∃ t : Finset Θ, #t * finrank K U ≤ 5 * Real.log (1 + 2 * b ^ 2) * finrank K W ∧
      (1 - 4 / b ^ 2) * finrank K W ≤ finrank K ↥(⨆ s ∈ t, U.map (B s)) := by
  have hb₂ : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  by_cases hb₄ : 4 < b ^ 2
  · have := Module.finite_of_finrank_pos hV
    set ε : ℝ := (8 * b ^ 2)⁻¹ with hεdef
    have hε : 0 < ε := by rw [hεdef]; positivity
    have hε' : ε < 1 / 16 := by
      rw [hεdef, inv_eq_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have hη : 3 / (16 * b ^ 2) = 3 / 2 * ε := by rw [hεdef]; field_simp; norm_num
    have heq : 16 * ε = 2 / b ^ 2 := by rw [hεdef]; field_simp; norm_num
    have hinv : (16 * ε)⁻¹ = b ^ 2 / 2 := by rw [heq, inv_div]
    obtain ⟨t, hcost, hrank⟩ :=
      (hη ▸ hB).exists_card_mul_finrank_le_and_le_finrank_biSup_range hV hε hε'
    rw [hinv] at hcost
    rw [heq] at hrank
    have hcost' := hcost.trans (mul_le_mul_of_nonneg_right (translate_log_budget hb)
      (Nat.cast_nonneg (finrank K W)))
    have hdim : (finrank K U : ℝ) ≤ finrank K V := by exact_mod_cast U.finrank_le
    have hloss : (#t : ℝ) * ((finrank K V : ℝ) - finrank K U) ≤ 2 / b ^ 2 * finrank K W := by
      calc _ ≤ #t * ((b ^ 8)⁻¹ * finrank K V) := mul_le_mul_of_nonneg_left hU (by positivity)
        _ = (#t * finrank K V) * (b ^ 8)⁻¹ := by ring
        _ ≤ (5 * Real.log (1 + 2 * b ^ 2) * finrank K W) * (b ^ 8)⁻¹ := by gcongr
        _ ≤ 2 / b ^ 2 * finrank K W := by
              rw [mul_right_comm]
              exact mul_le_mul_of_nonneg_right (translate_loss_budget hb₄) (by positivity)
    have hd : (finrank K ↥(⨆ s ∈ t, LinearMap.range (B s)) : ℝ) ≤
        (finrank K ↥(⨆ s ∈ t, U.map (B s)) : ℝ) +
          #t * ((finrank K V : ℝ) - finrank K U) := by
      rw [← Nat.cast_sub U.finrank_le]
      exact_mod_cast finrank_biSup_range_le B t U
    refine ⟨t, (mul_le_mul_of_nonneg_left hdim (Nat.cast_nonneg _)).trans hcost', ?_⟩
    calc (1 - 4 / b ^ 2) * finrank K W =
        (1 - 2 / b ^ 2) * finrank K W - 2 / b ^ 2 * finrank K W := by ring
      _ ≤ (finrank K ↥(⨆ s ∈ t, U.map (B s)) : ℝ) := by linarith
  · have hshare : 1 - 4 / b ^ 2 ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hb₂, one_mul]
      exact le_of_not_gt hb₄
    refine ⟨∅, ?_, (mul_nonpos_of_nonpos_of_nonneg hshare (by positivity)).trans (by positivity)⟩
    simpa using mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5)
      (Real.log_nonneg (by linarith : 1 ≤ 1 + 2 * b ^ 2))) (Nat.cast_nonneg (finrank K W))

end

end TauCeti
