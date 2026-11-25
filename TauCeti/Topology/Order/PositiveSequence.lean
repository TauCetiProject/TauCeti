/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Decreasing positive minorants

A sequence of positive real bounds admits a strictly decreasing positive minorant tending
to zero. This permits successive smallness requirements without a uniform positive lower
bound on the prescribed bounds.
-/

public section

open Filter
open scoped Topology

namespace TauCeti

/-- Any positive real sequence has a strictly decreasing positive minorant converging to zero.
The bounds themselves need not be monotone. -/
theorem exists_strictAnti_pos_lt_tendsto_zero {b : ℕ → ℝ} (hb : ∀ n, 0 < b n) :
    ∃ δ : ℕ → ℝ, StrictAnti δ ∧ (∀ n, 0 < δ n ∧ δ n < b n) ∧
      Tendsto δ atTop (𝓝 0) := by
  let δ : ℕ → ℝ := fun n ↦ Nat.rec (min (b 0) 1 / 2)
    (fun k d ↦ min (b (k + 1)) d / 2) n
  have hpos : ∀ n, 0 < δ n := by
    intro n
    induction n with
    | zero => exact div_pos (lt_min (hb 0) zero_lt_one) (by norm_num)
    | succ n ih => exact div_pos (lt_min (hb _) ih) (by norm_num)
  have hlt : ∀ n, δ n < b n := by
    intro n
    cases n with
    | zero => exact (half_lt_self (lt_min (hb 0) zero_lt_one)).trans_le (min_le_left _ _)
    | succ n => exact (half_lt_self (lt_min (hb _) (hpos n))).trans_le (min_le_left _ _)
  have hhalf : ∀ n, δ (n + 1) ≤ δ n / 2 := fun n ↦
    div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hanti : StrictAnti δ := strictAnti_nat_of_succ_lt fun n ↦
    (hhalf n).trans_lt (half_lt_self (hpos n))
  have hgeom : ∀ n, δ n ≤ (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => dsimp [δ]; norm_num; linarith [min_le_right (b 0) 1]
    | succ n ih =>
      rw [pow_succ]
      linarith [hhalf n]
  exact ⟨δ, hanti, fun n ↦ ⟨hpos n, hlt n⟩,
    squeeze_zero (fun n ↦ (hpos n).le) hgeom
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))⟩

end TauCeti
