/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Rank matching at the level prime of a theta lift

The full column rank has level factor `(T^k - 1)^f`, where `k` is the source rank and `f`
is the degree of the totally real field. Matching just its leading term `T^(f * k)`
determines the left endpoint of the prime search. A prime in the resulting relative window
preserves rank matching up to a constant, even after removing the old forms.

The level normalization and the full and new dimension factors are those in Levent Alpöge's
Riemann hypothesis formalization (`Formalism.MainNotions.StandardLattice.VandermondeCountExplicit`
and `GlobalTheory.Mem.Vol.trueDsig`).
-/

public section

namespace TauCeti.ThetaLift

/-- The target level for a word, obtained by matching the leading term of its full rank.
For target rank `D`, leading source coefficient `d` and redundancy parameter `Γ`, the
normalized dimension ratio `q` is `D / (d * Γ^2)`. -/
noncomputable def rankMatchingLevel (f k : ℕ) (q : ℝ) : ℝ :=
  q ^ (1 / ((f * k : ℕ) : ℝ))

/-- The rank-matching level is the real `f * k`-th root of the normalized dimension ratio. -/
theorem rankMatchingLevel_def (f k : ℕ) (q : ℝ) :
    rankMatchingLevel f k q = q ^ (1 / ((f * k : ℕ) : ℝ)) := (rfl)

/-- The target level is positive for a positive dimension ratio. -/
theorem rankMatchingLevel_pos (f k : ℕ) {q : ℝ} (hq : 0 < q) :
    0 < rankMatchingLevel f k q := by
  rw [rankMatchingLevel_def]
  exact Real.rpow_pos_of_pos hq _

/-- Raising the target level to the degree of the leading rank factor gives back the
normalized dimension ratio. -/
theorem rankMatchingLevel_pow_mul {f k : ℕ} (hf : 0 < f) (hk : 0 < k) {q : ℝ} (hq : 0 ≤ q) :
    rankMatchingLevel f k q ^ (f * k) = q := by
  rw [rankMatchingLevel_def, one_div]
  exact Real.rpow_inv_natCast_pow hq (Nat.mul_pos hf hk).ne'

/-- The rank-matching level is the unique nonnegative level whose leading power matches the
normalized dimension ratio. -/
theorem eq_rankMatchingLevel_iff {f k : ℕ} (hf : 0 < f) (hk : 0 < k) {q T : ℝ} (hq : 0 ≤ q)
    (hT : 0 ≤ T) : T = rankMatchingLevel f k q ↔ T ^ (f * k) = q := by
  constructor
  · rintro rfl
    exact rankMatchingLevel_pow_mul hf hk hq
  · intro h
    rw [rankMatchingLevel_def, ← h, one_div]
    exact (Real.pow_rpow_inv_natCast hT (Nat.mul_pos hf hk).ne').symm

/-- For a level sufficiently large relative to the field degree, the fraction of the full
rank that survives passage to the new space is between `3/4` and `1`. -/
theorem newRankFactor_mem_Icc {f : ℕ} {T : ℝ} (hT : 4 * f + 1 ≤ T) :
    ((T - 2) / (T - 1)) ^ f ∈ Set.Icc (3 / 4 : ℝ) 1 := by
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · norm_num
  have hf₁ : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hT₁ : 0 < T - 1 := by linarith
  have he : (T - 2) / (T - 1) = 1 + -(T - 1)⁻¹ := by field_simp; ring
  rw [he]
  have hrecip : (T - 1)⁻¹ ≤ 1 / 4 := by
    rw [inv_eq_one_div, div_le_iff₀ hT₁]
    linarith
  have hloss : (f : ℝ) * (T - 1)⁻¹ ≤ 1 / 4 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hT₁]
    linarith
  refine ⟨?_, ?_⟩
  · exact (by linarith : (3 / 4 : ℝ) ≤ 1 + f * -(T - 1)⁻¹).trans
      (one_add_mul_le_pow (by linarith) f)
  · exact pow_le_one₀ (by linarith) (by have := inv_nonneg.mpr hT₁.le; linarith)

/-- A level between the target and its relative enlargement by `1 + 1/(f*k)` gives a
normalized full rank in `[1/2, exp 1]`. A weak lower endpoint suffices for the rank estimate. -/
theorem fullRank_mem_Icc_of_rankMatchingLevel {f k : ℕ} (hf : 0 < f)
    {q T : ℝ} (hq : 0 < q) (hT : 2 * f ≤ T ^ k)
    (hlevel : rankMatchingLevel f k q ≤ T)
    (hwindow : T ≤ (1 + ((f * k : ℕ) : ℝ)⁻¹) * rankMatchingLevel f k q) :
    (T ^ k - 1) ^ f / q ∈ Set.Icc (1 / 2 : ℝ) (Real.exp 1) := by
  have hf₁ : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hTk₁ : 1 ≤ T ^ k := by linarith
  have hTk₀ : 0 < T ^ k := zero_lt_one.trans_le hTk₁
  have hk : 0 < k := by
    by_contra! hz
    rw [Nat.eq_zero_of_le_zero hz, pow_zero] at hT
    linarith
  have htarget := rankMatchingLevel_pos f k hq
  have hT₀ := htarget.trans_le hlevel
  have hpow := rankMatchingLevel_pow_mul hf hk hq.le
  have hqle : q ≤ T ^ (f * k) := hpow ▸ pow_le_pow_left₀ htarget.le hlevel (f * k)
  refine ⟨?_, ?_⟩
  · have he : T ^ k - 1 = T ^ k * (1 + -(T ^ k)⁻¹) := by
      field_simp
      ring
    have hsmall : (f : ℝ) * (T ^ k)⁻¹ ≤ 1 / 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hTk₀]
      linarith
    have hinv : (T ^ k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hTk₁
    have hber := one_add_mul_le_pow (a := -(T ^ k)⁻¹) (by linarith) f
    rw [le_div_iff₀ hq, he, mul_pow, ← pow_mul, Nat.mul_comm k f]
    calc
      _ ≤ T ^ (f * k) * (1 / 2) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · rw [div_le_iff₀ hq]
    calc
      _ ≤ (T ^ k) ^ f := pow_le_pow_left₀ (by linarith) (by linarith) f
      _ = T ^ (f * k) := by rw [← pow_mul, Nat.mul_comm k f]
      _ ≤ ((1 + ((f * k : ℕ) : ℝ)⁻¹) * rankMatchingLevel f k q) ^ (f * k) :=
        pow_le_pow_left₀ (by positivity) hwindow _
      _ ≤ _ := by
        rw [mul_pow, hpow]
        exact mul_le_mul_of_nonneg_right Real.one_add_inv_pow_le_exp hq.le

/-- The new rank in the same window is between `3/8` and `exp 1` times the matched rank. -/
theorem newRank_mem_Icc_of_rankMatchingLevel {f k : ℕ} (hf : 0 < f)
    {q T : ℝ} (hq : 0 < q) (hT : 4 * f + 1 ≤ T)
    (hlevel : rankMatchingLevel f k q ≤ T)
    (hwindow : T ≤ (1 + ((f * k : ℕ) : ℝ)⁻¹) * rankMatchingLevel f k q) :
    (T ^ k - 1) ^ f * ((T - 2) / (T - 1)) ^ f / q ∈ Set.Icc (3 / 8 : ℝ) (Real.exp 1) := by
  have hf₁ : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hT₁ : 1 < T := by linarith
  have hk : 0 < k := by
    by_contra! hz
    have hz0 := Nat.eq_zero_of_le_zero hz
    rw [hz0, rankMatchingLevel_def] at hwindow
    norm_num at hwindow
    exact hT₁.not_ge hwindow
  have hTk : 2 * (f : ℝ) ≤ T ^ k := (by linarith : 2 * (f : ℝ) ≤ T).trans
    (le_self_pow₀ hT₁.le hk.ne')
  obtain ⟨hl, hu⟩ := fullRank_mem_Icc_of_rankMatchingLevel hf hq hTk hlevel hwindow
  obtain ⟨hnl, hnu⟩ := newRankFactor_mem_Icc hT
  rw [mul_div_right_comm]
  refine ⟨?_, ?_⟩
  · calc
      (3 / 8 : ℝ) = (1 / 2) * (3 / 4) := by norm_num
      _ ≤ _ := mul_le_mul hl hnl (by norm_num) (by linarith)
  · exact (mul_le_of_le_one_right (by linarith [hl]) hnu).trans hu

end TauCeti.ThetaLift
