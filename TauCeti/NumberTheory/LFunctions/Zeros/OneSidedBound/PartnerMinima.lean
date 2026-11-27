/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Bounds for partner minima in local prime sums

The loss from imposing the partner cutoff at a prime is a sum of minima. For weights taking two
values, the small exponents cost at most the lower weight per term, except for a possible near
pair (both places carry the larger weight). The large exponents cost at most a geometric tail.
This separates the sparsity input from the bound used to compare the loss with a factorial
valuation budget.

The estimate is that of `New.Data.partnerMinSum_le` in
`grh/src/New/Derivatives/Sharpness/NearPairs.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

open Finset Set
open scoped NNReal

namespace TauCeti.OneSidedBound

/-- Bound the sum of the partner minima for two-valued weights. Among exponents below `L`, only
`e₀` can connect two large-weight places, and its uncut contribution is then at most `C`. No
restriction on the partner rule or on the permitted exponents above `L` is required. -/
theorem tsum_partner_min_le {ι : Type*} (B : Set ι) [DecidablePred (· ∈ B)]
    (partner : ℕ → ι → ι) (τ : ι) (E : Set ℕ) {p : ℝ} (hp : 1 < p) {b w C : ℝ≥0} {L e₀ : ℕ}
    (hnear : ∀ e ∈ E, e < L → τ ∈ B → partner e τ ∈ B →
      e = e₀ ∧ (b : ℝ) / p ^ e ≤ C) :
    let κ : ι → ℝ := B.piecewise (fun _ ↦ (b : ℝ)) (fun _ ↦ (w : ℝ))
    ∑' e : ℕ, E.indicator (fun e ↦ min (κ τ / p ^ e) (κ (partner e τ))) e ≤
      C + L * (w : ℝ) + max (b : ℝ) w / (p ^ L * (1 - p⁻¹)) := by
  classical
  intro κ
  let f := E.indicator (fun e ↦ min (κ τ / p ^ e) (κ (partner e τ)))
  have hp₀ : 0 < p := zero_lt_one.trans hp
  let M : ℝ := max (b : ℝ) w
  have hκ (σ : ι) : κ σ ∈ Icc (0 : ℝ) M := by
    simp only [κ, Set.piecewise]; split <;> simp [M]
  have hf (e : ℕ) : 0 ≤ f e ∧ f e ≤ M / p ^ e := by
    by_cases he : e ∈ E
    · simp only [f, indicator_of_mem he]
      refine ⟨?_, ?_⟩
      · exact le_min (div_nonneg (hκ τ).1 (by positivity)) (hκ _).1
      · exact (min_le_left ..).trans (div_le_div_of_nonneg_right (hκ τ).2 (by positivity))
    · simpa only [f, indicator_of_notMem he] using ⟨le_rfl, by positivity⟩
  have hr : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  have hg : Summable (fun e : ℕ ↦ M / p ^ e) := by
    simpa only [div_eq_mul_inv, inv_pow] using
      (summable_geometric_of_lt_one (inv_nonneg.mpr hp₀.le) hr).mul_left M
  have hs : Summable f := hg.of_nonneg_of_le (fun e ↦ (hf e).1) (fun e ↦ (hf e).2)
  have hinitial : ∀ e ∈ range L, f e ≤ (w : ℝ) + if e = e₀ then (C : ℝ) else 0 := by
    intro e he
    by_cases hE : e ∈ E
    · simp only [f, indicator_of_mem hE]
      by_cases hτ : τ ∈ B
      · by_cases hpartner : partner e τ ∈ B
        · obtain ⟨rfl, hle⟩ := hnear e hE (mem_range.mp he) hτ hpartner
          simpa only [κ, piecewise_eq_of_mem B _ _ hτ, ite_true] using
            (min_le_left ..).trans (hle.trans (le_add_of_nonneg_left (NNReal.coe_nonneg w)))
        · simpa only [κ, piecewise_eq_of_notMem B _ _ hpartner] using
            (min_le_right ..).trans (le_add_of_nonneg_right (by split <;> positivity))
      · have hdiv : (w : ℝ) / p ^ e ≤ w := div_le_self (by positivity) (one_le_pow₀ hp.le)
        simpa only [κ, piecewise_eq_of_notMem B _ _ hτ] using
          (min_le_left ..).trans (hdiv.trans (le_add_of_nonneg_right (by split <;> positivity)))
    · simp only [f, indicator_of_notMem hE]
      exact add_nonneg (by positivity) (by split <;> positivity)
  rw [← hs.sum_add_tsum_nat_add L]
  refine add_le_add ?_ ?_
  · calc
      ∑ e ∈ range L, f e ≤ ∑ e ∈ range L, ((w : ℝ) + if e = e₀ then (C : ℝ) else 0) :=
        sum_le_sum hinitial
      _ ≤ C + L * (w : ℝ) := by
        rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, sum_ite_eq']
        split <;> linarith [C.coe_nonneg]
  · refine ((summable_nat_add_iff L).mpr hs).tsum_le_tsum (fun e ↦ (hf (e + L)).2)
      ((summable_nat_add_iff L).mpr hg) |>.trans_eq ?_
    have hshift (e : ℕ) : M / p ^ (e + L) = (M / p ^ L) * p⁻¹ ^ e := by
      rw [add_comm e L, pow_add, ← div_div, inv_pow, div_eq_mul_inv _ (p ^ e)]
    simp_rw [hshift]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (inv_nonneg.mpr hp₀.le) hr, ← div_div]
    simp only [M, div_eq_mul_inv]

/-- For the tower parameter `s`, the partner-minimum loss is at most one near contribution `C`,
`l₀(s)` copies of the small weight `w`, and `2b/(kp)` from the tail. The tail requires only
`k ≤ 2^s`: in the dyadic tower, `s = 22e` and `k ≤ 3x^5 ≤ 3 · 2^(10e) ≤ 2^s` for `e ≥ 1`. -/
theorem partnerMinSum_le {ι : Type*} (B : Set ι) [DecidablePred (· ∈ B)]
    (partner : ℕ → ι → ι) (τ : ι) (E : Set ℕ) {p : ℝ} (hp : 2 ≤ p) {b w C : ℝ≥0} {s e₀ : ℕ} {k : ℝ}
    (hk : 0 < k) (hks : k ≤ 2 ^ s)
    (hnear : ∀ e ∈ E, 2 * e < l₀ s → τ ∈ B → partner e τ ∈ B →
      e = e₀ ∧ (b : ℝ) / p ^ e ≤ C) :
    let κ : ι → ℝ := B.piecewise (fun _ ↦ (b : ℝ)) (fun _ ↦ (w : ℝ))
    ∑' e : ℕ, E.indicator (fun e ↦ min (κ τ / p ^ e) (κ (partner e τ))) e ≤
      C + l₀ s * (w : ℝ) + 2 * b / (k * p) := by
  intro κ
  let L := (l₀ s + 1) / 2
  have hl := lt_l₀ s
  have hL : L ≤ l₀ s := by dsimp [L]; omega
  have hsL : s + 1 ≤ L := by dsimp [L]; omega
  have hp₁ : 1 < p := one_lt_two.trans_le hp
  have hi : p⁻¹ ≤ 1 / 2 := by simpa [one_div] using inv_anti₀ two_pos hp
  have hhalf : (1 : ℝ) / 2 ≤ 1 - p⁻¹ := by linarith
  rcases le_or_gt (w : ℝ) b with hw | hw
  swap
  · -- If the nominally small weight is larger, it bounds even the entire geometric series.
    have h := tsum_partner_min_le B partner τ E hp₁ (b := b) (w := w) (C := 0) (L := 0) (e₀ := 0)
      (fun e _ he ↦ (Nat.not_lt_zero e he).elim)
    simp only [NNReal.coe_zero, Nat.cast_zero, zero_mul, zero_add, pow_zero, one_mul,
      max_eq_right hw.le] at h
    refine h.trans ((div_le_div_of_nonneg_left w.coe_nonneg (by norm_num) hhalf).trans ?_)
    have hlarge : 2 ≤ l₀ s := by
      rw [l₀_def]
      exact (by decide : 2 ≤ 3 ^ (4 : ℕ)).trans (Nat.pow_le_pow_right (by decide) (by omega))
    have h' : (w : ℝ) / (1 / 2) ≤ l₀ s * (w : ℝ) := by
      rw [div_div_eq_mul_div, div_one, mul_comm (w : ℝ)]
      gcongr
      exact_mod_cast hlarge
    have htail : 0 ≤ (2 : ℝ) * b / (k * p) := by positivity
    linarith [htail, C.coe_nonneg]
  have hnear' (e : ℕ) (he : e ∈ E) (heL : e < L) :=
    hnear e he (by dsimp [L] at heL; omega)
  have h := tsum_partner_min_le B partner τ E hp₁ (w := w) hnear'
  simp only [max_eq_left hw] at h
  refine h.trans (add_le_add ?_ ?_)
  · gcongr
  · have hkp : k * p ≤ p ^ L := calc
      k * p ≤ p ^ s * p := by gcongr; exact hks.trans (by gcongr)
      _ = p ^ (s + 1) := (pow_succ p s).symm
      _ ≤ p ^ L := pow_le_pow_right₀ hp₁.le hsL
    have hmul : k * p / 2 ≤ p ^ L * (1 - p⁻¹) := by
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul hkp hhalf (by norm_num) (by positivity)
    calc
      _ ≤ (b : ℝ) / (k * p / 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hmul
      _ = _ := by ring

end TauCeti.OneSidedBound
