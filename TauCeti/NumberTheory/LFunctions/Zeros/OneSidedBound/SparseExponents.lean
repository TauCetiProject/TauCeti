/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Card
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Combinatorics.Additive.NoRelation

/-!
# Large sets of exponents for sparse places

To construct sparse sets of places in a cyclotomic tower, one takes powers of a unit of
order `2 ^ s` with exponents from a modular Behrend set. The exponents must avoid weighted
means with total weight at most `2 * l₀ s`, and the set must be large compared with
`towerDeg s = 3 * l₀ s * 2 ^ s`. This file supplies the exponent set with the required
cardinality, before transporting it to places.

The cardinality budget is that of `New.Parameters.exists_isSparse` in
`grh/src/New/Reduction/Data/Existence.lean` of lsernau/grh-lean (`72fead1`). We take the
floor of a real root to choose the digit bound.
-/

public section

open Finset

namespace TauCeti.OneSidedBound

private theorem exists_sparse_digit_bound {s n : ℕ} {W : ℝ} (hn : 0 < n)
    (hW : W ≤ 2 ^ s) (ho : (2 : ℝ) ^ s ≤ W ^ (n + 1))
    (hbase : (2 * (l₀ s : ℝ)) ^ n ≤ W) :
    ∃ H : ℕ, (2 * l₀ s * H) ^ n ≤ 2 ^ s ∧ (H : ℝ) ≤ W ∧
      (2 : ℝ) ^ s < W * (2 * H) ^ n := by
  have hW₀ : 0 < W := lt_of_lt_of_le (by rw [l₀_def]; positivity) hbase
  let u : ℝ := ((2 : ℝ) ^ s / W) ^ ((n : ℝ)⁻¹)
  have hu₀ : 0 ≤ u := by dsimp [u]; positivity
  have hup : u ^ n = (2 : ℝ) ^ s / W := by
    dsimp only [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne'), Real.rpow_one]
  have hu₁ : 1 ≤ u := by
    by_contra! h
    have h' := pow_lt_pow_left₀ h hu₀ hn.ne'
    rw [one_pow, hup, div_lt_one hW₀] at h'
    exact h'.not_ge hW
  have huW : u ≤ W := by
    by_contra! h
    have h' := pow_lt_pow_left₀ h hW₀.le hn.ne'
    rw [hup, lt_div_iff₀ hW₀, ← pow_succ] at h'
    exact h'.not_ge ho
  let H := ⌊u⌋₊
  have hH : 0 < H := Nat.floor_pos.mpr hu₁
  have hHu : (H : ℝ) ≤ u := Nat.floor_le hu₀
  have hH₂ : H + 1 ≤ 2 * H := by omega
  have huH : u < 2 * (H : ℝ) := (Nat.lt_floor_add_one u).trans_le (by exact_mod_cast hH₂)
  refine ⟨H, ?_, hHu.trans huW, ?_⟩
  · have hh := pow_le_pow_left₀ (Nat.cast_nonneg H) hHu n
    rw [hup] at hh
    have hfit : (2 * (l₀ s : ℝ) * H) ^ n ≤ (2 : ℝ) ^ s := by
      rw [mul_pow]
      exact (mul_le_mul hbase hh (by positivity) hW₀.le).trans_eq (mul_div_cancel₀ _ hW₀.ne')
    exact_mod_cast hfit
  · have hh := pow_lt_pow_left₀ huH hu₀ hn.ne'
    rwa [hup, div_lt_iff₀ hW₀, mul_comm] at hh

-- The budget for the base pays both for rounding the digits and for the loss from the sphere.
private theorem towerDeg_le_sparse_bound {s n H : ℕ} {W : ℝ} (hn : 0 < n)
    (hbase : (2 * (l₀ s : ℝ)) ^ n ≤ W) (hHW : (H : ℝ) ≤ W)
    (hcover : (2 : ℝ) ^ s < W * (2 * H) ^ n) :
    (towerDeg s : ℝ) ≤ ((H : ℝ) ^ n / (n * H ^ 2)) * W ^ 6 := by
  have hH : 0 < H := by
    by_contra! h
    have hz : (0 : ℝ) < 2 ^ s := by positivity
    simp [Nat.eq_zero_of_le_zero h, hn.ne', hz.not_gt] at hcover
  have hW : 0 ≤ W := (Nat.cast_nonneg H).trans hHW
  have hL : (3 : ℝ) ≤ l₀ s := by
    rw [l₀_def, Nat.cast_pow, Nat.cast_ofNat]
    exact le_self_pow₀ (by norm_num) (by omega)
  have hLW : (2 : ℝ) * l₀ s ≤ W := (le_self_pow₀ (by linarith) hn.ne').trans hbase
  have hC : (3 : ℝ) * l₀ s ≤ W ^ 2 := calc
    (3 : ℝ) * l₀ s ≤ (2 * l₀ s) ^ 2 := by nlinarith
    _ ≤ W ^ 2 := by gcongr
  have hN : (n : ℝ) * 2 ^ n ≤ W := calc
    (n : ℝ) * 2 ^ n ≤ 2 ^ n * 2 ^ n := by gcongr; exact_mod_cast n.lt_two_pow_self.le
    _ = 4 ^ n := by rw [← mul_pow]; norm_num
    _ ≤ W := (pow_le_pow_left₀ (by norm_num) (by linarith) n).trans hbase
  have hsize : (3 * l₀ s * n * 2 ^ n : ℝ) ≤ W ^ 3 := by
    rw [mul_assoc (3 * (l₀ s : ℝ)), pow_succ W 2]
    exact mul_le_mul hC hN (by positivity) (by positivity)
  have hH₂ : (H : ℝ) ^ 2 ≤ W ^ 2 := pow_le_pow_left₀ (by positivity) hHW 2
  rw [towerDeg_def]
  push_cast
  calc
    3 * (l₀ s : ℝ) * 2 ^ s ≤ 3 * l₀ s * (W * (2 * H) ^ n) := by gcongr
    _ = (3 * l₀ s * n * 2 ^ n) * (W * ((H : ℝ) ^ n / (n : ℝ))) := by
      rw [mul_pow]
      field_simp
    _ ≤ W ^ 3 * (W * ((H : ℝ) ^ n / (n : ℝ))) := by gcongr
    _ = ((H : ℝ) ^ n / (n * H ^ 2)) * (W ^ 4 * H ^ 2) := by field_simp
    _ ≤ ((H : ℝ) ^ n / (n * H ^ 2)) * W ^ 6 := by
      have hWW : W ^ 4 * W ^ 2 = W ^ 6 := (pow_add W 4 2).symm
      rw [← hWW]
      gcongr

/-- At tower exponent `s`, there is a set of exponents below `2 ^ s` with cardinality at least
`towerDeg s / W ^ 6`, avoiding all nontrivial modular weighted means with positive weights
of sum at most `2 * l₀ s`. -/
theorem exists_large_sparse_exponents {s n : ℕ} {W : ℝ} (hn : 0 < n)
    (ho : (2 : ℝ) ^ s ≤ W ^ (n + 1)) (hbase : (2 * (l₀ s : ℝ)) ^ n ≤ W) :
    ∃ S : Finset ℕ, (∀ e ∈ S, e < 2 ^ s) ∧ (towerDeg s : ℝ) ≤ #S * W ^ 6 ∧
      ∀ e₁ ∈ S, ∀ e₂ ∈ S, ∀ e₃ ∈ S, ∀ a b : ℕ, 0 < a → 0 < b → a + b ≤ 2 * l₀ s →
        (a + b) * e₂ ≡ a * e₁ + b * e₃ [MOD 2 ^ s] → e₁ = e₂ ∧ e₂ = e₃ := by
  have hL : 0 < l₀ s := by rw [l₀_def]; positivity
  by_cases hW : W ≤ (2 : ℝ) ^ s
  · obtain ⟨H, hfit, hHW, hcover⟩ := exists_sparse_digit_bound hn hW ho hbase
    obtain ⟨S, hS, hcard, hmean⟩ :=
      exists_eq_and_eq_of_add_mul_modEq (n := n) (H := H) (L := 2 * l₀ s) (by omega) hfit
    refine ⟨S, hS, (towerDeg_le_sparse_bound hn hbase hHW hcover).trans ?_, hmean⟩
    push_cast at hcard
    gcongr
  · have hL' : (1 : ℝ) ≤ l₀ s := by exact_mod_cast hL
    have hLW : (2 : ℝ) * l₀ s ≤ W := (le_self_pow₀ (by linarith) hn.ne').trans hbase
    have hW₁ : 1 ≤ W := by linarith
    have hC : (3 : ℝ) * l₀ s ≤ W ^ 2 :=
      (by nlinarith : (3 : ℝ) * l₀ s ≤ (2 * l₀ s) ^ 2).trans (by gcongr)
    refine ⟨{0}, by simp, ?_, by simp⟩
    simpa [towerDeg_def] using (calc
      3 * (l₀ s : ℝ) * 2 ^ s ≤ W ^ 2 * W := by gcongr; exact (not_le.mp hW).le
      _ = W ^ 3 := (pow_succ W 2).symm
      _ ≤ W ^ 6 := pow_le_pow_right₀ hW₁ (by decide))

end TauCeti.OneSidedBound
