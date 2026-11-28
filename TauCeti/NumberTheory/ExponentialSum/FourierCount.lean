/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ExponentialSum.NearIntegerCount
import TauCeti.Analysis.Fourier.Fejer

/-!
# Fourier bounds for near-integer counts

`TauCeti.nearIntegerCount_le_sum_norm_intervalExpSum` bounds the number of integers in a real
interval at which a phase is close to an integer. It uses the lower bound for `TauCeti.fejerKernel`
near zero and the upper bound for its finite sum in terms of Mathlib's `AddCircle.fourier`.
-/

public section

open Finset AddCircle

namespace TauCeti

/-- The near-integer count is bounded by the exponential sums of the integer multiples of
the phase. The term at frequency zero is the number of integers in the interval. For `N ≥ 1`
this term contributes at most `4 * N / H`. When `δ > 0`, the cutoff condition is equivalent to
`H ≤ ⌊1 / (8 * δ)⌋₊ + 1`. See Filaseta, *Short interval results for squarefree numbers*. -/
theorem nearIntegerCount_le_sum_norm_intervalExpSum (f : ℝ → ℝ) (a N δ : ℝ) {H : ℕ}
    (hH : 0 < H) (hδ : ((H : ℝ) - 1) * δ ≤ 1 / 8) :
    (nearIntegerCount f a N δ : ℝ) ≤
      2 / (H : ℝ) * ‖intervalExpSum (fun _ ↦ 0) a (a + N)‖ +
        4 / (H : ℝ) * ∑ k ∈ Icc (1 : ℤ) H,
          ‖intervalExpSum (fun x ↦ (k : ℝ) * f x) a (a + N)‖ := by
  classical
  let s : Finset ℤ := Icc ⌈a⌉ ⌊a + N⌋
  let z : ℤ → UnitAddCircle := fun n ↦ (f n : ℝ)
  have hH' : 0 < (H : ℝ) := Nat.cast_pos'.mpr hH
  have hkernel (n : ℤ) (hn : distInt (f n) < δ) : (H : ℝ) / 2 ≤ fejerKernel H (z n) := by
    by_cases hOne : H = 1
    · subst H
      norm_num only [Nat.cast_one, fejerKernel_one, Pi.one_apply, one_div, inv_le_one₀, one_le_two]
    have hTwoNat : 2 ≤ H := by omega
    have hTwo : (2 : ℝ) ≤ H := Nat.ofNat_le_cast.mpr hTwoNat
    have hsmall : (H : ℝ) * ‖z n‖ ≤ 1 / 4 := by
      have hz : ‖z n‖ ≤ δ := (distInt_eq_norm (f n) ▸ hn).le
      have hδ₀ : 0 ≤ δ := (norm_nonneg _).trans hz
      calc
        _ ≤ (H : ℝ) * δ := by gcongr
        _ ≤ (2 * ((H : ℝ) - 1)) * δ :=
          mul_le_mul_of_nonneg_right (by linarith) hδ₀
        _ ≤ _ := by linarith
    exact half_natCast_le_fejerKernel_of_mul_norm_le hsmall
  have hcount : (H : ℝ) / 2 * nearIntegerCount f a N δ ≤ ∑ n ∈ s, fejerKernel H (z n) := by
    rw [nearIntegerCount_def, mul_comm, ← nsmul_eq_mul, ← sum_const]
    exact (sum_le_sum fun n hn ↦ hkernel n (mem_filter.mp hn).2).trans
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun n _ _ ↦ fejerKernel_nonneg H (z n))
  have hmode (k : ℤ) : ∑ n ∈ s, fourier k (z n) =
      intervalExpSum (fun x ↦ (k : ℝ) * f x) a (a + N) := by
    rw [intervalExpSum_def]
    refine sum_congr rfl fun n _ ↦ ?_
    rw [fourier_coe_apply, expTwoPiI_def]
    push_cast
    simp only [div_one, mul_assoc]
  have hzero : (s.card : ℝ) = ‖intervalExpSum (fun _ ↦ 0) a (a + N)‖ := by
    simpa only [fourier_zero, sum_const, nsmul_eq_mul, mul_one, Int.cast_zero, zero_mul,
      Complex.norm_natCast] using (congrArg norm (hmode 0))
  have hbound := hcount.trans (s.sum_fejerKernel_le_card_add z H)
  simp_rw [hzero, hmode] at hbound
  apply (mul_le_mul_iff_of_pos_left hH').mp
  calc
    (H : ℝ) * (nearIntegerCount f a N δ : ℝ) =
        2 * ((H : ℝ) / 2 * nearIntegerCount f a N δ) := by ring
    _ ≤ _ := by
      field_simp
      linarith

end TauCeti
