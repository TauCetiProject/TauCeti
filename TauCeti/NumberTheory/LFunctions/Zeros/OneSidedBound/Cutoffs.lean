/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Algebra.Order.Archimedean.Basic
import TauCeti.Analysis.SpecialFunctions.Log.NatCastAdd
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Separated cutoffs for one-sided prime sum bounds

For a large cutoff `x`, choose `x₁ = ⌊exp (x ^ (ε / 6))⌋₊` and take `b` to be the least
multiple of `q * x₁` above `exp (x ^ ε)`. The rounding preserves the logarithmic size of `b`
uniformly for positive integers `q ≤ x ^ D`. The scales are separated by large powers, as
needed to estimate a two-cutoff prime remainder and impose a divisibility condition on its
weights at the same time.

The choice of scales is from `New.Parameters.IsLargeScale.exists_isAdmissibleData` in
lsernau/grh-lean, `New/Reduction/Data/Existence.lean` (revision `72fead1`).
-/

public section

namespace TauCeti.OneSidedBound

open Asymptotics Filter Real Set

/-- Rounding the upper cutoff by a product of a polynomially bounded integer and the
intermediate cutoff changes its logarithm by at most one. -/
private theorem eventually_exists_least_cutoff {ε : ℝ} (hε : 0 < ε) (D : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ q : ℕ, 0 < q → (q : ℝ) ≤ x ^ D →
      let x₁ := ⌊exp (x ^ (ε / 6))⌋₊
      1 ≤ x₁ ∧ ∃ b : ℕ, IsLeast {n : ℕ | q * x₁ ∣ n ∧ exp (x ^ ε) < n} b ∧
        log (b : ℝ) ∈ Icc (x ^ ε) (x ^ ε + 1) := by
  have hsmall := ((isLittleO_log_rpow_atTop hε).const_mul_left D).add
    (isLittleO_rpow_rpow_atTop (by linarith : ε / 6 < ε))
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall.eventuallyLE] with x hx hs q hq hqD
  have hx' : 0 < x := zero_lt_one.trans_le hx
  have hsum : D * log x + x ^ (ε / 6) ≤ x ^ ε :=
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs, abs_of_pos (rpow_pos_of_pos hx' ε)] using hs)
  intro x₁
  have hx₁ : 1 ≤ x₁ := by simpa [x₁] using rpow_nonneg hx'.le (ε / 6)
  obtain ⟨b, hb, hupper⟩ := Nat.exists_isLeast_dvd_and_lt_le_add
    (Nat.mul_pos hq hx₁) (exp_nonneg (x ^ ε))
  have hstep : ((q * x₁ : ℕ) : ℝ) ≤ exp (x ^ ε) := calc
    ((q * x₁ : ℕ) : ℝ) ≤ (x ^ D) * exp (x ^ (ε / 6)) := by
      rw [Nat.cast_mul]
      exact mul_le_mul hqD (Nat.floor_le (exp_nonneg _)) (Nat.cast_nonneg x₁)
        (rpow_nonneg hx'.le D)
    _ = exp (D * log x + x ^ (ε / 6)) := by rw [exp_add, rpow_def_of_pos hx', mul_comm D]
    _ ≤ exp (x ^ ε) := exp_le_exp.mpr hsum
  have hpos : 0 < (b : ℝ) := (exp_pos _).trans hb.1.2
  refine ⟨hx₁, b, hb, ⟨?_, ?_⟩⟩
  · simpa only [log_exp] using log_le_log (exp_pos _) hb.1.2.le
  · apply (log_le_iff_le_exp hpos).mpr
    rw [exp_add]
    have he : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp 1]
    calc
      (b : ℝ) ≤ exp (x ^ ε) + ((q * x₁ : ℕ) : ℝ) := hupper
      _ ≤ exp (x ^ ε) * 2 := by linarith
      _ ≤ exp (x ^ ε) * exp 1 := mul_le_mul_of_nonneg_left he (exp_nonneg _)

/-- For every sufficiently large `x`, the prescribed exponential rounding gives an intermediate
cutoff `x₁` and a least upper cutoff `b`, uniformly over `0 < q ≤ x ^ D`. The logarithmic bounds
control the rounding error, and the power bounds separate the three cutoffs. -/
theorem eventually_exists_admissible_cutoffs {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 100)
    (C D : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ q : ℕ, 0 < q → (q : ℝ) ≤ x ^ D →
      let x₁ := ⌊exp (x ^ (ε / 6))⌋₊
      ∃ b : ℕ, IsLeast {n : ℕ | q * x₁ ∣ n ∧ exp (x ^ ε) < n} b ∧
        x ^ (ε / 6) - 1 ≤ log (x₁ : ℝ) ∧ log (x₁ : ℝ) ≤ x ^ (ε / 6) ∧
        x ^ ε ≤ log (b : ℝ) ∧ log (b : ℝ) ≤ x ^ ε + 1 ∧
        C ≤ log (log (b : ℝ)) ∧ (log (b : ℝ)) ^ 100 ≤ x ∧
        x ^ (1000000 : ℕ) ≤ (x₁ : ℝ) ∧ x₁ ^ 1000000 ≤ b ∧
        (log (x₁ : ℝ)) ^ 6 ≤ log (b : ℝ) := by
  -- Compare the logarithmic scales first; the separation of the cutoffs follows by exponentiation.
  have hpow := isLittleO_rpow_rpow_atTop hε'
  have hone : (fun _ : ℝ ↦ (1 : ℝ)) =o[atTop] (fun x : ℝ ↦ x ^ ε) := by
    simpa only [rpow_zero] using isLittleO_rpow_rpow_atTop hε
  have hgrow := ((isLittleO_log_rpow_atTop (by linarith : 0 < ε / 6)).const_mul_left
    (1000000 : ℝ)).add (by
      simpa only [rpow_zero] using isLittleO_rpow_rpow_atTop (by linarith : 0 < ε / 6))
  have hsep := (isLittleO_rpow_rpow_atTop (by linarith : ε / 6 < ε)).const_mul_left (1000000 : ℝ)
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_exists_least_cutoff hε D,
    (hpow.add (hone.trans hpow)).eventuallyLE, hgrow.eventuallyLE, hsep.eventuallyLE,
    (tendsto_log_atTop.comp (tendsto_rpow_atTop hε)).eventually_ge_atTop C]
    with x hx hcut hpowx hgrowx hsepx hCx q hq hqD
  have hx' : 0 < x := zero_lt_one.trans_le hx
  simp only [Real.norm_eq_abs, abs_of_pos (rpow_pos_of_pos hx' _),
    abs_of_nonneg (by positivity : 0 ≤ x ^ ε + 1), abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1000000)] at hpowx hgrowx hsepx
  intro x₁
  obtain ⟨hx₁, b, hb, hlogb, hlogb'⟩ := hcut q hq hqD
  have hx₁le : (1 : ℝ) ≤ x₁ := Nat.one_le_cast.mpr hx₁
  have hx₁' : (0 : ℝ) < x₁ := zero_lt_one.trans_le hx₁le
  have hb' : (0 : ℝ) < b := (exp_pos _).trans hb.1.2
  have hlog₁ : log (x₁ : ℝ) ∈ Icc (x ^ (ε / 6) - log 2) (x ^ (ε / 6)) :=
    log_natFloor_exp_mem_Icc (rpow_nonneg hx'.le _)
  have hlogtwo : log 2 ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  refine ⟨b, hb, by linarith [hlog₁.1], hlog₁.2, hlogb, hlogb',
    hCx.trans (log_le_log (rpow_pos_of_pos hx' _) hlogb), ?_, ?_, ?_, ?_⟩
  · calc
      (log (b : ℝ)) ^ 100 ≤ (x ^ (1 / 100 : ℝ)) ^ (100 : ℕ) :=
        pow_le_pow_left₀ ((rpow_pos_of_pos hx' _).le.trans hlogb) (hlogb'.trans hpowx) _
      _ = x := by rw [← rpow_mul_natCast hx'.le]; norm_num
  · apply (log_le_log_iff (by positivity) hx₁').mp
    rw [log_pow, Nat.cast_ofNat]
    linarith [hlog₁.1, (le_abs_self _).trans hgrowx]
  · have h : (x₁ : ℝ) ^ (1000000 : ℕ) ≤ b := by
      apply (log_le_log_iff (by positivity) hb').mp
      rw [log_pow, Nat.cast_ofNat]
      exact (mul_le_mul_of_nonneg_left hlog₁.2 (by norm_num)).trans (hsepx.trans hlogb)
    rw [← Nat.cast_le (α := ℝ), Nat.cast_pow]
    exact h
  · calc
      (log (x₁ : ℝ)) ^ 6 ≤ (x ^ (ε / 6)) ^ (6 : ℕ) :=
        pow_le_pow_left₀ (log_nonneg hx₁le) hlog₁.2 _
      _ = x ^ ε := by rw [← rpow_mul_natCast hx'.le]; norm_num
      _ ≤ log (b : ℝ) := hlogb

end TauCeti.OneSidedBound
