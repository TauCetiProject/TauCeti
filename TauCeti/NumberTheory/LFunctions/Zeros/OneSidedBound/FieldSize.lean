/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import Mathlib.Analysis.Complex.ExponentialBounds
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.NumberTheory.Cyclotomic.Irreducible

/-!
# Size of the cyclotomic host for one-sided prime sums

The dyadic part of the cyclotomic order gives a lower bound on the number of infinite
places. For the upper bound, the fixed base modulus and the ternary part of the tower fit
in the margin between `x ^ 11` and `x ^ 12`. These estimates compare the number of places
available for the prime sums with the size of the underlying number field.

The bounds are those of `New.Data.f_mem_Icc` and `New.Data.q₁_le` in
`grh/src/New/Reduction/Data/Sizes.lean` of lsernau/grh-lean (revision `72fead1`).
-/

public section

open NumberField Real

namespace TauCeti.OneSidedBound.Parameters

-- The ternary part is at most linear in the tower exponent. Its logarithm therefore spends
-- at most half of the one spare power of x, plus an absolute constant.
private theorem log_three_mul_l₀_le (s : ℕ) :
    log (3 * (l₀ s : ℝ)) ≤ 14 + (s : ℝ) / 48 := by
  have hl : l₀ s ≤ 81 * (s + 1) := by
    by_cases h : s = 0
    · norm_num [h, l₀_def]
    · exact (l₀_le h).trans (by omega)
  have ht : (0 : ℝ) < 3 * (l₀ s : ℝ) := by rw [l₀_def]; positivity
  let u : ℝ := ((s : ℝ) + 1) / 48
  have hu : 0 < u := by dsimp [u]; positivity
  have hlt : 3 * (l₀ s : ℝ) ≤ (2 : ℝ) ^ 14 * u := by
    have hl' : (l₀ s : ℝ) ≤ 81 * ((s : ℝ) + 1) := by exact_mod_cast hl
    dsimp [u]
    linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
  have hlogu : log u ≤ (s : ℝ) / 48 := by
    have h := log_le_sub_one_of_pos hu
    dsimp only [u] at h ⊢
    linarith
  calc
    _ ≤ log ((2 : ℝ) ^ 14 * u) := log_le_log ht hlt
    _ = 14 * log 2 + log u := by
      rw [log_mul (by positivity) hu.ne', log_pow]
      norm_num
    _ ≤ _ := by linarith [log_two_lt_d9]

/-- The cyclotomic order is at most `x ^ 12` if the dyadic part is at most `(4 * x) ^ 11`
and the fixed modulus satisfies `q₀ ^ 100 ≤ x`. In particular, the result does not
require the chain length to be the least dyadic rank. -/
theorem q₁_le_pow_twelve (P : Parameters) {x s : ℕ} (hqx : P.q₀ ^ 100 ≤ x)
    (hs : 2 ^ s ≤ (4 * x) ^ 11) : P.q₁ s ≤ x ^ 12 := by
  have hqx' : (P.q₀ : ℝ) ^ 100 ≤ (x : ℝ) := by exact_mod_cast hqx
  have hqpos : (0 : ℝ) < P.q₀ := by exact_mod_cast P.q₀_pos
  have hx : (0 : ℝ) < x := (pow_pos hqpos _).trans_le hqx'
  have hqlog : 100 * log (P.q₀ : ℝ) ≤ log x := by
    simpa only [log_pow, Nat.cast_ofNat] using log_le_log (pow_pos hqpos 100) hqx'
  have hlogx : 100 ≤ log (x : ℝ) := by
    have h₀ := P.le_q₀
    have hq4 : (4 : ℝ) ≤ P.q₀ := by exact_mod_cast (show 4 ≤ P.q₀ by omega)
    have h := log_le_log (by norm_num : (0 : ℝ) < 4) hq4
    linarith [log_four_eq, log_two_gt_d9]
  have hs' : (2 : ℝ) ^ s ≤ (4 * (x : ℝ)) ^ 11 := by exact_mod_cast hs
  have hdyadic := log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) s) hs'
  rw [log_pow, log_pow, log_mul (by norm_num) hx.ne'] at hdyadic
  norm_num only [Nat.cast_ofNat] at hdyadic
  have hse : (s : ℝ) * log 2 ≤ 22 + 11 * log x := by linarith [log_four_le_two]
  have hslog : (s : ℝ) ≤ 24 * log (x : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (show (1 / 2 : ℝ) ≤ log 2 by
      linarith [log_two_gt_d9]) (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
    linarith
  have hlpos : (0 : ℝ) < 3 * (l₀ s : ℝ) := by rw [l₀_def]; positivity
  have hlog : log (P.q₁ s : ℝ) ≤ log ((x : ℝ) ^ 12) := by
    rw [q₁_def, towerDeg_def]
    push_cast
    rw [log_mul hqpos.ne' (mul_ne_zero hlpos.ne' (by positivity)),
      log_mul hlpos.ne' (by positivity), log_pow, log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [log_three_mul_l₀_le s]
  exact_mod_cast (log_le_log_iff (by exact_mod_cast P.q₁_pos s) (pow_pos hx 12)).mp hlog

/-- For the cyclotomic host over a base of degree at most two, the number of infinite places
lies between the dyadic tower order and the cyclotomic order, even if the cyclotomic
polynomial is reducible over the base. -/
theorem card_infinitePlace_mem_Icc (P : Parameters) (s : ℕ)
    {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    [IsCyclotomicExtension {P.q₁ s} K E] (hK : Module.finrank ℚ K ≤ 2) :
    Fintype.card (InfinitePlace E) ∈ Set.Icc (2 ^ s) (P.q₁ s) := by
  have hq : 2 < P.q₁ s := by
    have h := Nat.le_of_dvd (P.q₁_pos s) (P.q₀_dvd_q₁ s)
    have := P.le_q₀
    omega
  have hζ := IsCyclotomicExtension.zeta_spec (P.q₁ s) K E
  have hreal := InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hq hζ
  have hcard : 2 * Fintype.card (InfinitePlace E) = Module.finrank ℚ E := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hreal, zero_add,
      ← InfinitePlace.card_add_two_mul_card_eq_rank, hreal, zero_add]
  have hdyadic : 2 ^ (s + 2) ∣ P.q₁ s := by
    rw [q₁_def, towerDeg_def, pow_add, Nat.mul_comm (2 ^ s), ← Nat.mul_assoc]
    exact mul_dvd_mul_right (dvd_mul_of_dvd_left
      ((by norm_num : 2 ^ 2 ∣ 18480).trans P.dvd_q₀) _) _
  have hlow : 2 * 2 ^ s ≤ (P.q₁ s).totient := by
    have hdvd := Nat.totient_dvd_of_dvd hdyadic
    simp only [show s + 2 = (s + 1) + 1 by omega, Nat.totient_prime_pow_succ Nat.prime_two,
      Nat.reduceSub, mul_one, pow_succ' 2 s] at hdvd
    exact Nat.le_of_dvd (Nat.totient_pos.mpr (P.q₁_pos s)) hdvd
  have htot : (P.q₁ s).totient ≤ Module.finrank ℚ E := by
    simpa only [Nat.lcm_self] using IsPrimitiveRoot.lcm_totient_le_finrank (K := ℚ) hζ hζ
      (by simpa only [Nat.lcm_self] using Polynomial.cyclotomic.irreducible_rat (P.q₁_pos s))
  have hhigh : Module.finrank ℚ E ≤ 2 * P.q₁ s := by
    rw [← Module.finrank_mul_finrank ℚ K E]
    exact Nat.mul_le_mul hK
      ((IsCyclotomicExtension.finrank_le_totient K E).trans (Nat.totient_le _))
  exact ⟨by omega, by omega⟩

end TauCeti.OneSidedBound.Parameters
