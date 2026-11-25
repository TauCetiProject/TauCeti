/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import TauCeti.NumberTheory.ArithmeticFunction.DivisorBounds
import TauCeti.NumberTheory.PrimeCounting
import TauCeti.NumberTheory.SelbergSieve.CoprimeDiagonal
import TauCeti.NumberTheory.SelbergSieve.PrimeInterval

/-!
# The Selberg upper bound for primes in an interval

Selberg's sieve applied to the integers in `(x, x + y]`, sifted by the primes at most `z`,
bounds the number of primes in a short interval:

`π(x + y) - π(x) ≤ y / log z + z² (1 + 2 log z)² + z + 1`

for every real `x`, every `y ≥ 0` and every `z > 1`. The main term comes from the diagonal
mass `G(z) ≥ log z`; the error terms bound the absolute remainder `∑_{d < z²} 3^ω(d) |r_d|`
and count the primes at most `z`, which the sieve removes. With `z = √y / (log y)³` this
gives the Brun–Titchmarsh bound in intervals,

`π(x + y) - π(x) ≤ 2y / log y + C y log log (3y) / (log y)²`

for all real `x` and `y > 1`, with an absolute constant `C`. The constant comes from an
asymptotic comparison of `log log y` with `log y` and is not made explicit.

## Main results

* `TauCeti.primeCounting_floor_add_sub_le_div_log_add`: the bound at an arbitrary sieving
  level `z > 1`.
* `TauCeti.exists_primeCounting_floor_add_sub_le_two_mul_div_log_add`: the Brun–Titchmarsh bound
  in intervals of length `y > 1`, uniformly in the position `x`.

## References

* D. R. Heath-Brown, *Lectures on sieves*, §3, the first application of Corollary 3.1 and
  estimate (3.3).
* Arend Mellendijk, PNT+, `BrunTitchmarsh.lean`, the same sieve for primes in an interval:
  https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/7c7892801a0937aa6925e531a5e2c105bd20690b/PrimeNumberTheoremAnd/BrunTitchmarsh.lean
-/

public section

open Finset Real
open scoped ArithmeticFunction.omega

namespace TauCeti

/-- The Selberg remainder of the interval sieve at level `z` is at most `z² (1 + 2 log z)²`,
the coefficient-one majorant of `∑_{n ≤ z²} 3^ω(n)`. -/
private theorem sum_three_pow_mul_abs_rem_primeInterval_le (x y z : ℝ) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hz : 1 ≤ z) :
    ∑ d ∈ (BoundingSieve.primeInterval x y z).prodPrimes.divisors.filter
        (fun d : ℕ ↦ (d : ℝ) < z ^ 2),
      (3 : ℝ) ^ ω d * |(BoundingSieve.primeInterval x y z).rem d| ≤
      z ^ 2 * (1 + 2 * Real.log z) ^ 2 := by
  have hz2 : 1 ≤ z ^ 2 := one_le_pow₀ hz
  calc _ ≤ ∑ d ∈ (BoundingSieve.primeInterval x y z).prodPrimes.divisors.filter
          (fun d : ℕ ↦ (d : ℝ) < z ^ 2), (3 : ℝ) ^ ω d := by
        gcongr with d
        exact mul_le_of_le_one_right (by positivity)
          (BoundingSieve.abs_rem_primeInterval_lt_one x y z hx hy d).le
    _ ≤ ∑ n ∈ Ioc 0 ⌊z ^ 2⌋₊, (3 : ℝ) ^ ω n := by
        refine sum_le_sum_of_subset_of_nonneg (fun d hd ↦ ?_) (fun _ _ _ ↦ by positivity)
        obtain ⟨hdP, hdz⟩ := mem_filter.mp hd
        exact mem_Ioc.mpr ⟨Nat.pos_of_mem_divisors hdP,
          Nat.le_floor (le_of_lt hdz)⟩
    _ ≤ z ^ 2 * (1 + Real.log (z ^ 2)) ^ 2 :=
        ArithmeticFunction.sum_Ioc_three_pow_cardDistinctFactors_le_mul_one_add_log_sq hz2
    _ = z ^ 2 * (1 + 2 * Real.log z) ^ 2 := by rw [Real.log_pow, Nat.cast_ofNat]

/-- **Selberg's sieve for primes in an interval.** For every real `x`, every `y ≥ 0` and every
sieving level `z > 1`, the number of primes in `(x, x + y]` is at most
`y / log z + z² (1 + 2 log z)² + z + 1`. -/
theorem primeCounting_floor_add_sub_le_div_log_add (x y : ℝ) {z : ℝ} (hy : 0 ≤ y)
    (hz : 1 < z) :
    (Nat.primeCounting ⌊x + y⌋₊ : ℝ) - Nat.primeCounting ⌊x⌋₊ ≤
      y / Real.log z + z ^ 2 * (1 + 2 * Real.log z) ^ 2 + (z + 1) := by
  refine (Nat.primeCounting_floor_add_sub_le_max x y).trans ?_
  set x' := max x 0
  have hx' : 0 ≤ x' := le_max_right x 0
  set s := BoundingSieve.primeInterval x' y z
  have hlog : 0 < Real.log z := Real.log_pos hz
  have hG : Real.log z ≤ s.diagonalMass z := by
    have h := s.totient_div_mul_log_le_diagonalMass 1 (z := z) (by linarith)
      (fun p hp hpz _ ↦ ?_) (fun p _ _ _ ↦ ?_)
    · rwa [Nat.totient_one, Nat.cast_one, div_one, one_mul] at h
    · rw [BoundingSieve.primeInterval_prodPrimes, hp.dvd_primorial_iff]
      exact Nat.le_floor hpz.le
    · rw [BoundingSieve.primeInterval_nu_apply]
  have hπ : (Nat.primeCounting ⌊z⌋₊ : ℝ) ≤ z + 1 :=
    calc (Nat.primeCounting ⌊z⌋₊ : ℝ) ≤ ⌊z⌋₊ := by exact_mod_cast Nat.primeCounting_le_self _
      _ ≤ z + 1 := by linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ z)]
  rw [← Nat.cast_sub (Nat.monotone_primeCounting (Nat.floor_mono (by linarith : x' ≤ x' + y)))]
  calc _ ≤ s.siftedSum + Nat.primeCounting ⌊z⌋₊ :=
        BoundingSieve.primeCounting_sub_le_primeInterval x' y z
    _ ≤ (s.totalMass / s.diagonalMass z +
          ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ ↦ (d : ℝ) < z ^ 2),
            (3 : ℝ) ^ ω d * |s.rem d|) + (z + 1) := by
        gcongr
        exact s.siftedSum_le_totalMass_div_diagonalMass_add_sum_three_pow hz
    _ ≤ y / Real.log z + z ^ 2 * (1 + 2 * Real.log z) ^ 2 + (z + 1) := by
        rw [BoundingSieve.primeInterval_totalMass]
        gcongr
        exact sum_three_pow_mul_abs_rem_primeInterval_le x' y z hx' hy hz.le

/-- With `L = log y`, `a = log L ≥ 1` and `12 a ≤ L`, the sieving level `z = √y / L³` makes the
bound of `primeCounting_floor_add_sub_le_div_log_add` at most `2y / L + 30 y a / L²`. -/
private theorem primeCounting_floor_add_sub_le_of_log_le (x y : ℝ) (hy : 0 < y)
    (ha : 1 ≤ Real.log (Real.log y))
    (hL : 12 * Real.log (Real.log y) ≤ Real.log y) :
    (Nat.primeCounting ⌊x + y⌋₊ : ℝ) - Nat.primeCounting ⌊x⌋₊ ≤
      2 * y / Real.log y + 30 * y * Real.log (Real.log y) / Real.log y ^ 2 := by
  set L := Real.log y
  set a := Real.log L
  have hL0 : 0 < L := by linarith
  -- The sieving level `z = exp (L / 2 - 3a) = √y / L³`, and `E = y / L² = exp (L - 2a)`.
  have hyexp : Real.exp L = y := Real.exp_log hy
  have hLexp : Real.exp a = L := Real.exp_log hL0
  have hL2 : L ^ 2 = Real.exp (2 * a) := by
    rw [← hLexp, ← Real.exp_natCast_mul, Nat.cast_ofNat]
  have hE : y / L ^ 2 = Real.exp (L - 2 * a) := by
    rw [Real.exp_sub, hyexp, show 2 * a = a + a by ring, Real.exp_add, hLexp, sq]
  have hz : 1 < Real.exp (L / 2 - 3 * a) := Real.one_lt_exp_iff.mpr (by linarith)
  have hE1 : 1 ≤ Real.exp (L - 2 * a) := Real.one_le_exp (by linarith)
  refine (primeCounting_floor_add_sub_le_div_log_add x y hy.le hz).trans ?_
  rw [Real.log_exp]
  -- Main term: `y / (L / 2 - 3a) ≤ 2y / L + 24 a E`.
  have hmain : y / (L / 2 - 3 * a) ≤ 2 * y / L + 24 * a * (y / L ^ 2) := by
    rw [show 2 * y / L + 24 * a * (y / L ^ 2) = (2 * y * L + 24 * a * y) / L ^ 2 by
      field_simp, div_le_div_iff₀ (by linarith) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ a) hy.le)
      (sub_nonneg.mpr hL)]
  -- Remainder: `z² (1 + 2 log z)² ≤ 4 L² exp (L - 6a) = 4 exp (L - 4a) ≤ 4 a E`.
  have hrem : Real.exp (L / 2 - 3 * a) ^ 2 * (1 + 2 * (L / 2 - 3 * a)) ^ 2 ≤
      4 * a * (y / L ^ 2) := by
    have hsq : (1 + 2 * (L / 2 - 3 * a)) ^ 2 ≤ (2 * L) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    calc _ ≤ Real.exp (L / 2 - 3 * a) ^ 2 * (2 * L) ^ 2 := by gcongr
      _ = 4 * (Real.exp (L / 2 - 3 * a) ^ 2 * L ^ 2) := by ring
      _ = 4 * Real.exp (L - 4 * a) := by
        rw [hL2, ← Real.exp_natCast_mul, ← Real.exp_add]
        ring_nf
      _ ≤ 4 * Real.exp (L - 2 * a) := by gcongr; linarith
      _ ≤ 4 * a * (y / L ^ 2) := by
        rw [hE, mul_assoc]
        gcongr
        exact le_mul_of_one_le_left (by positivity) ha
  -- Small primes: `z + 1 ≤ 2E ≤ 2 a E`, since `z ≤ E` and `1 ≤ E`.
  have hsmall : Real.exp (L / 2 - 3 * a) + 1 ≤ 2 * a * (y / L ^ 2) := by
    have hzE : Real.exp (L / 2 - 3 * a) ≤ Real.exp (L - 2 * a) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [hE]
    nlinarith
  calc _ ≤ 2 * y / L + 24 * a * (y / L ^ 2) + 4 * a * (y / L ^ 2) +
        2 * a * (y / L ^ 2) := by gcongr
    _ = 2 * y / L + 30 * y * a / L ^ 2 := by ring

/-- **Brun–Titchmarsh in intervals.** There is an absolute constant `C` such that for every
real `x` and every `y > 1`, the interval `(x, x + y]` contains at most
`2y / log y + C y log log (3y) / (log y)²` primes. -/
theorem exists_primeCounting_floor_add_sub_le_two_mul_div_log_add :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ, 1 < y →
      (Nat.primeCounting ⌊x + y⌋₊ : ℝ) - Nat.primeCounting ⌊x⌋₊ ≤
        2 * y / Real.log y + C * y * Real.log (Real.log (3 * y)) / Real.log y ^ 2 := by
  -- Above some `L₀`, the level `z = √y / (log y)³` is admissible.
  have hev : ∀ᶠ L : ℝ in Filter.atTop, 1 ≤ Real.log L ∧ 12 * Real.log L ≤ L := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,
      Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 12 by norm_num),
      Filter.eventually_gt_atTop 0] with L h1 h2 h3
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith), id,
      abs_of_pos h3] at h2
    exact ⟨h1, by linarith⟩
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp hev
  have hℓ₀ : 0 < Real.log (Real.log 3) := Real.log_pos <| by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact Real.exp_one_lt_three
  refine ⟨30 + 2 * L₀ ^ 2 / Real.log (Real.log 3), by positivity, fun x y hy ↦ ?_⟩
  have hL0 : 0 < Real.log y := Real.log_pos (by linarith)
  have hlog3 : Real.log y ≤ Real.log (3 * y) := Real.log_le_log (by linarith) (by linarith)
  have hℓ : Real.log (Real.log 3) ≤ Real.log (Real.log (3 * y)) :=
    Real.log_le_log (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) (by linarith))
  rcases le_or_gt L₀ (Real.log y) with hL | hL
  · obtain ⟨h1, h12⟩ := hL₀ _ hL
    refine (primeCounting_floor_add_sub_le_of_log_le x y (by linarith) h1 h12).trans ?_
    gcongr
    exact le_add_of_nonneg_right (by positivity)
  -- Below `L₀`, the trivial bound `y + 1 ≤ 2y` suffices.
  · have hC : 2 * Real.log y ^ 2 ≤
        (30 + 2 * L₀ ^ 2 / Real.log (Real.log 3)) * Real.log (Real.log (3 * y)) :=
      calc 2 * Real.log y ^ 2 ≤ 2 * L₀ ^ 2 := by gcongr
        _ = 2 * L₀ ^ 2 / Real.log (Real.log 3) * Real.log (Real.log 3) := by field_simp
        _ ≤ 2 * L₀ ^ 2 / Real.log (Real.log 3) * Real.log (Real.log (3 * y)) := by gcongr
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by norm_num))
          (hℓ₀.le.trans hℓ)
    calc _ ≤ y + 1 := Nat.primeCounting_floor_add_sub_le_add_one x (by linarith)
      _ ≤ 2 * y := by linarith
      _ ≤ (30 + 2 * L₀ ^ 2 / Real.log (Real.log 3)) * y * Real.log (Real.log (3 * y)) /
          Real.log y ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hC (by linarith : (0 : ℝ) ≤ y)]
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

end TauCeti
