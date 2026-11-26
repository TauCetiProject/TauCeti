/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Remainder
import TauCeti.NumberTheory.SumPrimePow

/-!
# The logarithmic sum of the prime gains of a theta chain

The chain gain combines the local sums at the long rows with `k` copies of the local sums
at the direction weights, for each of `m` lifts. Multiplication by `2 log p` restores the
signed von Mangoldt weight on powers of `p`. Summing over primes therefore cancels the
finite prime sums in the exponent built from the main amount and the total remainder.

The normalization and identities are those of `New.Data.gain`,
`New.Data.two_mul_sum_gain_mul_log` and `New.Data.mainAmount_sub_add_two_mul_sum_gain` in
lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open ArithmeticFunction Finset

namespace TauCeti.OneSidedBound

variable {ι : Type*} (d : ℕ) [Fact d.Prime]

/-- The signed prime sum at a place. The weight at `next n σ` is subtracted from `y/n`
before taking the positive part, so the effective cutoff may vary with `n`. -/
noncomputable def placePrimeSum (A : ℕ) (κ : ι → ℝ) (next : ℕ → ι → ι) (y : ℝ) (σ : ι) : ℝ :=
  ∑ n ∈ Icc 1 A, primeWeight d 1 n * max (y / n - κ (next n σ)) 0

/-- Expand the prime sum at a place as a signed von Mangoldt sum. -/
theorem placePrimeSum_def (A : ℕ) (κ : ι → ℝ) (next : ℕ → ι → ι) (y : ℝ) (σ : ι) :
    placePrimeSum d A κ next y σ =
      ∑ n ∈ Icc 1 A, primeWeight d 1 n * max (y / n - κ (next n σ)) 0 := (rfl)

variable [Fintype ι]

/-- The total gain at `p` for `m` lifts, each with a long row at the places in `S` and
`k` direction rows at every place. The map `next n` supplies the place reached by `n`.
For a prime `p`, `A` bounds the powers of `p` in the sum. -/
noncomputable def chainPrimeGain (A m k : ℕ) (S : Finset ι) (a : ℝ)
    (κ : ι → ℝ) (next : ℕ → ι → ι) (p : ℕ) : ℝ :=
  (m : ℝ) * ∑ e ∈ Icc 1 (p.log A),
    ((1 - (legendreSym d (p ^ e : ℕ) : ℝ)) / 2) *
      ((∑ σ ∈ S, max (a / (p ^ e : ℕ) - κ (next (p ^ e) σ)) 0) +
       (k : ℝ) * ∑ σ, max (κ σ / (p ^ e : ℕ) - κ (next (p ^ e) σ)) 0)

/-- Expand a chain gain as a finite sum over the exponents of its prime. -/
theorem chainPrimeGain_def (A m k : ℕ) (S : Finset ι) (a : ℝ)
    (κ : ι → ℝ) (next : ℕ → ι → ι) (p : ℕ) :
    chainPrimeGain d A m k S a κ next p =
      (m : ℝ) * ∑ e ∈ Icc 1 (p.log A),
        ((1 - (legendreSym d (p ^ e : ℕ) : ℝ)) / 2) *
          ((∑ σ ∈ S, max (a / (p ^ e : ℕ) - κ (next (p ^ e) σ)) 0) +
           (k : ℝ) * ∑ σ, max (κ σ / (p ^ e : ℕ) - κ (next (p ^ e) σ)) 0) := (rfl)

variable {A m k : ℕ} {S : Finset ι} {a : ℝ} {κ : ι → ℝ} {next : ℕ → ι → ι}

/-- A split prime contributes no gain, since all its powers have Legendre symbol one. -/
theorem chainPrimeGain_eq_zero_of_legendreSym_eq_one {p : ℕ} (hp : legendreSym d p = 1) :
    chainPrimeGain d A m k S a κ next p = 0 := by
  have hs (e : ℕ) : legendreSym d (p ^ e : ℕ) = 1 := by
    simpa only [Nat.cast_pow, legendreSym.hom_apply, hp, one_pow] using
      (map_pow (legendreSym.hom d) (p : ℤ) e)
  simp only [chainPrimeGain_def, hs, Int.cast_one, sub_self, zero_div, zero_mul, sum_const_zero,
    mul_zero]

/-- A uniform lower bound on the weights forces the positive parts in the gain to vanish
at primes at or above the second cutoff `X`. -/
theorem chainPrimeGain_eq_zero_of_le {X : ℝ} {p : ℕ} (hXp : X ≤ p)
    (hX : 0 < X) (ha : 0 ≤ a) (hκ : ∀ σ, a / X ≤ κ σ) (hκ' : ∀ σ, κ σ ≤ a) :
    chainPrimeGain d A m k S a κ next p = 0 := by
  rw [chainPrimeGain_def]
  refine mul_eq_zero_of_right _ (sum_eq_zero fun e he ↦ ?_)
  have he₀ : e ≠ 0 := Nat.ne_zero_of_lt (mem_Icc.mp he).1
  have hpe : X ≤ (p ^ e : ℕ) := hXp.trans (by exact_mod_cast (Nat.le_self_pow he₀ p))
  have hbound (y : ℝ) (hy : y ≤ a) (σ : ι) :
      max (y / (p ^ e : ℕ) - κ (next (p ^ e) σ)) 0 = 0 := by
    have hpos : 0 < ((p ^ e : ℕ) : ℝ) := hX.trans_le hpe
    refine max_eq_right (sub_nonpos.mpr ?_)
    exact ((div_le_div_of_nonneg_right hy hpos.le).trans
      (div_le_div_of_nonneg_left ha hX hpe)).trans (hκ _)
  simp only [hbound a le_rfl, fun σ ↦ hbound (κ σ) (hκ' σ) σ, sum_const_zero, mul_zero, add_zero]

/-- Twice the log-weighted sum of the gains restores the two signed von Mangoldt sums.
The outer sum needs only the primes up to `A`, the cutoff for the original prime powers. -/
theorem two_mul_sum_chainPrimeGain_mul_log :
    2 * (∑ p ∈ Nat.primesLE A, chainPrimeGain d A m k S a κ next p * Real.log p) =
      (m : ℝ) * ((∑ σ ∈ S, placePrimeSum d A κ next a σ) +
        (k : ℝ) * ∑ σ, placePrimeSum d A κ next (κ σ) σ) := by
  let f (n : ℕ) := (∑ σ ∈ S, max (a / n - κ (next n σ)) 0) +
    (k : ℝ) * ∑ σ, max (κ σ / n - κ (next n σ)) 0
  have hsplit : (∑ n ∈ Icc 1 A, primeWeight d 1 n * f n) =
      ∑ p ∈ Nat.primesLE A, ∑ e ∈ Icc 1 (p.log A), primeWeight d 1 (p ^ e) * f (p ^ e) :=
    Nat.sum_Icc_eq_sum_primesLE_sum_Icc_log
      (fun n hn ↦ by simp [primeWeight_def, vonMangoldt_eq_zero_iff.mpr hn]) A
  calc
    _ = (m : ℝ) * ∑ p ∈ Nat.primesLE A, ∑ e ∈ Icc 1 (p.log A),
        primeWeight d 1 (p ^ e) * f (p ^ e) := by
      rw [mul_sum, mul_sum]
      refine sum_congr rfl fun p hp ↦ ?_
      rw [chainPrimeGain_def, mul_assoc, sum_mul, mul_sum, mul_sum, mul_sum]
      refine sum_congr rfl fun e he ↦ ?_
      have hp' := Nat.prime_of_mem_primesLE hp
      have he₀ : e ≠ 0 := Nat.ne_zero_of_lt (mem_Icc.mp he).1
      have hz : (↑(p ^ e : ℕ) : ZMod 1) = 1 := Subsingleton.elim _ _
      rw [primeWeight_def, ite_eq_left hz, vonMangoldt_apply_pow he₀, vonMangoldt_apply_prime hp']
      dsimp only [f]
      ring
    _ = (m : ℝ) * ∑ n ∈ Icc 1 A, primeWeight d 1 n * f n := by rw [hsplit]
    _ = _ := by
      have hf (n : ℕ) : primeWeight d 1 n * f n =
          (∑ σ ∈ S, primeWeight d 1 n * max (a / n - κ (next n σ)) 0) +
          (k : ℝ) * ∑ σ, primeWeight d 1 n * max (κ σ / n - κ (next n σ)) 0 := by
        simp only [f, mul_add, mul_left_comm (primeWeight d 1 n) (k : ℝ), mul_sum]
      simp_rw [placePrimeSum_def, hf]
      rw [sum_add_distrib, ← mul_sum, sum_comm (s := Icc 1 A) (t := S),
        sum_comm (s := Icc 1 A) (t := univ)]

/-- Only nonsplit primes strictly below `X` are needed to recover the signed prime sums
when all the weights lie between `a / X` and `a`. -/
theorem two_mul_sum_smallNonsplit_chainPrimeGain_mul_log {X : ℝ} (hX : 0 < X) (ha : 0 ≤ a)
    (hκ : ∀ σ, a / X ≤ κ σ) (hκ' : ∀ σ, κ σ ≤ a) :
    2 * (∑ p ∈ (Nat.primesLE A).filter (fun p : ℕ ↦ (p : ℝ) < X ∧ legendreSym d p ≠ 1),
      chainPrimeGain d A m k S a κ next p * Real.log p) =
    (m : ℝ) * ((∑ σ ∈ S, placePrimeSum d A κ next a σ) +
      (k : ℝ) * ∑ σ, placePrimeSum d A κ next (κ σ) σ) := by
  classical
  rw [sum_filter_of_ne (fun p _ hp ↦ ?_), two_mul_sum_chainPrimeGain_mul_log]
  by_contra hnot
  apply hp
  simp only [not_and_or, not_lt, not_ne_iff] at hnot
  rcases hnot with hle | hsplit
  · rw [chainPrimeGain_eq_zero_of_le d hle hX ha hκ hκ', zero_mul]
  · rw [chainPrimeGain_eq_zero_of_legendreSym_eq_one d hsplit, zero_mul]

/-- The exponent for the composite lift can be written without prime sums. Adding twice the
log-weighted gains over the small nonsplit primes to the main amount minus `m` times the
remainder leaves just the expected long-row sum and the direction jet costs. -/
theorem mainAmount_sub_add_two_mul_sum_chainPrimeGain {X : ℝ} (hX : 0 < X) (ha : 0 ≤ a)
    (hκ : ∀ σ, a / X ≤ κ σ) (hκ' : ∀ σ, κ σ ≤ a) (jet : ι → ℝ) (expected : ℝ) :
    (m : ℝ) * k * (∑ σ, (jet σ - placePrimeSum d A κ next (κ σ) σ)) -
      (m : ℝ) * (∑ σ ∈ S, (placePrimeSum d A κ next a σ - expected)) +
      2 * (∑ p ∈ (Nat.primesLE A).filter (fun p : ℕ ↦ (p : ℝ) < X ∧ legendreSym d p ≠ 1),
        chainPrimeGain d A m k S a κ next p * Real.log p) =
    (m : ℝ) * S.card * expected + (m : ℝ) * k * ∑ σ, jet σ := by
  rw [two_mul_sum_smallNonsplit_chainPrimeGain_mul_log d hX ha hκ hκ',
    sum_sub_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul]
  ring

end TauCeti.OneSidedBound
