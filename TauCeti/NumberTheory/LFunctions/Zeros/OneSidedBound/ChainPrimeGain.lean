/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.LocalPrimeSum
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Remainder

/-!
# The logarithmic sum of the prime gains of a theta chain

The chain gain combines the local sums at the long rows with `k` copies of the local sums
at the direction weights, for each of `m` lifts. Multiplication by `2 log p` restores the
weight `primeWeight d 1` on powers of `p`. Summing over primes cancels these weighted sums
from the direction jet costs and the long-row contribution to the exponent.

The normalization and identities are those of `New.Data.gain`,
`New.Data.two_mul_sum_gain_mul_log` and `New.Data.mainAmount_sub_add_two_mul_sum_gain` in
lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open Finset

namespace TauCeti.OneSidedBound

variable {ι : Type*} (d : ℕ) [Fact d.Prime]

/-- The local sum at prime `p` for order `y` at place `σ`. A power `n = p^e ≤ A` contributes
`max (y / n - κ (next n σ)) 0` when `e ≥ 1`, with weight `(1 - χ(n)) / 2`, where `χ`
is the Legendre symbol modulo `d`. -/
noncomputable def placeLocalPrimeSum (A : ℕ) (κ : ι → ℝ) (next : ℕ → ι → ι)
    (y : ℝ) (σ : ι) (p : ℕ) : ℝ :=
  localPrimeSum d p (fun n ↦ if n ≤ A then max (y / n - κ (next n σ)) 0 else 0)

/-- Express the local sum at a place using the cutoff on its kernel. -/
theorem placeLocalPrimeSum_def (A : ℕ) (κ : ι → ℝ) (next : ℕ → ι → ι)
    (y : ℝ) (σ : ι) (p : ℕ) :
    placeLocalPrimeSum d A κ next y σ p =
      localPrimeSum d p (fun n ↦ if n ≤ A then max (y / n - κ (next n σ)) 0 else 0) := (rfl)

variable {A : ℕ} {κ : ι → ℝ} {next : ℕ → ι → ι} {y : ℝ} {σ : ι}

/-- The local sum at a place is nonnegative because its kernel uses positive parts. -/
theorem placeLocalPrimeSum_nonneg (p : ℕ) : 0 ≤ placeLocalPrimeSum d A κ next y σ p := by
  rw [placeLocalPrimeSum_def]
  exact localPrimeSum_nonneg fun _ _ ↦ ite_nonneg (le_max_right _ _) le_rfl

/-- The local sum vanishes at `p ≥ X` if the weights reached by the powers of `p` up to `A`
are at least `y / X`. -/
theorem placeLocalPrimeSum_eq_zero_of_le {X : ℝ} {p : ℕ} (hXp : X ≤ p)
    (hX : 0 < X) (hy : 0 ≤ y) (hκ : ∀ e > 0, p ^ e ≤ A → y / X ≤ κ (next (p ^ e) σ)) :
    placeLocalPrimeSum d A κ next y σ p = 0 := by
  rw [placeLocalPrimeSum_def]
  refine localPrimeSum_eq_zero_of_lt_prime (N := 0) (Nat.cast_pos.mp (hX.trans_le hXp))
    (fun e he _ ↦ ?_)
  by_cases hA : p ^ e ≤ A
  · have hpe : X ≤ (p ^ e : ℕ) := hXp.trans (by exact_mod_cast Nat.le_self_pow he.ne' p)
    rw [ite_eq_left hA, max_eq_right (sub_nonpos.mpr
      ((div_le_div_of_nonneg_left hy hX hpe).trans (hκ e he hA)))]
  · exact ite_eq_right hA

/-- Regroup the Legendre-weighted von Mangoldt sum at a place by prime, for any order `y`. -/
theorem sum_primeWeight_mul_max_eq_sum_placeLocalPrimeSum :
    ∑ n ∈ Icc 1 A, primeWeight d 1 n * max (y / n - κ (next n σ)) 0 =
      ∑ p ∈ Nat.primesLE A, (2 * Real.log p) * placeLocalPrimeSum d A κ next y σ p := by
  simp only [placeLocalPrimeSum_def]
  rw [← sum_vonMangoldt_mul_one_sub_legendreSym_eq_sum_localPrimeSum d (N := A) (A := A)
    le_rfl (fun n hn _ ↦ ite_eq_right (not_le.mpr hn))]
  exact sum_congr rfl fun n hn ↦ by rw [ite_eq_left (mem_Icc.mp hn).2, primeWeight_one]

variable [Fintype ι]

/-- The total of the local prime sums at the direction places, taking order `κ σ` at `σ`. -/
noncomputable def localPrimeSumTotal (A : ℕ) (κ : ι → ℝ) (next : ℕ → ι → ι) (p : ℕ) : ℝ :=
  ∑ σ, placeLocalPrimeSum d A κ next (κ σ) σ p

/-- Expand the total over direction places. -/
theorem localPrimeSumTotal_def (A : ℕ) (κ : ι → ℝ) (next : ℕ → ι → ι) (p : ℕ) :
    localPrimeSumTotal d A κ next p = ∑ σ, placeLocalPrimeSum d A κ next (κ σ) σ p := (rfl)

/-- The total of the local prime sums at the direction places is nonnegative. -/
theorem localPrimeSumTotal_nonneg (p : ℕ) : 0 ≤ localPrimeSumTotal d A κ next p := by
  rw [localPrimeSumTotal_def]
  exact sum_nonneg fun _ _ ↦ placeLocalPrimeSum_nonneg d p

/-- The gain at `p` for `m` lifts, each with an order-`a` row at every place in `S` and `k`
direction rows of order `κ σ` at every `σ`. Each row uses `placeLocalPrimeSum`: the positive
parts on powers up to `A` carry the Legendre half-weight `(1 - χ(p^e)) / 2`. -/
noncomputable def chainPrimeGain (A m k : ℕ) (S : Finset ι) (a : ℝ)
    (κ : ι → ℝ) (next : ℕ → ι → ι) (p : ℕ) : ℝ :=
  (m : ℝ) * ((∑ σ ∈ S, placeLocalPrimeSum d A κ next a σ p) +
    (k : ℝ) * localPrimeSumTotal d A κ next p)

/-- Expand a chain gain in terms of the contributions from the long rows and the directions. -/
theorem chainPrimeGain_def (A m k : ℕ) (S : Finset ι) (a : ℝ)
    (κ : ι → ℝ) (next : ℕ → ι → ι) (p : ℕ) :
    chainPrimeGain d A m k S a κ next p =
      (m : ℝ) * ((∑ σ ∈ S, placeLocalPrimeSum d A κ next a σ p) +
        (k : ℝ) * localPrimeSumTotal d A κ next p) := (rfl)

variable {m k : ℕ} {S : Finset ι} {a : ℝ}

/-- The gain is nonnegative: it adds local sums with natural multiplicities. -/
theorem chainPrimeGain_nonneg (p : ℕ) : 0 ≤ chainPrimeGain d A m k S a κ next p := by
  rw [chainPrimeGain_def]
  exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg
    (sum_nonneg fun _ _ ↦ placeLocalPrimeSum_nonneg d p)
    (mul_nonneg (Nat.cast_nonneg _) (localPrimeSumTotal_nonneg d p)))

/-- A split prime contributes no gain, since its local prime sums vanish. -/
@[simp] theorem chainPrimeGain_eq_zero_of_legendreSym_eq_one {p : ℕ} (hp : legendreSym d p = 1) :
    chainPrimeGain d A m k S a κ next p = 0 := by
  simp only [chainPrimeGain_def, localPrimeSumTotal_def, placeLocalPrimeSum_def,
    localPrimeSum_eq_zero_of_legendreSym_eq_one hp, sum_const_zero, mul_zero, add_zero]

/-- A uniform lower bound on the weights forces the positive parts in the gain to vanish
at primes at or above the second cutoff `X`. -/
theorem chainPrimeGain_eq_zero_of_le {X : ℝ} {p : ℕ} (hXp : X ≤ p)
    (hX : 0 < X) (ha : 0 ≤ a) (hκ : ∀ σ, a / X ≤ κ σ) (hκ' : ∀ σ, κ σ ≤ a) :
    chainPrimeGain d A m k S a κ next p = 0 := by
  have hzero (y : ℝ) (hy₀ : 0 ≤ y) (hy : y ≤ a) (σ : ι) :
      placeLocalPrimeSum d A κ next y σ p = 0 :=
    placeLocalPrimeSum_eq_zero_of_le d hXp hX hy₀ fun _ _ _ ↦
      (div_le_div_of_nonneg_right hy hX.le).trans (hκ _)
  have hdir (σ : ι) : placeLocalPrimeSum d A κ next (κ σ) σ p = 0 :=
    hzero (κ σ) ((div_nonneg ha hX.le).trans (hκ σ)) (hκ' σ) σ
  simp only [chainPrimeGain_def, localPrimeSumTotal_def, hzero a ha le_rfl, hdir,
    sum_const_zero, mul_zero, add_zero]

/-- Twice the log-weighted sum of the gains restores the two `primeWeight d 1` sums.
Only primes up to `A`, the cutoff for their powers, are required. -/
theorem two_mul_sum_chainPrimeGain_mul_log :
    2 * (∑ p ∈ Nat.primesLE A, chainPrimeGain d A m k S a κ next p * Real.log p) =
      (m : ℝ) * ((∑ σ ∈ S, ∑ n ∈ Icc 1 A, primeWeight d 1 n * max (a / n - κ (next n σ)) 0) +
        (k : ℝ) * ∑ σ, ∑ n ∈ Icc 1 A, primeWeight d 1 n * max (κ σ / n - κ (next n σ)) 0) := by
  calc
    _ = (m : ℝ) * ∑ p ∈ Nat.primesLE A,
        ((∑ σ ∈ S, (2 * Real.log p) * placeLocalPrimeSum d A κ next a σ p) +
          (k : ℝ) * ∑ σ, (2 * Real.log p) * placeLocalPrimeSum d A κ next (κ σ) σ p) := by
      conv_lhs => rw [mul_sum]
      conv_rhs => rw [mul_sum]
      refine sum_congr rfl fun p _ ↦ ?_
      simp only [chainPrimeGain_def, localPrimeSumTotal_def, ← mul_sum]
      ring
    _ = _ := by
      simp only [sum_add_distrib, ← mul_sum (a := (k : ℝ)), sum_comm (s := Nat.primesLE A),
        sum_primeWeight_mul_max_eq_sum_placeLocalPrimeSum]

/-- Only nonsplit primes strictly below `X` are needed to recover the `primeWeight d 1` sums
when all the weights lie between `a / X` and `a`. -/
theorem two_mul_sum_smallNonsplit_chainPrimeGain_mul_log {X : ℝ} (hX : 0 < X) (ha : 0 ≤ a)
    (hκ : ∀ σ, a / X ≤ κ σ) (hκ' : ∀ σ, κ σ ≤ a) :
    2 * (∑ p ∈ (Nat.primesLE A).filter (fun p : ℕ ↦ (p : ℝ) < X ∧ legendreSym d p ≠ 1),
      chainPrimeGain d A m k S a κ next p * Real.log p) =
    (m : ℝ) * ((∑ σ ∈ S, ∑ n ∈ Icc 1 A, primeWeight d 1 n * max (a / n - κ (next n σ)) 0) +
      (k : ℝ) * ∑ σ, ∑ n ∈ Icc 1 A, primeWeight d 1 n * max (κ σ / n - κ (next n σ)) 0) := by
  classical
  rw [sum_filter_of_ne (fun p _ hp ↦ ?_), two_mul_sum_chainPrimeGain_mul_log]
  by_contra hnot
  apply hp
  simp only [not_and_or, not_lt, not_ne_iff] at hnot
  rcases hnot with hle | hsplit
  · rw [chainPrimeGain_eq_zero_of_le d hle hX ha hκ hκ', zero_mul]
  · rw [chainPrimeGain_eq_zero_of_legendreSym_eq_one d hsplit, zero_mul]

/-- For `0 < X`, `0 ≤ a` and `a / X ≤ κ σ ≤ a`, the doubled log-weighted gain over
nonsplit primes below `X` cancels the weighted prime sums subtracted from the direction jet
costs and from the long-row term. The remaining exponent is the `m * k`-scaled sum of the jet
costs plus `m` times `expected` for each place in `S`. -/
theorem mul_sum_sub_sub_add_two_mul_sum_chainPrimeGain_eq {X : ℝ} (hX : 0 < X) (ha : 0 ≤ a)
    (hκ : ∀ σ, a / X ≤ κ σ) (hκ' : ∀ σ, κ σ ≤ a) (jet : ι → ℝ) (expected : ℝ) :
    (m : ℝ) * k * (∑ σ, (jet σ -
        ∑ n ∈ Icc 1 A, primeWeight d 1 n * max (κ σ / n - κ (next n σ)) 0)) -
      (m : ℝ) * (∑ σ ∈ S, ((∑ n ∈ Icc 1 A, primeWeight d 1 n * max (a / n - κ (next n σ)) 0) -
        expected)) +
      2 * (∑ p ∈ (Nat.primesLE A).filter (fun p : ℕ ↦ (p : ℝ) < X ∧ legendreSym d p ≠ 1),
        chainPrimeGain d A m k S a κ next p * Real.log p) =
    (m : ℝ) * S.card * expected + (m : ℝ) * k * ∑ σ, jet σ := by
  simp only [two_mul_sum_smallNonsplit_chainPrimeGain_mul_log d hX ha hκ hκ',
    sum_sub_distrib, sum_const, nsmul_eq_mul]
  ring

end TauCeti.OneSidedBound
