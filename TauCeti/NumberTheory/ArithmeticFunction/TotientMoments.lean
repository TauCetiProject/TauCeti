/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.SumPrimeReciprocals
import TauCeti.NumberTheory.ArithmeticFunction.Misc
import TauCeti.NumberTheory.Divisors
import TauCeti.NumberTheory.EulerProduct.Squarefree

/-!
# Divisor moments over reciprocal totients

For every fixed `j ≥ 0`, the sum `∑_{1 ≤ q ≤ Q} τ(q) ^ j / φ(q)` of the `j`-th power of the
number-of-divisors function against the reciprocal of Euler's totient is at most
`C_j (1 + log Q) ^ (2 ^ j)`. The proof has two parts.

* The sum `∑_{q ≤ N} τ(q) ^ j / q` is at most `H_N ^ (2 ^ j)`, by induction on `j`: since
  `τ(d e) ≤ τ(d) τ(e)` (`Nat.card_divisors_mul_le`), one has
  `τ(q) ^ (j + 1) / q ≤ ∑_{d e = q} (τ(d) ^ j / d) (τ(e) ^ j / e)`, and summing over `q ≤ N` is
  bounded by the square of the sum for `j`.
* Writing `q / φ(q) = ∑_{d ∣ q} μ(d)² / φ(d)` and `q = d l`, the sum against `1 / φ(q)` is at most
  `K_j ∑_{l ≤ N} τ(l) ^ j / l` with `K_j = ∑_d μ(d)² τ(d) ^ j / (d φ(d))`, a series that converges
  because its terms are supported on squarefree `d`, multiplicative, and `O(2 ^ j / p ^ 2)` at the
  primes.

Since every term is nonnegative, the same bound holds for the sum restricted to `q` coprime to
any fixed `s`, uniformly in `s`.

## Main results

* `TauCeti.sum_Ioc_card_divisors_pow_div_le_harmonic_pow`:
  `∑_{q ≤ N} τ(q) ^ j / q ≤ H_N ^ (2 ^ j)`.
* `TauCeti.div_totient_eq_sum_divisors_moebius_sq_div_totient`:
  `n / φ(n) = ∑_{d ∣ n} μ(d)² / φ(d)`.
* `TauCeti.summable_moebius_sq_mul_card_divisors_pow_div`: the series `K_j` converges.
* `TauCeti.sum_Ioc_card_divisors_pow_div_totient_le`:
  `∑_{q ≤ N} τ(q) ^ j / φ(q) ≤ K_j H_N ^ (2 ^ j)`.
* `TauCeti.exists_sum_Ioc_card_divisors_pow_div_totient_le`: the bound
  `C (1 + log Q) ^ (2 ^ j)` with a real cutoff `Q ≥ 1`, also for the sum over `q` coprime to `s`.

## References

* K. S. Kedlaya, *Notes on analytic number theory*, Chapter 18, §18.1, proof of Theorem 18.3.
-/

public section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TauCeti

/-- The arithmetic function `n ↦ τ(n) ^ j / n`. -/
private noncomputable def divisorPowDiv (j : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ (#n.divisors : ℝ) ^ j / n, by simp⟩

private theorem divisorPowDiv_apply (j n : ℕ) :
    divisorPowDiv j n = (#n.divisors : ℝ) ^ j / n := rfl

private theorem divisorPowDiv_nonneg (j n : ℕ) : 0 ≤ divisorPowDiv j n := by
  rw [divisorPowDiv_apply]
  positivity

/-- `τ(n) ^ (j + 1) / n ≤ ∑_{d e = n} (τ(d) ^ j / d) (τ(e) ^ j / e)`. -/
private theorem divisorPowDiv_succ_le (j n : ℕ) :
    divisorPowDiv (j + 1) n ≤ (divisorPowDiv j * divisorPowDiv j) n := by
  have hsum : divisorPowDiv (j + 1) n = ∑ _d ∈ n.divisors, (#n.divisors : ℝ) ^ j / n := by
    rw [sum_const, nsmul_eq_mul, divisorPowDiv_apply, pow_succ]
    ring
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal fun a b ↦ divisorPowDiv j a * divisorPowDiv j b, hsum]
  refine sum_le_sum fun d hd ↦ ?_
  obtain ⟨e, rfl⟩ := Nat.dvd_of_mem_divisors hd
  have hd0 : d ≠ 0 := left_ne_zero_of_mul (Nat.ne_zero_of_mem_divisors hd)
  have hle : (#(d * e).divisors : ℝ) ^ j ≤ (#d.divisors : ℝ) ^ j * (#e.divisors : ℝ) ^ j := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (mod_cast Nat.card_divisors_mul_le d e) j
  rw [Nat.mul_div_cancel_left e (Nat.pos_of_ne_zero hd0), divisorPowDiv_apply,
    divisorPowDiv_apply, div_mul_div_comm, ← Nat.cast_mul]
  exact div_le_div_of_nonneg_right hle (Nat.cast_nonneg _)

/-- **Divisor moments against `1 / n`.** For all `j` and `N`,
`∑_{1 ≤ n ≤ N} τ(n) ^ j / n ≤ H_N ^ (2 ^ j)`, where `H_N` is the harmonic number. -/
theorem sum_Ioc_card_divisors_pow_div_le_harmonic_pow (j N : ℕ) :
    ∑ n ∈ Ioc 0 N, (#n.divisors : ℝ) ^ j / n ≤ (harmonic N : ℝ) ^ 2 ^ j := by
  induction j with
  | zero =>
    simp only [pow_zero, pow_one, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast, one_div, ← Icc_add_one_left_eq_Ioc, zero_add]
    exact le_rfl
  | succ j ih =>
    have hnonneg : 0 ≤ ∑ n ∈ Ioc 0 N, (#n.divisors : ℝ) ^ j / n :=
      sum_nonneg fun n _ ↦ divisorPowDiv_nonneg j n
    calc ∑ n ∈ Ioc 0 N, (#n.divisors : ℝ) ^ (j + 1) / n
        ≤ ∑ n ∈ Ioc 0 N, (divisorPowDiv j * divisorPowDiv j) n • (1 : ℝ) :=
          sum_le_sum fun n _ ↦ by
            rw [smul_eq_mul, mul_one]
            exact divisorPowDiv_succ_le j n
      _ = ∑ m ∈ Ioc 0 N, divisorPowDiv j m • ∑ l ∈ Ioc 0 (N / m), divisorPowDiv j l • (1 : ℝ) :=
          sum_Ioc_mul_smul_eq_sum_sum _ _ _ N
      _ ≤ ∑ m ∈ Ioc 0 N, divisorPowDiv j m * ∑ l ∈ Ioc 0 N, divisorPowDiv j l :=
          sum_le_sum fun m _ ↦ by
            rw [smul_eq_mul]
            refine mul_le_mul_of_nonneg_left ?_ (divisorPowDiv_nonneg j m)
            simp only [smul_eq_mul, mul_one]
            exact sum_le_sum_of_subset_of_nonneg
              (Ioc_subset_Ioc_right (Nat.div_le_self N m)) fun l _ _ ↦ divisorPowDiv_nonneg j l
      _ = (∑ n ∈ Ioc 0 N, (#n.divisors : ℝ) ^ j / n) ^ 2 := by
          rw [← sum_mul, sq]
          rfl
      _ ≤ ((harmonic N : ℝ) ^ 2 ^ j) ^ 2 := pow_le_pow_left₀ hnonneg ih 2
      _ = (harmonic N : ℝ) ^ 2 ^ (j + 1) := by rw [← pow_mul, pow_succ]

/-- The arithmetic function `d ↦ μ(d)² / φ(d)`. -/
private noncomputable def moebiusSqDivTotient : ArithmeticFunction ℝ :=
  ⟨fun d ↦ (μ d : ℝ) ^ 2 / d.totient, by simp⟩

private theorem moebiusSqDivTotient_apply (d : ℕ) :
    moebiusSqDivTotient d = (μ d : ℝ) ^ 2 / d.totient := rfl

private theorem moebiusSqDivTotient_nonneg (d : ℕ) : 0 ≤ moebiusSqDivTotient d := by
  rw [moebiusSqDivTotient_apply]
  positivity

private theorem isMultiplicative_moebiusSqDivTotient : moebiusSqDivTotient.IsMultiplicative := by
  refine ⟨by simp [moebiusSqDivTotient_apply], fun {m n} hmn ↦ ?_⟩
  simp only [moebiusSqDivTotient_apply, isMultiplicative_moebius.map_mul_of_coprime hmn,
    Nat.totient_mul hmn, Int.cast_mul, Nat.cast_mul, mul_pow]
  rw [mul_div_mul_comm]

/-- The arithmetic function `n ↦ n / φ(n)`. -/
private noncomputable def divTotient : ArithmeticFunction ℝ :=
  ⟨fun n ↦ (n : ℝ) / n.totient, by simp⟩

private theorem isMultiplicative_divTotient : divTotient.IsMultiplicative := by
  refine ⟨by simp [divTotient], fun {m n} hmn ↦ ?_⟩
  simp only [divTotient, ArithmeticFunction.coe_mk, Nat.totient_mul hmn, Nat.cast_mul]
  rw [mul_div_mul_comm]

/-- **The totient quotient as a sum over squarefree divisors.** For `n ≠ 0`,
`n / φ(n) = ∑_{d ∣ n} μ(d)² / φ(d)`. -/
theorem div_totient_eq_sum_divisors_moebius_sq_div_totient (n : ℕ) :
    (n : ℝ) / n.totient = ∑ d ∈ n.divisors, (μ d : ℝ) ^ 2 / d.totient := by
  have hmul : (moebiusSqDivTotient * (ζ : ArithmeticFunction ℝ)).IsMultiplicative :=
    isMultiplicative_moebiusSqDivTotient.mul isMultiplicative_zeta.natCast
  have key : moebiusSqDivTotient * (ζ : ArithmeticFunction ℝ) = divTotient := by
    refine (hmul.eq_iff_eq_on_prime_powers _ _ isMultiplicative_divTotient).2 fun p i hp ↦ ?_
    have hp1 : ((p : ℝ) - 1) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hp.one_lt.ne')
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [moebiusSqDivTotient_apply, divTotient]
    obtain ⟨i, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rw [sum_range_succ', sum_range_succ', sum_eq_zero fun l _ ↦ ?_]
    · simp only [moebiusSqDivTotient_apply, divTotient, ArithmeticFunction.coe_mk, zero_add,
        pow_one, pow_zero, moebius_apply_prime hp, isMultiplicative_moebius.map_one,
        Nat.totient_prime hp, Nat.totient_one, Nat.totient_prime_pow_succ hp i, Nat.cast_mul,
        Nat.cast_pow, Nat.cast_pred hp.pos, Int.cast_neg, Int.cast_one, Nat.cast_one]
      field_simp
      ring
    · rw [moebiusSqDivTotient_apply, moebius_apply_prime_pow hp (by omega),
        ite_eq_right (by omega)]
      simp
  have h := congrArg (fun f : ArithmeticFunction ℝ ↦ f n) key
  rw [coe_mul_zeta_apply] at h
  exact h.symm

/-- `τ(d l) ^ j / (d l) ≤ (τ(d) ^ j / d) (τ(l) ^ j / l)`, for all `d` and `l`. -/
private theorem divisorPowDiv_mul_le (j d l : ℕ) :
    divisorPowDiv j (d * l) ≤ divisorPowDiv j d * divisorPowDiv j l := by
  have hle : (#(d * l).divisors : ℝ) ^ j ≤ (#d.divisors : ℝ) ^ j * (#l.divisors : ℝ) ^ j := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (mod_cast Nat.card_divisors_mul_le d l) j
  rw [divisorPowDiv_apply, divisorPowDiv_apply, divisorPowDiv_apply, div_mul_div_comm,
    ← Nat.cast_mul]
  exact div_le_div_of_nonneg_right hle (Nat.cast_nonneg _)

/-- The weight `μ(d)² τ(d) ^ j / (d φ(d))` as a product of the two auxiliary functions. -/
private theorem moebiusSqDivTotient_mul_divisorPowDiv (j d : ℕ) :
    moebiusSqDivTotient d * divisorPowDiv j d =
      (μ d : ℝ) ^ 2 * (#d.divisors : ℝ) ^ j / (d * d.totient) := by
  rw [moebiusSqDivTotient_apply, divisorPowDiv_apply, div_mul_div_comm, mul_comm (d : ℝ)]

/-- **The squarefree divisor weight is summable.** For every `j`, the series
`∑_d μ(d)² τ(d) ^ j / (d φ(d))` converges: its terms are supported on squarefree `d`, are
multiplicative, and are `2 ^ j / (p (p - 1))` at a prime `p`. -/
theorem summable_moebius_sq_mul_card_divisors_pow_div (j : ℕ) :
    Summable fun d : ℕ ↦ (μ d : ℝ) ^ 2 * (#d.divisors : ℝ) ^ j / (d * d.totient) := by
  simp_rw [← moebiusSqDivTotient_mul_divisorPowDiv]
  refine summable_of_summable_primes_of_squarefree
    (fun n ↦ mul_nonneg (moebiusSqDivTotient_nonneg n) (divisorPowDiv_nonneg j n)) ?_ ?_ ?_ ?_
  · simp [moebiusSqDivTotient_apply, divisorPowDiv_apply]
  · intro m n hmn
    rw [isMultiplicative_moebiusSqDivTotient.map_mul_of_coprime hmn, divisorPowDiv_apply,
      divisorPowDiv_apply, divisorPowDiv_apply, hmn.card_divisors_mul, Nat.cast_mul,
      Nat.cast_mul, mul_pow, ← div_mul_div_comm]
    ring
  · intro p k hp hk
    rw [moebiusSqDivTotient_apply, moebius_apply_prime_pow hp (by omega),
      ite_eq_right (by omega)]
    simp
  · have hsum : Summable fun p : Nat.Primes ↦ (2 : ℝ) ^ (j + 1) * ((p : ℕ) : ℝ) ^ (-2 : ℝ) :=
      (Nat.Primes.summable_rpow.2 (by norm_num)).mul_left _
    refine hsum.of_nonneg_of_le (fun p ↦ mul_nonneg (moebiusSqDivTotient_nonneg p)
      (divisorPowDiv_nonneg j p)) fun p ↦ ?_
    have hp := p.prop
    have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast hp.two_le
    rw [moebiusSqDivTotient_apply, divisorPowDiv_apply, moebius_apply_prime hp,
      Nat.totient_prime hp, hp.divisors, card_pair hp.one_lt.ne, Nat.cast_pred hp.pos,
      Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_two]
    calc (((-1 : ℤ) : ℝ)) ^ 2 / (((p : ℕ) : ℝ) - 1) * (((2 : ℕ) : ℝ) ^ j / ((p : ℕ) : ℝ))
        = (2 : ℝ) ^ j / ((((p : ℕ) : ℝ) - 1) * (p : ℕ)) := by
          push_cast
          rw [div_mul_div_comm]
          congr 1
          ring
      _ ≤ (2 : ℝ) ^ j / (((p : ℕ) : ℝ) ^ 2 / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
      _ = (2 : ℝ) ^ (j + 1) * (((p : ℕ) : ℝ) ^ 2)⁻¹ := by
          rw [div_div_eq_mul_div, div_eq_mul_inv, pow_succ (2 : ℝ) j]

/-- **Divisor moments over reciprocal totients.** For all `j` and `N`,
`∑_{1 ≤ q ≤ N} τ(q) ^ j / φ(q) ≤ K_j H_N ^ (2 ^ j)`, where `H_N` is the harmonic number and
`K_j = ∑_d μ(d)² τ(d) ^ j / (d φ(d))` is a convergent series depending only on `j`. -/
theorem sum_Ioc_card_divisors_pow_div_totient_le (j N : ℕ) :
    ∑ q ∈ Ioc 0 N, (#q.divisors : ℝ) ^ j / q.totient ≤
      (∑' d : ℕ, (μ d : ℝ) ^ 2 * (#d.divisors : ℝ) ^ j / (d * d.totient)) *
        (harmonic N : ℝ) ^ 2 ^ j := by
  have hK := summable_moebius_sq_mul_card_divisors_pow_div j
  have hw (d : ℕ) : 0 ≤ (μ d : ℝ) ^ 2 * (#d.divisors : ℝ) ^ j / (d * d.totient) := by
    positivity
  calc ∑ q ∈ Ioc 0 N, (#q.divisors : ℝ) ^ j / q.totient
      = ∑ q ∈ Ioc 0 N, (moebiusSqDivTotient * (ζ : ArithmeticFunction ℝ)) q •
          divisorPowDiv j q := sum_congr rfl fun q hq ↦ by
        have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (mem_Ioc.1 hq).1.ne'
        have hid := div_totient_eq_sum_divisors_moebius_sq_div_totient q
        rw [coe_mul_zeta_apply, smul_eq_mul, divisorPowDiv_apply]
        simp only [moebiusSqDivTotient_apply]
        rw [← hid, div_mul_div_comm, mul_comm, mul_div_mul_right _ _ hq0]
    _ = ∑ d ∈ Ioc 0 N, moebiusSqDivTotient d • ∑ l ∈ Ioc 0 (N / d),
          ((ζ : ArithmeticFunction ℝ) l) • divisorPowDiv j (d * l) :=
        sum_Ioc_mul_smul_eq_sum_sum _ _ _ N
    _ ≤ ∑ d ∈ Ioc 0 N, (moebiusSqDivTotient d * divisorPowDiv j d) *
          ∑ l ∈ Ioc 0 N, divisorPowDiv j l := sum_le_sum fun d _ ↦ by
        rw [smul_eq_mul, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (moebiusSqDivTotient_nonneg d)
        rw [mul_sum]
        calc ∑ l ∈ Ioc 0 (N / d), ((ζ : ArithmeticFunction ℝ) l) • divisorPowDiv j (d * l)
            ≤ ∑ l ∈ Ioc 0 (N / d), divisorPowDiv j d * divisorPowDiv j l :=
              sum_le_sum fun l hl ↦ by
                rw [natCoe_apply, zeta_apply_ne (mem_Ioc.1 hl).1.ne', Nat.cast_one, one_smul]
                exact divisorPowDiv_mul_le j d l
          _ ≤ ∑ l ∈ Ioc 0 N, divisorPowDiv j d * divisorPowDiv j l :=
              sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right (Nat.div_le_self N d))
                fun l _ _ ↦ mul_nonneg (divisorPowDiv_nonneg j d) (divisorPowDiv_nonneg j l)
    _ = (∑ d ∈ Ioc 0 N, (μ d : ℝ) ^ 2 * (#d.divisors : ℝ) ^ j / (d * d.totient)) *
          ∑ l ∈ Ioc 0 N, (#l.divisors : ℝ) ^ j / l := by
        rw [sum_mul]
        exact sum_congr rfl fun d _ ↦ by rw [moebiusSqDivTotient_mul_divisorPowDiv]; rfl
    _ ≤ (∑' d : ℕ, (μ d : ℝ) ^ 2 * (#d.divisors : ℝ) ^ j / (d * d.totient)) *
          (harmonic N : ℝ) ^ 2 ^ j :=
        mul_le_mul (hK.sum_le_tsum _ fun d _ ↦ hw d)
          (sum_Ioc_card_divisors_pow_div_le_harmonic_pow j N)
          (sum_nonneg fun l _ ↦ divisorPowDiv_nonneg j l) (tsum_nonneg hw)

/-- **Divisor moments over reciprocal totients, with a real cutoff.** For every `j` there is a
constant `C > 0` such that `∑_{1 ≤ q ≤ Q} τ(q) ^ j / φ(q) ≤ C (1 + log Q) ^ (2 ^ j)` for every real
`Q ≥ 1`. The same bound holds for the sum restricted to the `q` coprime to any `s`, with the same
constant. -/
theorem exists_sum_Ioc_card_divisors_pow_div_totient_le (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 1 ≤ Q → ∀ s : ℕ,
      ∑ q ∈ Ioc 0 ⌊Q⌋₊ with q.Coprime s, (#q.divisors : ℝ) ^ j / q.totient ≤
        C * (1 + Real.log Q) ^ 2 ^ j := by
  have hK := summable_moebius_sq_mul_card_divisors_pow_div j
  have hw (d : ℕ) : 0 ≤ (μ d : ℝ) ^ 2 * (#d.divisors : ℝ) ^ j / (d * d.totient) := by
    positivity
  have hC : (1 : ℝ) ≤ ∑' d : ℕ, (μ d : ℝ) ^ 2 * (#d.divisors : ℝ) ^ j / (d * d.totient) := by
    refine le_trans (le_of_eq ?_) (hK.le_tsum 1 fun d _ ↦ hw d)
    simp
  refine ⟨_, zero_lt_one.trans_le hC, fun Q hQ s ↦ ?_⟩
  have hH : 0 ≤ (harmonic ⌊Q⌋₊ : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact sum_nonneg fun n _ ↦ inv_nonneg.2 (Nat.cast_nonneg n)
  calc ∑ q ∈ Ioc 0 ⌊Q⌋₊ with q.Coprime s, (#q.divisors : ℝ) ^ j / q.totient
      ≤ ∑ q ∈ Ioc 0 ⌊Q⌋₊, (#q.divisors : ℝ) ^ j / q.totient :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun q _ _ ↦ by positivity
    _ ≤ _ * (harmonic ⌊Q⌋₊ : ℝ) ^ 2 ^ j := sum_Ioc_card_divisors_pow_div_totient_le j ⌊Q⌋₊
    _ ≤ _ * (1 + Real.log Q) ^ 2 ^ j :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hH (harmonic_floor_le_one_add_log Q hQ) _) (tsum_nonneg hw)

/-! ### Examples -/

/-- At `Q = 2` and `j = 0` the sum is `1 / φ(1) + 1 / φ(2) = 2`. -/
example : ∑ q ∈ Ioc 0 2, (#q.divisors : ℝ) ^ 0 / q.totient = 2 := by
  rw [show Ioc 0 2 = {1, 2} by decide, sum_pair (by decide)]
  norm_num

/-- At `Q = 2` the sums for `j = 1` and `j = 2` are `3` and `5`. -/
example : ∑ q ∈ Ioc 0 2, (#q.divisors : ℝ) ^ 1 / q.totient = 3 ∧
    ∑ q ∈ Ioc 0 2, (#q.divisors : ℝ) ^ 2 / q.totient = 5 := by
  rw [show Ioc 0 2 = {1, 2} by decide, sum_pair (by decide), sum_pair (by decide),
    show #(Nat.divisors 2) = 2 by decide]
  norm_num

/-- At `Q = 3` and `j = 1` the sum is `1 + 2 + 1 = 4`, and its part over the `q` coprime to `2`
is `1 + 1 = 2`. -/
example : ∑ q ∈ Ioc 0 3, (#q.divisors : ℝ) ^ 1 / q.totient = 4 ∧
    ∑ q ∈ Ioc 0 3 with q.Coprime 2, (#q.divisors : ℝ) ^ 1 / q.totient = 2 := by
  rw [show (Ioc 0 3).filter (·.Coprime 2) = {1, 3} by decide, show Ioc 0 3 = {1, 2, 3} by decide,
    sum_pair (by decide), sum_insert (by decide), sum_pair (by decide),
    show #(Nat.divisors 2) = 2 by decide, show #(Nat.divisors 3) = 2 by decide,
    show Nat.totient 3 = 2 by decide]
  norm_num

end TauCeti
