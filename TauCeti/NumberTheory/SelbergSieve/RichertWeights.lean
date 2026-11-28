/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.BigOperators.Field
import TauCeti.NumberTheory.PrimeFactors.Bounds

/-!
# Richert's logarithmic sieve weights

Fix `N > 1`, exponents `0 < α < β` and an integer `r` with `(r + 1) β > 1`. Richert's weight of a
prime `p` with `N ^ α ≤ p < N ^ β` is `w_p = β / ((r + 1) β - 1) * (1 - log p / (β log N))`, and
`w_p = 0` otherwise. For a finite family `A ⊆ [1, N]` with nonnegative weights `a`, the weighted
sum

`W = ∑_{n ∈ A, every prime factor of n is ≥ N ^ α} a n * (1 - ∑_{p ∣ n} w_p)`

is a combination `S - ∑_p w_p S_p` of sifted sums, to which upper and lower sieve bounds apply.
The weights are chosen so that `∑_{p ∣ n} w_p ≥ 1` as soon as `n ≤ N` has at least `r + 1` prime
factors: with distinct prime factors always, and with prime factors counted with multiplicity
unless the square of a prime in `[N ^ α, N ^ β)` divides `n`. Hence a positive lower bound for `W`
produces members of `A` with at most `r` prime factors, up to that square exception.

The inner sum runs over the distinct prime factors of `n`; no hypothesis `α < β` is needed for
the statements below.

## Main definitions

* `TauCeti.SieveWeighted.richertWeight N α β r p`: the weight `w_p`.
* `TauCeti.SieveWeighted.richertSum A a N α β r`: the weighted sum `W`.

## Main results

* `TauCeti.SieveWeighted.richertWeight_nonneg`: the weights are nonnegative.
* `TauCeti.SieveWeighted.richertSum_eq_sum_sub_sum_mul`: `W = S - ∑_p w_p S_p`.
* `TauCeti.SieveWeighted.one_le_sum_primeFactors_richertWeight`: `∑_{p ∣ n} w_p ≥ 1` when `n` has
  at least `r + 1` distinct prime factors.
* `TauCeti.SieveWeighted.one_le_sum_primeFactors_richertWeight_of_forall_sq_dvd`: the same when
  `Ω(n) ≥ r + 1` and no prime below `N ^ β` has its square dividing `n`.
* `TauCeti.SieveWeighted.richertSum_le_sum_add_sum`: `W` is at most the weight of the `n` with
  `Ω(n) ≤ r` plus the weight of the `n` divisible by the square of a prime in `[N ^ α, N ^ β)`.

## References

* D. R. Heath-Brown, *Lectures on sieves*, arXiv:math/0209360, §6, (6.1)–(6.4).
-/

public section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Omega

namespace TauCeti.SieveWeighted

variable {N α β : ℝ} {r : ℕ} {n p : ℕ}

/-- **Richert's logarithmic weight** of a natural number `p`: for a prime `p` with
`N ^ α ≤ p < N ^ β` it is `β / ((r + 1) β - 1) * (1 - log p / (β log N))`, and it is `0` for every
other `p`. The upper endpoint is strict. -/
noncomputable def richertWeight (N α β : ℝ) (r : ℕ) (p : ℕ) : ℝ :=
  if p.Prime ∧ N ^ α ≤ (p : ℝ) ∧ (p : ℝ) < N ^ β then
    β / ((r + 1) * β - 1) * (1 - Real.log p / (β * Real.log N))
  else 0

/-- The value of Richert's weight at a prime in the weighted range. -/
theorem richertWeight_of_prime (hp : p.Prime) (hpα : N ^ α ≤ (p : ℝ)) (hpβ : (p : ℝ) < N ^ β) :
    richertWeight N α β r p = β / ((r + 1) * β - 1) * (1 - Real.log p / (β * Real.log N)) :=
  ite_eq_left ⟨hp, hpα, hpβ⟩

/-- Richert's weight vanishes at a number that is not prime. -/
theorem richertWeight_eq_zero_of_not_prime (hp : ¬p.Prime) : richertWeight N α β r p = 0 :=
  ite_eq_right fun h ↦ hp h.1

/-- Richert's weight vanishes below the range: at `p < N ^ α`. -/
theorem richertWeight_eq_zero_of_lt (hpα : (p : ℝ) < N ^ α) : richertWeight N α β r p = 0 :=
  ite_eq_right fun h ↦ hpα.not_ge h.2.1

/-- Richert's weight vanishes above the range, including at the endpoint `p = N ^ β`. -/
theorem richertWeight_eq_zero_of_le (hpβ : N ^ β ≤ (p : ℝ)) : richertWeight N α β r p = 0 :=
  ite_eq_right fun h ↦ hpβ.not_gt h.2.2

/-- Richert's weights are nonnegative when `N > 1`, `β > 0` and `(r + 1) β > 1`. -/
theorem richertWeight_nonneg (hN : 1 < N) (hβ : 0 < β) (hr : 1 < (r + 1) * β) (p : ℕ) :
    0 ≤ richertWeight N α β r p := by
  rw [richertWeight]
  split_ifs with h
  · obtain ⟨hp, -, hpβ⟩ := h
    have hlog : 0 < Real.log N := Real.log_pos hN
    have hp0 : (0 : ℝ) < p := Nat.cast_pos.2 hp.pos
    have hlt : Real.log p < β * Real.log N :=
      (Real.lt_rpow_iff_log_lt hp0 (zero_lt_one.trans hN)).1 hpβ
    refine mul_nonneg (div_nonneg hβ.le (by linarith)) (sub_nonneg.2 ?_)
    exact (div_le_one (mul_pos hβ hlog)).2 hlt.le
  · exact le_rfl

/-- At a prime `p ≥ N ^ α`, Richert's weight is at least the unrestricted expression
`β / ((r + 1) β - 1) * (1 - log p / (β log N))`: beyond `N ^ β` that expression is nonpositive. -/
theorem mul_one_sub_log_div_le_richertWeight (hN : 1 < N) (hβ : 0 < β) (hr : 1 < (r + 1) * β)
    (hp : p.Prime) (hpα : N ^ α ≤ (p : ℝ)) :
    β / ((r + 1) * β - 1) * (1 - Real.log p / (β * Real.log N)) ≤ richertWeight N α β r p := by
  rcases lt_or_ge (p : ℝ) (N ^ β) with hpβ | hpβ
  · rw [richertWeight_of_prime hp hpα hpβ]
  · rw [richertWeight_eq_zero_of_le hpβ]
    have hlog : 0 < Real.log N := Real.log_pos hN
    have hN0 : 0 < N := zero_lt_one.trans hN
    have hle : β * Real.log N ≤ Real.log p := by
      rw [← Real.log_rpow hN0]
      exact Real.log_le_log (Real.rpow_pos_of_pos hN0 β) hpβ
    refine mul_nonpos_of_nonneg_of_nonpos (div_nonneg hβ.le (by linarith)) (sub_nonpos.2 ?_)
    exact (one_le_div (mul_pos hβ hlog)).2 hle

/-- The normalization of Richert's weights: if `K ≥ r + 1` and `log n ≤ log N`, then
`β / ((r + 1) β - 1) * (K - log n / (β log N)) ≥ 1`. -/
private theorem one_le_mul_sub_log_div (hN : 1 < N) (hβ : 0 < β) (hr : 1 < (r + 1) * β)
    {K : ℝ} (hK : (r : ℝ) + 1 ≤ K) {x : ℝ} (hx : x ≤ Real.log N) :
    1 ≤ β / ((r + 1) * β - 1) * (K - x / (β * Real.log N)) := by
  have hlog : 0 < Real.log N := Real.log_pos hN
  have hden : 0 < (r + 1) * β - 1 := by linarith
  have hx' : x / (β * Real.log N) ≤ 1 / β := by
    rw [div_le_div_iff₀ (mul_pos hβ hlog) hβ, one_mul]
    nlinarith
  have hd : β * ((r : ℝ) + 1) - 1 ≠ 0 := by
    rw [mul_comm]
    exact hden.ne'
  calc (1 : ℝ) = β / ((r + 1) * β - 1) * ((r + 1) - 1 / β) := by
        field_simp
    _ ≤ β / ((r + 1) * β - 1) * (K - x / (β * Real.log N)) :=
        mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hβ.le hden.le)

/-- **Richert's weights exceed one on numbers with many distinct prime factors.** If
`1 ≤ n ≤ N`, every prime factor of `n` is at least `N ^ α`, and `n` has at least `r + 1` distinct
prime factors, then `∑_{p ∣ n} w_p ≥ 1`. -/
theorem one_le_sum_primeFactors_richertWeight (hN : 1 < N) (hβ : 0 < β)
    (hr : 1 < (r + 1) * β) (hn0 : n ≠ 0) (hnN : (n : ℝ) ≤ N)
    (hrough : ∀ p ∈ n.primeFactors, N ^ α ≤ (p : ℝ)) (hω : r + 1 ≤ #n.primeFactors) :
    1 ≤ ∑ p ∈ n.primeFactors, richertWeight N α β r p := by
  have hlogn : ∑ p ∈ n.primeFactors, Real.log p ≤ Real.log N :=
    (Nat.sum_primeFactors_log_le n).trans
      (Real.log_le_log (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)) hnN)
  have hK : (r : ℝ) + 1 ≤ (#n.primeFactors : ℝ) := by exact_mod_cast hω
  calc (1 : ℝ) ≤ β / ((r + 1) * β - 1) *
        ((#n.primeFactors : ℝ) - (∑ p ∈ n.primeFactors, Real.log p) / (β * Real.log N)) :=
        one_le_mul_sub_log_div hN hβ hr hK hlogn
    _ = ∑ p ∈ n.primeFactors,
          β / ((r + 1) * β - 1) * (1 - Real.log p / (β * Real.log N)) := by
        rw [← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, sum_div]
    _ ≤ ∑ p ∈ n.primeFactors, richertWeight N α β r p :=
        sum_le_sum fun p hp ↦ mul_one_sub_log_div_le_richertWeight hN hβ hr
          (Nat.prime_of_mem_primeFactors hp) (hrough p hp)

/-- **The square exception.** If `1 ≤ n ≤ N`, every prime factor of `n` is at least `N ^ α`, `n`
has at least `r + 1` prime factors counted with multiplicity, and every prime whose square divides
`n` is at least `N ^ β`, then `∑_{p ∣ n} w_p ≥ 1`. Hence a number with `Ω(n) > r` can have a
positive Richert summand only if the square of some prime in `[N ^ α, N ^ β)` divides it. -/
theorem one_le_sum_primeFactors_richertWeight_of_forall_sq_dvd (hN : 1 < N) (hβ : 0 < β)
    (hr : 1 < (r + 1) * β) (hn0 : n ≠ 0) (hnN : (n : ℝ) ≤ N)
    (hrough : ∀ p ∈ n.primeFactors, N ^ α ≤ (p : ℝ)) (hΩ : r + 1 ≤ Ω n)
    (hsq : ∀ p ∈ n.primeFactors, p ^ 2 ∣ n → N ^ β ≤ (p : ℝ)) :
    1 ≤ ∑ p ∈ n.primeFactors, richertWeight N α β r p := by
  have hlog : 0 < Real.log N := Real.log_pos hN
  have hN0 : 0 < N := zero_lt_one.trans hN
  have hc : 0 ≤ β / ((r + 1) * β - 1) := div_nonneg hβ.le (by linarith)
  have hlogn : Real.log n ≤ Real.log N :=
    Real.log_le_log (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)) hnN
  have hK : (r : ℝ) + 1 ≤ (Ω n : ℝ) := by exact_mod_cast hΩ
  have hΩsum : (Ω n : ℝ) = ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) := by
    rw [cardFactors_eq_sum_factorization, Finsupp.sum, Nat.support_factorization, Nat.cast_sum]
  have hlogsum : Real.log n = ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log p := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
  have hterm (p : ℕ) (hp : p ∈ n.primeFactors) :
      β / ((r + 1) * β - 1) * ((n.factorization p : ℝ) -
        (n.factorization p : ℝ) * Real.log p / (β * Real.log N)) ≤ richertWeight N α β r p := by
    have hpp := Nat.prime_of_mem_primeFactors hp
    have he : 1 ≤ n.factorization p :=
      hpp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hp)
    rcases he.eq_or_lt with he1 | he2
    · rw [← he1, Nat.cast_one, one_mul]
      exact mul_one_sub_log_div_le_richertWeight hN hβ hr hpp (hrough p hp)
    · have hpβ : N ^ β ≤ (p : ℝ) := hsq p hp ((hpp.pow_dvd_iff_le_factorization hn0).2 he2)
      have hle : β * Real.log N ≤ Real.log p := by
        rw [← Real.log_rpow hN0]
        exact Real.log_le_log (Real.rpow_pos_of_pos hN0 β) hpβ
      have hfac : (n.factorization p : ℝ) - (n.factorization p : ℝ) * Real.log p /
          (β * Real.log N) = (n.factorization p : ℝ) * (1 - Real.log p / (β * Real.log N)) := by
        ring
      rw [hfac]
      exact (mul_nonpos_of_nonneg_of_nonpos hc (mul_nonpos_of_nonneg_of_nonpos
        (Nat.cast_nonneg _) (sub_nonpos.2 ((one_le_div (mul_pos hβ hlog)).2 hle)))).trans
        (richertWeight_nonneg hN hβ hr p)
  calc (1 : ℝ) ≤ β / ((r + 1) * β - 1) * ((Ω n : ℝ) - Real.log n / (β * Real.log N)) :=
        one_le_mul_sub_log_div hN hβ hr hK hlogn
    _ = ∑ p ∈ n.primeFactors, β / ((r + 1) * β - 1) * ((n.factorization p : ℝ) -
          (n.factorization p : ℝ) * Real.log p / (β * Real.log N)) := by
        rw [← mul_sum, sum_sub_distrib, ← sum_div, ← hΩsum, ← hlogsum]
    _ ≤ ∑ p ∈ n.primeFactors, richertWeight N α β r p := sum_le_sum hterm

/-- **Richert's weighted sum** of a finite family `A` with weights `a`: the sum of
`a n * (1 - ∑_{p ∣ n} w_p)` over the `n ∈ A` all of whose prime factors are at least `N ^ α`. The
inner sum is over the distinct prime factors of `n`. -/
noncomputable def richertSum (A : Finset ℕ) (a : ℕ → ℝ) (N α β : ℝ) (r : ℕ) : ℝ :=
  ∑ n ∈ A.filter fun n : ℕ ↦ ∀ p ∈ n.primeFactors, N ^ α ≤ ((p : ℕ) : ℝ),
    a n * (1 - ∑ p ∈ n.primeFactors, richertWeight N α β r p)

/-- The defining formula for Richert's weighted sum. -/
theorem richertSum_def (A : Finset ℕ) (a : ℕ → ℝ) (N α β : ℝ) (r : ℕ) :
    richertSum A a N α β r =
      ∑ n ∈ A.filter fun n : ℕ ↦ ∀ p ∈ n.primeFactors, N ^ α ≤ ((p : ℕ) : ℝ),
        a n * (1 - ∑ p ∈ n.primeFactors, richertWeight N α β r p) := by
  rfl

/-- Richert's weighted sum of the empty family is `0`. -/
@[simp]
theorem richertSum_empty (a : ℕ → ℝ) (N α β : ℝ) (r : ℕ) : richertSum ∅ a N α β r = 0 := by
  rw [richertSum_def, filter_empty, sum_empty]

/-- **Richert's sum as a combination of sifted sums.** If `A` consists of positive integers whose
prime factors all lie in the finite set `P`, then `W = S - ∑_{p ∈ P} w_p S_p`, where `S` is the
sum of `a n` over the `n ∈ A` with every prime factor at least `N ^ α`, and `S_p` is the part of
that sum with `p ∣ n`. -/
theorem richertSum_eq_sum_sub_sum_mul {A : Finset ℕ} (a : ℕ → ℝ) (N α β : ℝ) (r : ℕ)
    (hA : ∀ n ∈ A, n ≠ 0) {P : Finset ℕ} (hP : ∀ n ∈ A, n.primeFactors ⊆ P) :
    richertSum A a N α β r =
      ∑ n ∈ A.filter fun n : ℕ ↦ ∀ p ∈ n.primeFactors, N ^ α ≤ ((p : ℕ) : ℝ), a n -
        ∑ p ∈ P, richertWeight N α β r p *
          ∑ n ∈ (A.filter fun n : ℕ ↦ ∀ q ∈ n.primeFactors, N ^ α ≤ ((q : ℕ) : ℝ)).filter
            (p ∣ ·), a n := by
  have hterm (n : ℕ) (hn : n ∈ A.filter fun n : ℕ ↦ ∀ q ∈ n.primeFactors,
      N ^ α ≤ ((q : ℕ) : ℝ)) :
      a n * (1 - ∑ p ∈ n.primeFactors, richertWeight N α β r p) =
        a n - ∑ p ∈ P, if p ∣ n then richertWeight N α β r p * a n else 0 := by
    have hnA := (mem_filter.1 hn).1
    have hinner : ∑ p ∈ n.primeFactors, richertWeight N α β r p =
        ∑ p ∈ P.filter (· ∣ n), richertWeight N α β r p :=
      sum_subset (fun p hp ↦ mem_filter.2 ⟨hP n hnA hp, Nat.dvd_of_mem_primeFactors hp⟩)
        fun p hp hpn ↦ richertWeight_eq_zero_of_not_prime fun hpp ↦
          hpn (Nat.mem_primeFactors.2 ⟨hpp, (mem_filter.1 hp).2, hA n hnA⟩)
    rw [mul_sub, mul_one, hinner, mul_sum, sum_filter]
    exact congrArg (a n - ·) (sum_congr rfl fun p _ ↦ by split_ifs <;> ring)
  rw [richertSum_def, sum_congr rfl hterm, sum_sub_distrib, sum_comm]
  refine congrArg _ (sum_congr rfl fun p _ ↦ ?_)
  rw [mul_sum]
  exact (sum_filter _ _).symm

open Classical in
/-- **Richert's weighted sum detects almost-primes.** Let `N > 1`, `β > 0` and `(r + 1) β > 1`,
and let `A` be a finite set of integers in `[1, N]` with nonnegative weights `a`. Then Richert's
weighted sum is at most the weight of the `n ∈ A` with `Ω(n) ≤ r` plus the weight of the `n ∈ A`
divisible by the square of a prime in `[N ^ α, N ^ β)`. -/
theorem richertSum_le_sum_add_sum (hN : 1 < N) (hβ : 0 < β) (hr : 1 < (r + 1) * β)
    {A : Finset ℕ} {a : ℕ → ℝ} (ha : ∀ n ∈ A, 0 ≤ a n) (hA : ∀ n ∈ A, n ≠ 0 ∧ (n : ℝ) ≤ N) :
    richertSum A a N α β r ≤ ∑ n ∈ A.filter (fun n : ℕ ↦ Ω n ≤ r), a n +
      ∑ n ∈ A.filter (fun n : ℕ ↦ ∃ p : ℕ, p.Prime ∧ N ^ α ≤ (p : ℝ) ∧ (p : ℝ) < N ^ β ∧
        p ^ 2 ∣ n), a n := by
  rw [richertSum_def, sum_filter, sum_filter, sum_filter, ← sum_add_distrib]
  refine sum_le_sum fun n hn ↦ ?_
  have han := ha n hn
  obtain ⟨hn0, hnN⟩ := hA n hn
  have hw : 0 ≤ ∑ p ∈ n.primeFactors, richertWeight N α β r p :=
    sum_nonneg fun p _ ↦ richertWeight_nonneg hN hβ hr p
  have hle : a n * (1 - ∑ p ∈ n.primeFactors, richertWeight N α β r p) ≤ a n :=
    mul_le_of_le_one_right han (by linarith)
  have h1 : 0 ≤ (if Ω n ≤ r then a n else 0) := by split_ifs <;> first | exact han | exact le_rfl
  have h2 : 0 ≤ (if ∃ p : ℕ, p.Prime ∧ N ^ α ≤ (p : ℝ) ∧ (p : ℝ) < N ^ β ∧ p ^ 2 ∣ n
      then a n else 0) := by split_ifs <;> first | exact han | exact le_rfl
  by_cases hrough : ∀ p ∈ n.primeFactors, N ^ α ≤ ((p : ℕ) : ℝ)
  swap
  · rw [ite_eq_right hrough]
    exact add_nonneg h1 h2
  rw [ite_eq_left hrough]
  by_cases hΩ : Ω n ≤ r
  · rw [ite_eq_left hΩ]
    exact hle.trans (le_add_of_nonneg_right h2)
  by_cases hsq : ∃ p : ℕ, p.Prime ∧ N ^ α ≤ (p : ℝ) ∧ (p : ℝ) < N ^ β ∧ p ^ 2 ∣ n
  · rw [ite_eq_left hsq]
    exact hle.trans (le_add_of_nonneg_left h1)
  · rw [ite_eq_right hΩ, ite_eq_right hsq, add_zero]
    refine mul_nonpos_of_nonneg_of_nonpos han (sub_nonpos.2 ?_)
    refine one_le_sum_primeFactors_richertWeight_of_forall_sq_dvd hN hβ hr hn0 hnN hrough
      (by omega) fun p hp hp2 ↦ ?_
    by_contra hlt
    exact hsq ⟨p, Nat.prime_of_mem_primeFactors hp, hrough p hp, not_le.1 hlt, hp2⟩

/-! ### Examples -/

/-- At the upper endpoint `p = N ^ β` the weight is `0`: the range is half-open. -/
example (hp : (p : ℝ) = N ^ β) : richertWeight N α β r p = 0 :=
  richertWeight_eq_zero_of_le hp.ge

/-- For `N = 8`, `α = 1 / 4`, `β = 1`: the number `8` has one distinct prime factor but
`Ω(8) = 3`, and it is divisible by the square of the prime `2`, which lies in `[8 ^ (1 / 4), 8)`.
It is counted by the square exception. -/
example : ∃ q : ℕ, q.Prime ∧ (8 : ℝ) ^ (1 / 4 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (8 : ℝ) ^ (1 : ℝ) ∧
    q ^ 2 ∣ 8 := by
  refine ⟨2, Nat.prime_two, ?_, by norm_num, by norm_num⟩
  have h16 : ((16 : ℝ)) ^ (1 / 4 : ℝ) = 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [Nat.cast_ofNat, ← h16]
  exact Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)

end TauCeti.SieveWeighted
