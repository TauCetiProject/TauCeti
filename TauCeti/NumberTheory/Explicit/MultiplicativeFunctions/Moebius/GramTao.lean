/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Explicit.MultiplicativeFunctions.Moebius.Restricted
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The Gram–Tao bound `|m_S(x)| ≤ 1`

For a set `S` of primes, write `⟨S⟩` for the integers `n ≥ 1` all of whose prime factors lie in `S`
and `m_S(x) = ∑_{n ≤ x, n ∈ ⟨S⟩} μ(n) / n` (`TauCeti.moebiusDivSumIn`). Gram proved `|m(x)| ≤ 1` for
the unrestricted sum, and Tao extended this to every semigroup restriction:
`|m_S(x)| ≤ 1` for every set `S` and every real `x`.

The proof is the Möbius inversion of the indicator of the complementary semigroup `⟨Sᶜ⟩`: for
`n ≥ 1`, `∑_{d ∣ n, d ∈ ⟨S⟩} μ(d)` is `1` if no prime factor of `n` lies in `S` and `0` otherwise.
Summed over `n ≤ N` this counts the `n ≤ N` in `⟨Sᶜ⟩`, a number `U ≥ 1`, as
`U = ∑_{d ≤ N, d ∈ ⟨S⟩} μ(d) ⌊N / d⌋`. Replacing `⌊N / d⌋` by `N / d` changes each term with
`d > 1` by less than `1` and the term `d = 1` not at all, so `|N m_S(N) - U| ≤ T - 1`, where `T` is
the number of `d ≤ N` in `⟨S⟩`. Since `⟨S⟩` and `⟨Sᶜ⟩` meet only in `1`, `U + T ≤ N + 1`; hence
`2 - N ≤ N m_S(N) ≤ N`. This gives `|m_S(x)| ≤ 1`, and the sharper lower bound
`-1 + 2 / N ≤ m_S(N)` at natural `N`.

## Main declarations

* `TauCeti.sum_divisors_filter_moebius`: `∑_{d ∣ n, d ∈ ⟨S⟩} μ(d) = 1_{⟨Sᶜ⟩}(n)` for `n ≠ 0`.
* `TauCeti.card_filter_eq_sum_moebius_mul_natFloor_div`: the number of `n ≤ x` in `⟨Sᶜ⟩` is
  `∑_{d ≤ x, d ∈ ⟨S⟩} μ(d) ⌊x / d⌋`; for `S` the set of all primes this is Meissel's identity.
* `TauCeti.abs_moebiusDivSumIn_le_one`: Tao's bound `|m_S(x)| ≤ 1`.
* `TauCeti.neg_one_add_two_div_le_moebiusDivSumIn`: `-1 + 2 / N ≤ m_S(N)` at natural `N`.
* `TauCeti.abs_moebiusDivSum_le_one`, `TauCeti.neg_one_add_two_div_le_moebiusDivSum`: Gram's bounds
  `|m(x)| ≤ 1` and `-1 + 2 / N ≤ m(N)`.

## References

* T. Tao, *A remark on partial sums involving the Möbius function*, Bull. Aust. Math. Soc. 81
  (2010), 343–349, Theorem 1.1.
* M. Balazard, *Elementary remarks on Möbius' function*, Proc. Steklov Inst. Math. 276 (2012),
  33–39, equation (2).
* The case of all primes is adapted from `sum_mobius_div_self_le` in the Prime Number Theorem And
  project, https://github.com/AlexKontorovich/PrimeNumberTheoremAnd, file
  `PrimeNumberTheoremAnd/Consequences.lean`, revision `41b1a3c`.
-/

public section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TauCeti

open Classical in
/-- `μ` times the indicator of `⟨S⟩`, as the pointwise product of `μ` with the multiplicative
function `d ↦ ∏_{p ∣ d} 1_S(p)`. -/
private theorem pmul_moebius_prodPrimeFactors_apply (S : Set ℕ) (d : ℕ) :
    pmul (μ : ArithmeticFunction ℤ) (prodPrimeFactors fun p ↦ if p ∈ S then 1 else 0) d =
      if ∀ p ∈ d.primeFactors, p ∈ S then μ d else 0 := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  rw [pmul_apply, prodPrimeFactors_apply hd, prod_boole, mul_ite, mul_one, mul_zero]

open Classical in
/-- **Möbius inversion of a semigroup indicator.** For `n ≠ 0`, the sum of `μ(d)` over the
divisors `d` of `n` all of whose prime factors lie in `S` is `1` if no prime factor of `n` lies in
`S`, and `0` otherwise. -/
theorem sum_divisors_filter_moebius (S : Set ℕ) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors with ∀ p ∈ d.primeFactors, p ∈ S, μ d =
      if ∀ p ∈ n.primeFactors, p ∉ S then 1 else 0 := by
  set g : ArithmeticFunction ℤ := prodPrimeFactors fun p ↦ if p ∈ S then 1 else 0
  have h := (IsMultiplicative.prodPrimeFactors _).prodPrimeFactors_one_sub g hn
  rw [sum_filter, ← prod_boole]
  calc ∑ d ∈ n.divisors, (if ∀ p ∈ d.primeFactors, p ∈ S then μ d else 0)
      = ∑ d ∈ n.divisors, (μ : ArithmeticFunction ℤ) d * g d := by
        simp only [← pmul_moebius_prodPrimeFactors_apply, pmul_apply, g]
    _ = ∏ p ∈ n.primeFactors, (1 - g p) := h.symm
    _ = ∏ p ∈ n.primeFactors, if p ∉ S then 1 else 0 :=
        prod_congr rfl fun p hp ↦ by
          have hp := Nat.prime_of_mem_primeFactors hp
          rw [prodPrimeFactors_apply hp.ne_zero, hp.primeFactors]
          by_cases h : p ∈ S <;> simp [h]

open Classical in
/-- **The count of `⟨Sᶜ⟩` up to `x`.** The number of `n ≤ x` none of whose prime factors lies in
`S` is `∑_{d ≤ x, d ∈ ⟨S⟩} μ(d) ⌊x / d⌋`. For `S` the set of all primes the left side is `1` when
`x ≥ 1`, which is Meissel's identity. -/
theorem card_filter_eq_sum_moebius_mul_natFloor_div (S : Set ℕ) (x : ℝ) :
    (#{n ∈ Icc 1 ⌊x⌋₊ | ∀ p ∈ n.primeFactors, p ∉ S} : ℝ) =
      ∑ d ∈ Icc 1 ⌊x⌋₊ with ∀ p ∈ d.primeFactors, p ∈ S, (μ d : ℝ) * ⌊x / d⌋₊ := by
  have h := sum_Ioc_mul_zeta_eq_sum
    (pmul (μ : ArithmeticFunction ℤ) (prodPrimeFactors fun p ↦ if p ∈ S then 1 else 0)) ⌊x⌋₊
  rw [← Icc_add_one_left_eq_Ioc, zero_add] at h
  have hL : ∀ n ∈ Icc 1 ⌊x⌋₊, (pmul (μ : ArithmeticFunction ℤ)
      (prodPrimeFactors fun p ↦ if p ∈ S then 1 else 0) * ζ) n =
        if ∀ p ∈ n.primeFactors, p ∉ S then 1 else 0 := fun n hn ↦ by
    rw [coe_mul_zeta_apply, ← sum_divisors_filter_moebius S (by grind), sum_filter]
    simp only [pmul_moebius_prodPrimeFactors_apply]
  rw [sum_congr rfl hL] at h
  simp only [pmul_moebius_prodPrimeFactors_apply] at h
  rw [card_filter, sum_filter]
  simp only [Nat.floor_div_natCast]
  have := congrArg (Int.cast : ℤ → ℝ) h
  push_cast [ite_mul, zero_mul] at this ⊢
  exact this

/-! ### Tao's bound -/

/-- `1` has no prime factors, so it lies in every semigroup restriction of `[1, N]`, `N ≥ 1`. -/
private theorem one_mem_filter_primeFactors (P : ℕ → Prop) {N : ℕ} (hN : 1 ≤ N)
    [DecidablePred fun n : ℕ ↦ ∀ p ∈ n.primeFactors, P p] :
    1 ∈ (Icc 1 N).filter fun n ↦ ∀ p ∈ n.primeFactors, P p :=
  mem_filter.2 ⟨mem_Icc.2 ⟨le_rfl, hN⟩, fun p hp ↦ absurd hp (by simp)⟩

open Classical in
/-- Replacing `⌊N / d⌋` by `N / d` in `∑_{d ≤ N, d ∈ ⟨S⟩} μ(d) ⌊N / d⌋` changes each term with
`d > 1` by less than `1` and the term `d = 1` not at all. -/
private theorem abs_natCast_mul_moebiusDivSumIn_sub_card_le (S : Set ℕ) {N : ℕ} (hN : 1 ≤ N) :
    |N * moebiusDivSumIn S N - #{n ∈ Icc 1 N | ∀ p ∈ n.primeFactors, p ∉ S}| ≤
      #{n ∈ Icc 1 N | ∀ p ∈ n.primeFactors, p ∈ S} - 1 := by
  have h1 := one_mem_filter_primeFactors (· ∈ S) hN
  have hd : ∀ d : ℕ, |(N : ℝ) * ((μ d : ℝ) / d) - μ d * ⌊(N : ℝ) / d⌋₊| ≤ 1 := fun d ↦ by
    have h0 : 0 ≤ (N : ℝ) / d - ⌊(N : ℝ) / d⌋₊ := sub_nonneg.2 (Nat.floor_le (by positivity))
    have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
    rw [show (N : ℝ) * ((μ d : ℝ) / d) - μ d * ⌊(N : ℝ) / d⌋₊ =
        μ d * ((N : ℝ) / d - ⌊(N : ℝ) / d⌋₊) by ring, abs_mul, abs_of_nonneg h0]
    nlinarith [Nat.lt_floor_add_one ((N : ℝ) / d), abs_nonneg (μ d : ℝ)]
  have hcount := card_filter_eq_sum_moebius_mul_natFloor_div S N
  rw [Nat.floor_natCast] at hcount
  rw [hcount, moebiusDivSumIn_def, Nat.floor_natCast, mul_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [← add_sum_erase _ _ h1]
  -- the term `d = 1` vanishes, since `⌊N / 1⌋ = N`
  have h1term : |(N : ℝ) * ((μ 1 : ℝ) / (1 : ℕ)) - μ 1 * ⌊(N : ℝ) / (1 : ℕ)⌋₊| = 0 := by simp
  -- every other term is at most `1`
  set T := {n ∈ Icc 1 N | ∀ p ∈ n.primeFactors, p ∈ S}
  have hrest : ∑ d ∈ T.erase 1, |(N : ℝ) * ((μ d : ℝ) / d) - μ d * ⌊(N : ℝ) / d⌋₊| ≤
      #(T.erase 1) :=
    (sum_le_sum fun d _ ↦ hd d).trans_eq (by rw [sum_const, nsmul_one])
  have hcard : (#(T.erase 1) : ℝ) + 1 = #T := by exact_mod_cast card_erase_add_one h1
  linarith

open Classical in
/-- `⟨S⟩` and `⟨Sᶜ⟩` meet only in `1`, so at most `N + 1` integers in `[1, N]` are counted by the
two restrictions together. -/
private theorem card_filter_mem_add_card_filter_notMem_le (S : Set ℕ) (N : ℕ) :
    #{n ∈ Icc 1 N | ∀ p ∈ n.primeFactors, p ∈ S} +
      #{n ∈ Icc 1 N | ∀ p ∈ n.primeFactors, p ∉ S} ≤ N + 1 := by
  rw [← card_union_add_card_inter]
  refine add_le_add ?_ (card_le_one.2 fun a ha b hb ↦ ?_)
  · simpa using card_le_card (union_subset (filter_subset _ (Icc 1 N)) (filter_subset _ _))
  · have h : ∀ n ∈ ((Icc 1 N).filter fun n ↦ ∀ p ∈ n.primeFactors, p ∈ S) ∩
        ((Icc 1 N).filter fun n ↦ ∀ p ∈ n.primeFactors, p ∉ S), n = 1 := fun n hn ↦ by
      simp only [mem_inter, mem_filter, mem_Icc] at hn
      have := Nat.primeFactors_eq_empty.1 (eq_empty_of_forall_notMem fun p hp ↦
        hn.2.2 p hp (hn.1.2 p hp))
      omega
    rw [h a ha, h b hb]

open Classical in
/-- Gram's argument for `⟨S⟩`: `2 - N ≤ N m_S(N) ≤ N` for every natural `N ≥ 1`. -/
private theorem natCast_mul_moebiusDivSumIn_mem_Icc (S : Set ℕ) {N : ℕ} (hN : 1 ≤ N) :
    2 - N ≤ N * moebiusDivSumIn S N ∧ N * moebiusDivSumIn S N ≤ N := by
  have hE := abs_le.1 (abs_natCast_mul_moebiusDivSumIn_sub_card_le S hN)
  have hTU : (#{n ∈ Icc 1 N | ∀ p ∈ n.primeFactors, p ∈ S} : ℝ) +
      #{n ∈ Icc 1 N | ∀ p ∈ n.primeFactors, p ∉ S} ≤ N + 1 := by
    exact_mod_cast card_filter_mem_add_card_filter_notMem_le S N
  have hU : (1 : ℝ) ≤ #{n ∈ Icc 1 N | ∀ p ∈ n.primeFactors, p ∉ S} := by
    exact_mod_cast card_pos.2 ⟨1, one_mem_filter_primeFactors (· ∉ S) hN⟩
  constructor <;> linarith [hE.1, hE.2]

/-- `m_S(x) ≤ 1` for every set `S` and every real `x`. -/
theorem moebiusDivSumIn_le_one (S : Set ℕ) (x : ℝ) : moebiusDivSumIn S x ≤ 1 := by
  rw [← moebiusDivSumIn_natFloor]
  rcases Nat.eq_zero_or_pos ⌊x⌋₊ with h | h
  · simp [h, moebiusDivSumIn_of_lt_one]
  · have hN : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast h
    exact le_of_mul_le_mul_left (by simpa using (natCast_mul_moebiusDivSumIn_mem_Icc S h).2) hN

/-- **Gram's lower bound** for `⟨S⟩`: `-1 + 2 / N ≤ m_S(N)` for every natural `N`. At `N = 0` both
sides are junk values, `-1 ≤ 0`. -/
theorem neg_one_add_two_div_le_moebiusDivSumIn (S : Set ℕ) (N : ℕ) :
    -1 + 2 / N ≤ moebiusDivSumIn S N := by
  rcases Nat.eq_zero_or_pos N with rfl | h
  · simp [moebiusDivSumIn_of_lt_one]
  · have hN : (0 : ℝ) < N := by exact_mod_cast h
    rw [neg_add_eq_sub, ← div_self hN.ne', ← sub_div, div_le_iff₀ hN, mul_comm]
    exact (natCast_mul_moebiusDivSumIn_mem_Icc S h).1

/-- **Tao's theorem**: `|m_S(x)| ≤ 1` for every set `S` and every real `x`, where
`m_S(x) = ∑ μ(n) / n` over the `n ≤ x` all of whose prime factors lie in `S`. -/
theorem abs_moebiusDivSumIn_le_one (S : Set ℕ) (x : ℝ) : |moebiusDivSumIn S x| ≤ 1 := by
  refine abs_le.2 ⟨?_, moebiusDivSumIn_le_one S x⟩
  rw [← moebiusDivSumIn_natFloor]
  exact le_trans (le_add_of_nonneg_right (by positivity))
    (neg_one_add_two_div_le_moebiusDivSumIn S ⌊x⌋₊)

/-- **Gram's bound** `|m(x)| ≤ 1` for every real `x`. -/
theorem abs_moebiusDivSum_le_one (x : ℝ) : |moebiusDivSum x| ≤ 1 := by
  simpa [moebiusDivSumIn_of_setOf_prime_subset le_rfl] using
    abs_moebiusDivSumIn_le_one {p | p.Prime} x

/-- **Gram's lower bound** `-1 + 2 / N ≤ m(N)` for every natural `N`. -/
theorem neg_one_add_two_div_le_moebiusDivSum (N : ℕ) : -1 + 2 / N ≤ moebiusDivSum N := by
  simpa [moebiusDivSumIn_of_setOf_prime_subset le_rfl] using
    neg_one_add_two_div_le_moebiusDivSumIn {p | p.Prime} N

end TauCeti
