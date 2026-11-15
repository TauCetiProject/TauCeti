/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import TauCeti.NumberTheory.ArithmeticFunction.Additive
import TauCeti.Algebra.BigOperators.Finset.SquaredDeviation
import TauCeti.Algebra.BigOperators.Ring.Finset
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.Analysis.SpecificLimits.ReciprocalSeries
import TauCeti.Data.Nat.Cast.Order.Field
import TauCeti.NumberTheory.Chebyshev.Mertens
import TauCeti.NumberTheory.SumPrimePow

/-!
# The Turán–Kubilius inequality

For any real-valued additive arithmetic function `f : ArithmeticFunction ℝ` and any natural number
`N`, set

* `A = ∑_{p ≤ N} ∑_{1 ≤ k ≤ log_p N} f(p ^ k) / p ^ k`,
* `B = ∑_{p ≤ N} ∑_{1 ≤ k ≤ log_p N} f(p ^ k) ^ 2 / p ^ k`.

The **Turán–Kubilius inequality** bounds the empirical second central moment of `f` on `{1, …, N}`
by a universal constant multiple of `N * B`:

`∑ n ∈ Icc 1 N, (f n - A) ^ 2 ≤ 30 * N * B`.

To avoid invoking Mertens' second theorem while keeping an explicit small constant, the proof splits
the prime-power pairs `(p, k)` at `M = Nat.sqrt N`:

* **Small prime powers** (`p ^ k ≤ M`): exact prime-valuation indicators `1_{n.factorization p = k}`
  are centered at their asymptotic density `α(p, k) = 1 / p ^ k - 1 / p ^ (k + 1)`. Inclusion–
  exclusion over multiples of `p ^ k` and `p ^ (k + 1)` controls single-prime counts to within `1`
  and coprime pair counts (`p ≠ q`) to within `2`, giving pairwise correlation at most `3`. By
  Cauchy–Schwarz and `∑_{q ≤ M} q ≤ M ^ 2 ≤ N`, the centered small part has second moment at most
  `4 * N * B_S`, and shifting from `α(p, k)` to `1 / p ^ k` costs at most a convergent higher-power
  geometric tail, yielding `≤ 10 * N * B_S`.
* **Large prime powers** (`M < p ^ k ≤ N`): since `(M + 1) ^ 2 > N`, at most one large prime power
  can occur in the canonical factorization of any `n ∈ Icc 1 N`. Hence
  `∑_{n ≤ N} f_L(n) ^ 2 ≤ N * B_L`, and `Finset.sum_sub_sq_le_sum_sq_add_div` plus Cauchy–Schwarz
  reduce `∑_{n ≤ N} (f_L(n) - A_L) ^ 2` to bounding `∑_{(p, k) ∈ L} 1 / p ^ k`: exponents `k ≥ 2`
  contribute at most `1` by `Nat.sum_primesLE_sum_Icc_two_inv_pow_le_one`, while primes
  `M + 1 ≤ p ≤ N` contribute at most `11` by `Chebyshev.sum_primesLE_filter_ge_inv_le`.

Combining the two parts via `(u + v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2` gives constant `26 ≤ 30` for all
`N : ℕ` (including `N = 0, 1`, with no `2 ≤ N` side-condition). For strongly additive functions
(`f (p ^ k) = f p` for `k ≥ 1`), stripping the convergent `k ≥ 2` geometric tails yields the
distinct-prime form over `Nat.primesLE N`, which specializes at `ω = cardDistinctFactors` to
Turán's original 1934 variance bound.

## Main results

* `ArithmeticFunction.IsAdditive.apply_eq_sum_primesLE_Icc_log`: prime-power indicator expansion of
  an additive function on `Icc 1 N`.
* `ArithmeticFunction.IsAdditive.sum_Icc_log_sub_sq_le`,
  `ArithmeticFunction.IsAdditive.sum_Icc_sub_sq_le`: **the Turán–Kubilius inequality** with
  constant `30`, in both `Icc 1 (p.log N)` and `if p ^ k ≤ N` cutoff forms, for all `N : ℕ`.
* `ArithmeticFunction.IsStronglyAdditive.sum_primesLE_Icc_log_sq_le`,
  `ArithmeticFunction.IsStronglyAdditive.sum_primesLE_Icc_log_sub_eq`,
  `ArithmeticFunction.IsStronglyAdditive.sub_sum_primesLE_sq_le`: comparison between full
  prime-power sums and distinct-prime sums for strongly additive functions.
* `ArithmeticFunction.IsStronglyAdditive.sum_Icc_sub_sq_le`: distinct-prime Turán–Kubilius bound
  for strongly additive functions.
* `ArithmeticFunction.sum_Icc_cardDistinctFactors_sub_sq_le`: Turán's inequality (1934) for `ω(n)`.

## References

* C. Elsholtz and T. Tao, *Counting the number of solutions to the Erdős–Straus equation on unit
  fractions*, Appendix A, Lemmas A.2–A.3.
* J. Kubilius, *Probabilistic Methods in the Theory of Numbers*, Chapter III.
* P. Turán, *On a theorem of Hardy and Ramanujan*, J. London Math. Soc. **9** (1934), 274–276.
-/

public section

open Finset

namespace ArithmeticFunction

/-! ### Exact-valuation counts and correlations -/

section ValuationCounts

/-- Asymptotic density `1 / p ^ k - 1 / p ^ (k + 1)` of `{n : v_p(n) = k}`. -/
private noncomputable def valDensity (p k : ℕ) : ℝ :=
  1 / (p : ℝ) ^ k - 1 / (p : ℝ) ^ (k + 1)

private lemma valDensity_bounds {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    0 ≤ valDensity p k ∧ valDensity p k ≤ 1 / 2 := by
  have hp1 : (1 : ℝ) ≤ p := mod_cast hp.one_lt.le
  have hpow : (p : ℝ) ^ k ≤ (p : ℝ) ^ (k + 1) := pow_le_pow_right₀ hp1 (Nat.le_succ k)
  have h2 : (2 : ℝ) ≤ (p : ℝ) ^ k :=
    (show (2 : ℝ) ≤ p from mod_cast hp.two_le).trans (le_self_pow₀ hp1 (by lia : k ≠ 0))
  refine ⟨sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) hpow), ?_⟩
  exact (sub_le_self _ (by positivity)).trans (one_div_le_one_div_of_le zero_lt_two h2)

/-- On positive integers `n`, the exact-valuation indicator `1_{n.factorization p = k}` for prime
`p` equals `1_{p ^ k ∣ n} - 1_{p ^ (k + 1) ∣ n}`. -/
private lemma ite_factorization_eq_sub {n p k : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    (if n.factorization p = k then (1 : ℝ) else 0) =
      (if p ^ k ∣ n then (1 : ℝ) else 0) - (if p ^ (k + 1) ∣ n then (1 : ℝ) else 0) := by
  simp only [hp.pow_dvd_iff_le_factorization hn]
  (split_ifs <;> try lia) <;> norm_num

/-- The count of `n ∈ Icc 1 N` with `n.factorization p = k` is at most `N / p ^ k` and within `1`
of `N * valDensity p k`. -/
private lemma sum_ite_factorization_bounds (N : ℕ) {p k : ℕ} (hp : p.Prime) :
    let C := ∑ n ∈ Icc 1 N, (if n.factorization p = k then (1 : ℝ) else 0)
    (0 ≤ C ∧ C ≤ (N : ℝ) / (p : ℝ) ^ k) ∧ |C - (N : ℝ) * valDensity p k| ≤ 1 := by
  intro C
  have hdvd (d : ℕ) : ∑ n ∈ Icc 1 N, (if d ∣ n then (1 : ℝ) else 0) = ((N / d : ℕ) : ℝ) := by
    rw [show Icc 1 N = Ioc 0 N from Icc_succ_left_eq_Ioc 0 N, sum_boole,
      Nat.Ioc_filter_dvd_card_eq_div]
  have hC_nonneg : 0 ≤ C := sum_nonneg fun _ _ ↦ by split_ifs <;> norm_num
  have hC_eq : C = ((N / p ^ k : ℕ) : ℝ) - ((N / p ^ (k + 1) : ℕ) : ℝ) := by
    calc C = ∑ n ∈ Icc 1 N, ((if p ^ k ∣ n then (1 : ℝ) else 0) -
              (if p ^ (k + 1) ∣ n then (1 : ℝ) else 0)) :=
            sum_congr rfl fun n hn ↦ ite_factorization_eq_sub
              (by have := (mem_Icc.mp hn).1; lia) hp
      _ = ((N / p ^ k : ℕ) : ℝ) - ((N / p ^ (k + 1) : ℕ) : ℝ) := by
            rw [sum_sub_distrib, hdvd, hdvd]
  have hle : C ≤ (N : ℝ) / (p : ℝ) ^ k := by
    rw [hC_eq]
    have h1 : ((N / p ^ k : ℕ) : ℝ) ≤ (N : ℝ) / ((p ^ k : ℕ) : ℝ) := Nat.cast_div_le
    push_cast at h1
    linarith [Nat.cast_nonneg (α := ℝ) (N / p ^ (k + 1))]
  refine ⟨⟨hC_nonneg, hle⟩, ?_⟩
  have hr1_0 : 0 ≤ (N : ℝ) / ((p ^ k : ℕ) : ℝ) - ((N / p ^ k : ℕ) : ℝ) :=
    sub_nonneg.mpr Nat.cast_div_le
  have hr1_1 := Nat.div_sub_cast_div_le_one (α := ℝ) N (p ^ k)
  have hr2_0 : 0 ≤ (N : ℝ) / ((p ^ (k + 1) : ℕ) : ℝ) - ((N / p ^ (k + 1) : ℕ) : ℝ) :=
    sub_nonneg.mpr Nat.cast_div_le
  have hr2_1 := Nat.div_sub_cast_div_le_one (α := ℝ) N (p ^ (k + 1))
  push_cast at hr1_0 hr1_1 hr2_0 hr2_1
  have hdiff : C - (N : ℝ) * valDensity p k =
      ((N : ℝ) / (p : ℝ) ^ (k + 1) - ((N / p ^ (k + 1) : ℕ) : ℝ)) -
        ((N : ℝ) / (p : ℝ) ^ k - ((N / p ^ k : ℕ) : ℝ)) := by
    rw [hC_eq, valDensity]; ring
  rw [hdiff, abs_le]
  exact ⟨by linarith, by linarith⟩

/-- For distinct primes `p ≠ q`, the joint count of `n ∈ Icc 1 N` with `n.factorization p = k` and
`n.factorization q = l` is within `2` of `N * valDensity p k * valDensity q l`. -/
private lemma abs_sum_ite_factorization_mul_sub_le (N : ℕ) {p q k l : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    |(∑ n ∈ Icc 1 N, (if n.factorization p = k then (1 : ℝ) else 0) *
        (if n.factorization q = l then (1 : ℝ) else 0)) -
      (N : ℝ) * valDensity p k * valDensity q l| ≤ 2 := by
  have hdvd (d : ℕ) : ∑ n ∈ Icc 1 N, (if d ∣ n then (1 : ℝ) else 0) = ((N / d : ℕ) : ℝ) := by
    rw [show Icc 1 N = Ioc 0 N from Icc_succ_left_eq_Ioc 0 N, sum_boole,
      Nat.Ioc_filter_dvd_card_eq_div]
  have hiff : ∀ i j n : ℕ, p ^ i * q ^ j ∣ n ↔ p ^ i ∣ n ∧ q ^ j ∣ n := fun i j n ↦
    ⟨fun h ↦ ⟨(dvd_mul_right _ _).trans h, (dvd_mul_left _ _).trans h⟩, fun ⟨h1, h2⟩ ↦
      (((Nat.coprime_primes hp hq).mpr hpq).pow i j).mul_dvd_of_dvd_of_dvd h1 h2⟩
  have hmul : ∀ i j n : ℕ, (if p ^ i ∣ n then (1 : ℝ) else 0) *
      (if q ^ j ∣ n then (1 : ℝ) else 0) = (if p ^ i * q ^ j ∣ n then (1 : ℝ) else 0) := by
    intro i j n; simp only [hiff]; split_ifs <;> simp_all
  have hsum : (∑ n ∈ Icc 1 N, (if n.factorization p = k then (1 : ℝ) else 0) *
        (if n.factorization q = l then (1 : ℝ) else 0)) =
      ((N / (p ^ k * q ^ l) : ℕ) : ℝ) - ((N / (p ^ k * q ^ (l + 1)) : ℕ) : ℝ) -
        ((N / (p ^ (k + 1) * q ^ l) : ℕ) : ℝ) +
          ((N / (p ^ (k + 1) * q ^ (l + 1)) : ℕ) : ℝ) := by
    trans ∑ n ∈ Icc 1 N, ((if p ^ k * q ^ l ∣ n then (1 : ℝ) else 0) -
        (if p ^ k * q ^ (l + 1) ∣ n then (1 : ℝ) else 0) -
        (if p ^ (k + 1) * q ^ l ∣ n then (1 : ℝ) else 0) +
        (if p ^ (k + 1) * q ^ (l + 1) ∣ n then (1 : ℝ) else 0))
    · refine sum_congr rfl fun n hn ↦ ?_
      have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; lia
      rw [ite_factorization_eq_sub hn0 hp, ite_factorization_eq_sub hn0 hq]
      linear_combination hmul k l n - hmul k (l + 1) n - hmul (k + 1) l n + hmul (k + 1) (l + 1) n
    · simp only [sum_add_distrib, sum_sub_distrib, hdvd]
  set r := fun d : ℕ ↦ (N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ)
  have hr0 : ∀ d, 0 ≤ r d := fun _ ↦ sub_nonneg.mpr Nat.cast_div_le
  have hr1 : ∀ d, r d ≤ 1 := fun d ↦ Nat.div_sub_cast_div_le_one N d
  have hdiff : (∑ n ∈ Icc 1 N, (if n.factorization p = k then (1 : ℝ) else 0) *
        (if n.factorization q = l then (1 : ℝ) else 0)) -
      (N : ℝ) * valDensity p k * valDensity q l =
      (r (p ^ k * q ^ (l + 1)) - r (p ^ k * q ^ l)) +
        (r (p ^ (k + 1) * q ^ l) - r (p ^ (k + 1) * q ^ (l + 1))) := by
    simp only [hsum, r, valDensity, Nat.cast_mul, Nat.cast_pow]; ring
  rw [hdiff, abs_le]
  constructor
  · linarith [hr0 (p ^ k * q ^ (l + 1)), hr1 (p ^ k * q ^ l),
      hr0 (p ^ (k + 1) * q ^ l), hr1 (p ^ (k + 1) * q ^ (l + 1))]
  · linarith [hr1 (p ^ k * q ^ (l + 1)), hr0 (p ^ k * q ^ l),
      hr1 (p ^ (k + 1) * q ^ l), hr0 (p ^ (k + 1) * q ^ (l + 1))]

/-- Centered valuation indicators at distinct primes have empirical correlation bounded by `3`. -/
private lemma abs_sum_centered_factorization_mul_le (N : ℕ) {p q k l : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hk : 1 ≤ k) (hl : 1 ≤ l) :
    |∑ n ∈ Icc 1 N, ((if n.factorization p = k then (1 : ℝ) else 0) - valDensity p k) *
        ((if n.factorization q = l then (1 : ℝ) else 0) - valDensity q l)| ≤ 3 := by
  set Ip : ℕ → ℝ := fun n ↦ if n.factorization p = k then 1 else 0
  set Iq : ℕ → ℝ := fun n ↦ if n.factorization q = l then 1 else 0
  have hconst (r : ℝ) : ∑ _n ∈ Icc 1 N, r = (N : ℝ) * r := by simp
  have hid : (∑ n ∈ Icc 1 N, (Ip n - valDensity p k) * (Iq n - valDensity q l)) =
      ((∑ n ∈ Icc 1 N, Ip n * Iq n) - (N : ℝ) * valDensity p k * valDensity q l) -
        valDensity q l * ((∑ n ∈ Icc 1 N, Ip n) - (N : ℝ) * valDensity p k) -
        valDensity p k * ((∑ n ∈ Icc 1 N, Iq n) - (N : ℝ) * valDensity q l) := by
    have hexp : ∀ n, (Ip n - valDensity p k) * (Iq n - valDensity q l) =
        (Ip n * Iq n - valDensity q l * Ip n - valDensity p k * Iq n) +
          valDensity p k * valDensity q l := fun _ ↦ by ring
    simp_rw [hexp, sum_add_distrib, sum_sub_distrib, ← mul_sum, hconst]; ring
  obtain ⟨hα0, hα⟩ := valDensity_bounds hp hk
  obtain ⟨hβ0, hβ⟩ := valDensity_bounds hq hl
  have hJ := abs_sum_ite_factorization_mul_sub_le N hp hq hpq (k := k) (l := l)
  have hCp := (sum_ite_factorization_bounds N hp (k := k)).2
  have hCq := (sum_ite_factorization_bounds N hq (k := l)).2
  set E12 := (∑ n ∈ Icc 1 N, Ip n * Iq n) - (N : ℝ) * valDensity p k * valDensity q l
  set E1 := (∑ n ∈ Icc 1 N, Ip n) - (N : ℝ) * valDensity p k
  set E2 := (∑ n ∈ Icc 1 N, Iq n) - (N : ℝ) * valDensity q l
  rw [hid]
  have h1 := abs_sub (E12 - valDensity q l * E1) (valDensity p k * E2)
  have h2 := abs_sub E12 (valDensity q l * E1)
  rw [abs_mul, abs_of_nonneg hα0] at h1
  rw [abs_mul, abs_of_nonneg hβ0] at h2
  nlinarith

/-- Single-prime diagonal second moment for a centered prime-power linear combination. -/
private lemma sum_centered_single_prime_sq_le (N : ℕ) (f : ArithmeticFunction ℝ)
    {p : ℕ} (hp : p.Prime) (M : ℕ) :
    let K := Icc 1 (p.log M)
    let Y : ℕ → ℝ := fun n ↦
      ∑ k ∈ K, f (p ^ k) * ((if n.factorization p = k then (1 : ℝ) else 0) - valDensity p k)
    ∑ n ∈ Icc 1 N, Y n ^ 2 ≤
      (N : ℝ) * (∑ k ∈ K, f (p ^ k) ^ 2 / (p : ℝ) ^ k) + (∑ k ∈ K, |f (p ^ k)|) ^ 2 := by
  intro K Y
  set g : ℕ → ℝ := fun n ↦ ∑ k ∈ K, if n.factorization p = k then f (p ^ k) else 0
  set μ : ℝ := ∑ k ∈ K, f (p ^ k) * valDensity p k
  have hY : ∀ n, Y n = g n - μ := fun n ↦ by
    simp only [Y, g, μ, mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero]
  have hg2_le : ∑ n ∈ Icc 1 N, g n ^ 2 ≤ (N : ℝ) * ∑ k ∈ K, f (p ^ k) ^ 2 / (p : ℝ) ^ k := by
    have hgsq : ∀ n, g n ^ 2 = ∑ k ∈ K, if n.factorization p = k then f (p ^ k) ^ 2 else 0 :=
      fun n ↦ K.sum_ite_pow_of_subsingleton (n.factorization p = ·) (fun k ↦ f (p ^ k)) two_ne_zero
        fun _ _ _ _ h1 h2 ↦ h1.symm.trans h2
    simp_rw [hgsq]
    rw [sum_comm, mul_sum]
    refine sum_le_sum fun k _ ↦ ?_
    calc (∑ n ∈ Icc 1 N, if n.factorization p = k then f (p ^ k) ^ 2 else 0)
        = f (p ^ k) ^ 2 * ∑ n ∈ Icc 1 N, (if n.factorization p = k then (1 : ℝ) else 0) := by
          rw [mul_sum]; refine sum_congr rfl fun _ _ ↦ by split_ifs <;> ring
      _ ≤ f (p ^ k) ^ 2 * ((N : ℝ) / (p : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left (sum_ite_factorization_bounds N hp).1.2 (sq_nonneg _)
      _ = (N : ℝ) * (f (p ^ k) ^ 2 / (p : ℝ) ^ k) := by ring
  set δ : ℝ := (∑ n ∈ Icc 1 N, g n) - (N : ℝ) * μ
  have hδ_abs : |δ| ≤ ∑ k ∈ K, |f (p ^ k)| := by
    have hδ_eq : δ = ∑ k ∈ K, f (p ^ k) *
        ((∑ n ∈ Icc 1 N, (if n.factorization p = k then (1 : ℝ) else 0)) -
          (N : ℝ) * valDensity p k) := by
      simp only [δ, g, μ, mul_sum]
      rw [sum_comm, ← sum_sub_distrib]
      refine sum_congr rfl fun k _ ↦ ?_
      have : (∑ n ∈ Icc 1 N, if n.factorization p = k then f (p ^ k) else 0) =
          f (p ^ k) * ∑ n ∈ Icc 1 N, (if n.factorization p = k then (1 : ℝ) else 0) := by
        rw [mul_sum]; refine sum_congr rfl fun _ _ ↦ by split_ifs <;> ring
      rw [this]; ring
    rw [hδ_eq]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ ↦ ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (sum_ite_factorization_bounds N hp).2
  have hvar : ∑ n ∈ Icc 1 N, Y n ^ 2 ≤ (∑ n ∈ Icc 1 N, g n ^ 2) + δ ^ 2 / (N : ℝ) := by
    simpa [hY, δ] using (Icc 1 N).sum_sub_sq_le_sum_sq_add_div g μ
  have hδ_div : δ ^ 2 / (N : ℝ) ≤ (∑ k ∈ K, |f (p ^ k)|) ^ 2 := by
    rcases eq_or_ne N 0 with rfl | hN0
    · simp [sq_nonneg]
    · exact (div_le_self (sq_nonneg δ) (mod_cast Nat.pos_of_ne_zero hN0)).trans
        ((sq_abs δ).symm ▸ pow_le_pow_left₀ (abs_nonneg δ) hδ_abs 2)
  exact hvar.trans (add_le_add hg2_le hδ_div)

end ValuationCounts

/-! ### Small and large prime-power variance bounds -/

section SplitBounds

/-- Distinct-prime off-diagonal correlation bound for centered small-prime-power sums. -/
private lemma sum_small_centered_mul_le (N M : ℕ) (f : ArithmeticFunction ℝ)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    let Y : ℕ → ℕ → ℝ := fun r n ↦ ∑ k ∈ Icc 1 (r.log M),
      f (r ^ k) * ((if n.factorization r = k then (1 : ℝ) else 0) - valDensity r k)
    ∑ n ∈ Icc 1 N, Y p n * Y q n ≤
      3 * ((∑ k ∈ Icc 1 (p.log M), |f (p ^ k)|) * ∑ l ∈ Icc 1 (q.log M), |f (q ^ l)|) := by
  intro Y
  have hexp : ∑ n ∈ Icc 1 N, Y p n * Y q n =
      ∑ k ∈ Icc 1 (p.log M), ∑ l ∈ Icc 1 (q.log M), f (p ^ k) * f (q ^ l) *
        ∑ n ∈ Icc 1 N, ((if n.factorization p = k then (1 : ℝ) else 0) - valDensity p k) *
          ((if n.factorization q = l then (1 : ℝ) else 0) - valDensity q l) := by
    trans ∑ n ∈ Icc 1 N, ∑ k ∈ Icc 1 (p.log M), ∑ l ∈ Icc 1 (q.log M),
        f (p ^ k) * f (q ^ l) *
          (((if n.factorization p = k then (1 : ℝ) else 0) - valDensity p k) *
            ((if n.factorization q = l then (1 : ℝ) else 0) - valDensity q l))
    · refine sum_congr rfl fun n _ ↦ ?_
      simp only [Y, sum_mul_sum]
      exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring
    · rw [sum_comm]
      refine sum_congr rfl fun k _ ↦ ?_
      rw [sum_comm]
      exact sum_congr rfl fun l _ ↦ (mul_sum _ _ _).symm
  rw [hexp]
  calc _ ≤ ∑ k ∈ Icc 1 (p.log M), ∑ l ∈ Icc 1 (q.log M), |f (p ^ k)| * |f (q ^ l)| * 3 := by
        refine sum_le_sum fun k hk ↦ sum_le_sum fun l hl ↦ ?_
        set Ckl := ∑ n ∈ Icc 1 N,
          ((if n.factorization p = k then (1 : ℝ) else 0) - valDensity p k) *
            ((if n.factorization q = l then (1 : ℝ) else 0) - valDensity q l)
        have hcorr : |Ckl| ≤ 3 :=
          abs_sum_centered_factorization_mul_le N hp hq hpq (mem_Icc.mp hk).1 (mem_Icc.mp hl).1
        calc f (p ^ k) * f (q ^ l) * Ckl
            ≤ |f (p ^ k) * f (q ^ l) * Ckl| := le_abs_self _
          _ = |f (p ^ k)| * |f (q ^ l)| * |Ckl| := by rw [abs_mul, abs_mul]
          _ ≤ |f (p ^ k)| * |f (q ^ l)| * 3 := mul_le_mul_of_nonneg_left hcorr (by positivity)
    _ = 3 * ((∑ k ∈ Icc 1 (p.log M), |f (p ^ k)|) * ∑ l ∈ Icc 1 (q.log M), |f (q ^ l)|) := by
        rw [sum_mul_sum, mul_sum]
        refine sum_congr rfl fun _ _ ↦ ?_
        rw [mul_sum]
        exact sum_congr rfl fun _ _ ↦ by ring

/-- Cauchy–Schwarz bound `(∑_{p^k ≤ √N} |f(p^k)|) ^ 2 ≤ N * B_S` via `∑_{q ≤ √N} q ≤ N`. -/
private lemma sum_primesLE_abs_pow_sq_le (N : ℕ) (f : ArithmeticFunction ℝ) :
    let M := N.sqrt
    (∑ p ∈ Nat.primesLE M, ∑ k ∈ Icc 1 (p.log M), |f (p ^ k)|) ^ 2 ≤
      (N : ℝ) * ∑ p ∈ Nat.primesLE M, ∑ k ∈ Icc 1 (p.log M), f (p ^ k) ^ 2 / (p : ℝ) ^ k := by
  intro M
  have hW_reg : (∑ p ∈ Nat.primesLE M, ∑ k ∈ Icc 1 (p.log M), |f (p ^ k)|) =
      ∑ q ∈ Icc 1 M, (if IsPrimePow q then |f q| else 0) := by
    symm
    refine (Nat.sum_Icc_eq_sum_primesLE_sum_Icc_log (fun _ hn ↦ ite_eq_right hn) M).trans ?_
    exact sum_congr rfl fun p hp ↦ sum_congr rfl fun k hk ↦ ite_eq_left
      ((Nat.prime_of_mem_primesLE hp).isPrimePow.pow (by have := (mem_Icc.mp hk).1; lia))
  have hB_reg : (∑ p ∈ Nat.primesLE M, ∑ k ∈ Icc 1 (p.log M), f (p ^ k) ^ 2 / (p : ℝ) ^ k) =
      ∑ q ∈ Icc 1 M, (if IsPrimePow q then f q ^ 2 / (q : ℝ) else 0) := by
    symm
    refine (Nat.sum_Icc_eq_sum_primesLE_sum_Icc_log (fun _ hn ↦ ite_eq_right hn) M).trans ?_
    refine sum_congr rfl fun p hp ↦ sum_congr rfl fun k hk ↦ ?_
    rw [ite_eq_left ((Nat.prime_of_mem_primesLE hp).isPrimePow.pow
      (by have := (mem_Icc.mp hk).1; lia)), Nat.cast_pow]
  rw [hW_reg, hB_reg, mul_comm]
  refine (sum_sq_le_sum_mul_sum_of_sq_le_mul (Icc 1 M)
    (f := fun q ↦ if IsPrimePow q then f q ^ 2 / (q : ℝ) else 0) (g := fun q ↦ (q : ℝ))
    (fun _ _ ↦ by split_ifs <;> positivity) (fun _ _ ↦ by positivity) fun q hq ↦ ?_).trans ?_
  · split_ifs
    · have hq0 : (q : ℝ) ≠ 0 := mod_cast (by have := (mem_Icc.mp hq).1; lia : q ≠ 0)
      rw [sq_abs, div_mul_cancel₀ _ hq0]
    · simp
  · refine mul_le_mul_of_nonneg_left ?_ (sum_nonneg fun _ _ ↦ by split_ifs <;> positivity)
    have hsq : ∑ q ∈ Icc 1 M, q ≤ N := by
      calc ∑ q ∈ Icc 1 M, q ≤ #(Icc 1 M) • M :=
            sum_le_card_nsmul (Icc 1 M) id M fun q hq ↦ (mem_Icc.mp hq).2
        _ = M * M := by simp
        _ ≤ N := Nat.sqrt_le N
    rw [← Nat.cast_sum]
    exact_mod_cast hsq

/-- Shifting `valDensity p k = 1 / p ^ k - 1 / p ^ (k + 1)` to `1 / p ^ k` changes the small-prime
expectation by at most `√B_S`. -/
private lemma small_density_shift_sq_le (M : ℕ) (f : ArithmeticFunction ℝ) :
    let AS := ∑ p ∈ Nat.primesLE M, ∑ k ∈ Icc 1 (p.log M), f (p ^ k) / (p : ℝ) ^ k
    let μS := ∑ p ∈ Nat.primesLE M, ∑ k ∈ Icc 1 (p.log M), f (p ^ k) * valDensity p k
    let BS := ∑ p ∈ Nat.primesLE M, ∑ k ∈ Icc 1 (p.log M), f (p ^ k) ^ 2 / (p : ℝ) ^ k
    (AS - μS) ^ 2 ≤ BS := by
  intro AS μS BS
  set S := (Nat.primesLE M).sigma fun p ↦ Icc 1 (p.log M)
  have hB_nonneg : 0 ≤ BS :=
    sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ div_nonneg (sq_nonneg _) (by positivity)
  have hdiff : AS - μS = ∑ x ∈ S, f (x.1 ^ x.2) / (x.1 : ℝ) ^ (x.2 + 1) := by
    rw [sum_sigma]
    simp only [AS, μS, valDensity, ← sum_sub_distrib]
    exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring
  have hBS_eq : BS = ∑ x ∈ S, f (x.1 ^ x.2) ^ 2 / (x.1 : ℝ) ^ x.2 := by rw [sum_sigma]
  have hcs : (∑ x ∈ S, |f (x.1 ^ x.2)| / (x.1 : ℝ) ^ (x.2 + 1)) ^ 2 ≤
      BS * ∑ x ∈ S, ((x.1 : ℝ) ^ (x.2 + 2))⁻¹ := by
    rw [hBS_eq]
    refine sum_sq_le_sum_mul_sum_of_sq_le_mul S (fun _ _ ↦ by positivity)
      (fun _ _ ↦ by positivity) fun x hx ↦ ?_
    have hp0 : (x.1 : ℝ) ≠ 0 := mod_cast (Nat.prime_of_mem_primesLE (mem_sigma.mp hx).1).ne_zero
    rw [div_pow, sq_abs]; field_simp; exact le_of_eq (by ring)
  have htail : ∑ x ∈ S, ((x.1 : ℝ) ^ (x.2 + 2))⁻¹ ≤ 1 := by
    rw [sum_sigma]
    refine (sum_le_sum fun p hp ↦ ?_).trans (Nat.sum_primesLE_inv_mul_sub_one_le_one M)
    have hmap : ∑ k ∈ Icc 1 (p.log M), ((p : ℝ) ^ (k + 2))⁻¹ ≤
        ∑ j ∈ Icc 2 (p.log M + 2), ((p : ℝ) ^ j)⁻¹ := by
      calc ∑ k ∈ Icc 1 (p.log M), ((p : ℝ) ^ (k + 2))⁻¹
          = ∑ j ∈ (Icc 1 (p.log M)).map ⟨(· + 2), add_left_injective 2⟩, ((p : ℝ) ^ j)⁻¹ := by
            rw [sum_map]; simp only [Function.Embedding.coeFn_mk]
        _ ≤ ∑ j ∈ Icc 2 (p.log M + 2), ((p : ℝ) ^ j)⁻¹ := by
            refine sum_le_sum_of_subset_of_nonneg (fun j hj ↦ ?_) fun _ _ _ ↦ by positivity
            obtain ⟨k, hk, rfl⟩ := mem_map.mp hj
            simp only [Function.Embedding.coeFn_mk, mem_Icc] at hk ⊢; lia
    exact hmap.trans (TauCeti.sum_Icc_inv_pow_le (Nat.prime_of_mem_primesLE hp).ne_one _)
  have habs : |AS - μS| ≤ ∑ x ∈ S, |f (x.1 ^ x.2)| / (x.1 : ℝ) ^ (x.2 + 1) := by
    rw [hdiff]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ ↦ ?_)
    have hx0 : (0 : ℝ) ≤ (x.1 : ℝ) ^ (x.2 + 1) := by positivity
    rw [abs_div, abs_of_nonneg hx0]
  calc (AS - μS) ^ 2 = |AS - μS| ^ 2 := (sq_abs _).symm
    _ ≤ (∑ x ∈ S, |f (x.1 ^ x.2)| / (x.1 : ℝ) ^ (x.2 + 1)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ ≤ BS * ∑ x ∈ S, ((x.1 : ℝ) ^ (x.2 + 2))⁻¹ := hcs
    _ ≤ BS * 1 := mul_le_mul_of_nonneg_left htail hB_nonneg
    _ = BS := mul_one BS

/-- Small prime powers `p ^ k ≤ M` (`M = Nat.sqrt N`) satisfy
`∑_{n ≤ N} (f_S(n) - A_S) ^ 2 ≤ 10 * N * B_S`. -/
private lemma sum_small_prime_powers_sub_sq_le (N : ℕ) (f : ArithmeticFunction ℝ) :
    let M := N.sqrt
    let fS : ℕ → ℝ := fun n ↦ ∑ p ∈ Nat.primesLE M, ∑ k ∈ Icc 1 (p.log M),
      if n.factorization p = k then f (p ^ k) else 0
    let AS : ℝ := ∑ p ∈ Nat.primesLE M, ∑ k ∈ Icc 1 (p.log M), f (p ^ k) / (p : ℝ) ^ k
    let BS : ℝ := ∑ p ∈ Nat.primesLE M, ∑ k ∈ Icc 1 (p.log M), f (p ^ k) ^ 2 / (p : ℝ) ^ k
    ∑ n ∈ Icc 1 N, (fS n - AS) ^ 2 ≤ 10 * (N : ℝ) * BS := by
  intro M fS AS BS
  set Y : ℕ → ℕ → ℝ := fun p n ↦ ∑ k ∈ Icc 1 (p.log M),
    f (p ^ k) * ((if n.factorization p = k then (1 : ℝ) else 0) - valDensity p k)
  set μS : ℝ := ∑ p ∈ Nat.primesLE M, ∑ k ∈ Icc 1 (p.log M), f (p ^ k) * valDensity p k
  set W : ℕ → ℝ := fun p ↦ ∑ k ∈ Icc 1 (p.log M), |f (p ^ k)|
  have hY_sum : ∀ n, ∑ p ∈ Nat.primesLE M, Y p n = fS n - μS := fun n ↦ by
    simp only [Y, fS, μS, mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero]
  have hcentered : ∑ n ∈ Icc 1 N, (fS n - μS) ^ 2 ≤
      (N : ℝ) * BS + 3 * (∑ p ∈ Nat.primesLE M, W p) ^ 2 := by
    calc ∑ n ∈ Icc 1 N, (fS n - μS) ^ 2
        = ∑ p ∈ Nat.primesLE M, ∑ q ∈ Nat.primesLE M, ∑ n ∈ Icc 1 N, Y p n * Y q n := by
          simp_rw [← hY_sum, sq, sum_mul_sum]
          rw [sum_comm]
          exact sum_congr rfl fun _ _ ↦ sum_comm
      _ ≤ ∑ p ∈ Nat.primesLE M, ∑ q ∈ Nat.primesLE M,
            ((if p = q then (N : ℝ) * ∑ k ∈ Icc 1 (p.log M), f (p ^ k) ^ 2 / (p : ℝ) ^ k else 0) +
              3 * (W p * W q)) := by
          refine sum_le_sum fun p hp ↦ sum_le_sum fun q hq ↦ ?_
          by_cases hpq : p = q
          · subst hpq
            simp only [ite_true, ← sq]
            have hdiag := sum_centered_single_prime_sq_le N f (Nat.prime_of_mem_primesLE hp) M
            linarith [sq_nonneg (W p)]
          · simp only [hpq, ite_false, zero_add]
            exact sum_small_centered_mul_le N M f (Nat.prime_of_mem_primesLE hp)
              (Nat.prime_of_mem_primesLE hq) hpq
      _ = (N : ℝ) * BS + 3 * (∑ p ∈ Nat.primesLE M, W p) ^ 2 := by
          simp only [sum_add_distrib]
          congr 1
          · rw [mul_sum]
            refine sum_congr rfl fun p hp ↦ ?_
            rw [sum_eq_single p (fun q _ hqp ↦ ite_eq_right hqp.symm) (fun h ↦ absurd hp h),
              ite_eq_left rfl]
          · rw [sq, sum_mul_sum, mul_sum]
            refine sum_congr rfl fun _ _ ↦ ?_
            rw [mul_sum]
  have hW_sq : (∑ p ∈ Nat.primesLE M, W p) ^ 2 ≤ (N : ℝ) * BS := sum_primesLE_abs_pow_sq_le N f
  have hshift_sq : (AS - μS) ^ 2 ≤ BS := small_density_shift_sq_le M f
  have hconst (r : ℝ) : ∑ _n ∈ Icc 1 N, r = (N : ℝ) * r := by simp
  calc ∑ n ∈ Icc 1 N, (fS n - AS) ^ 2
      ≤ ∑ n ∈ Icc 1 N, (2 * (fS n - μS) ^ 2 + 2 * (AS - μS) ^ 2) :=
        sum_le_sum fun n _ ↦ by nlinarith [sq_nonneg ((fS n - μS) + (AS - μS))]
    _ = 2 * (∑ n ∈ Icc 1 N, (fS n - μS) ^ 2) + 2 * (N : ℝ) * (AS - μS) ^ 2 := by
        simp only [sum_add_distrib, ← mul_sum, hconst]; ring
    _ ≤ 10 * (N : ℝ) * BS := by nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- At most one prime power exceeding `Nat.sqrt N` can exactly divide `n ∈ Icc 1 N`. -/
private lemma large_prime_powers_subsingleton {N n : ℕ} (hn : n ∈ Icc 1 N) :
    let L := ((Nat.primesLE N).sigma fun p ↦ Icc 1 (p.log N)).filter fun x ↦ N.sqrt < x.1 ^ x.2
    ∀ x ∈ L, ∀ y ∈ L, n.factorization x.1 = x.2 → n.factorization y.1 = y.2 → x = y := by
  intro L x hx y hy hnx hny
  by_contra hxy
  have hp : x.1.Prime := Nat.prime_of_mem_primesLE (mem_sigma.mp (mem_filter.mp hx).1).1
  have hq : y.1.Prime := Nat.prime_of_mem_primesLE (mem_sigma.mp (mem_filter.mp hy).1).1
  have hpq : x.1 ≠ y.1 := fun h ↦ hxy (Sigma.ext h (heq_of_eq (by rw [← hnx, ← hny, h])))
  have hdvd : (x.1 ^ x.2) * (y.1 ^ y.2) ∣ n :=
    (((Nat.coprime_primes hp hq).mpr hpq).pow x.2 y.2).mul_dvd_of_dvd_of_dvd
      (hnx ▸ Nat.ordProj_dvd n x.1) (hny ▸ Nat.ordProj_dvd n y.1)
  have hle : (x.1 ^ x.2) * (y.1 ^ y.2) ≤ N :=
    (Nat.le_of_dvd (by have := (mem_Icc.mp hn).1; lia) hdvd).trans (mem_Icc.mp hn).2
  have hgt : N < (N.sqrt + 1) * (N.sqrt + 1) := Nat.lt_succ_sqrt N
  have h1 : N.sqrt + 1 ≤ x.1 ^ x.2 := (mem_filter.mp hx).2
  have h2 : N.sqrt + 1 ≤ y.1 ^ y.2 := (mem_filter.mp hy).2
  nlinarith

/-- Large primes (`k = 1`, `N.sqrt < p ≤ N`) have reciprocal sum at most `11`. -/
private lemma sum_large_prime_powers_exp_one_inv_le (N : ℕ) :
    let L := ((Nat.primesLE N).sigma fun p ↦ Icc 1 (p.log N)).filter fun x ↦ N.sqrt < x.1 ^ x.2
    ∑ x ∈ L.filter (fun x ↦ x.2 = 1), ((x.1 : ℝ) ^ x.2)⁻¹ ≤ 11 := by
  intro L
  have hinj : ∀ x ∈ L.filter (fun x ↦ x.2 = 1), ∀ y ∈ L.filter (fun x ↦ x.2 = 1),
      x.1 = y.1 → x = y := fun x hx y hy h ↦
    Sigma.ext h (heq_of_eq ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm))
  have himg : ∑ x ∈ L.filter (fun x ↦ x.2 = 1), ((x.1 : ℝ) ^ x.2)⁻¹ ≤
      ∑ p ∈ (Nat.primesLE N).filter (N.sqrt < ·), (p : ℝ)⁻¹ := by
    calc ∑ x ∈ L.filter (fun x ↦ x.2 = 1), ((x.1 : ℝ) ^ x.2)⁻¹
        = ∑ p ∈ (L.filter (fun x ↦ x.2 = 1)).image Sigma.fst, (p : ℝ)⁻¹ := by
          rw [sum_image hinj]
          exact sum_congr rfl fun x hx ↦ by rw [(mem_filter.mp hx).2, pow_one]
      _ ≤ ∑ p ∈ (Nat.primesLE N).filter (N.sqrt < ·), (p : ℝ)⁻¹ := by
          refine sum_le_sum_of_subset_of_nonneg (fun p hp ↦ ?_) fun _ _ _ ↦ by positivity
          obtain ⟨⟨p, k⟩, hx, rfl⟩ := mem_image.mp hp
          obtain ⟨hxL, rfl⟩ := mem_filter.mp hx
          obtain ⟨hxsig, hxgt⟩ := mem_filter.mp hxL
          exact mem_filter.mpr ⟨(mem_sigma.mp hxsig).1, by simpa using hxgt⟩
  refine himg.trans ?_
  rcases lt_or_ge N 4 with hN4 | hN4
  · have hsub : (Nat.primesLE N).filter (N.sqrt < ·) ⊆ Icc 1 3 := fun p hp ↦ by
      have hp' := (mem_filter.mp hp).1
      exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hp').pos,
        (Nat.le_of_mem_primesLE hp').trans (by lia)⟩
    refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity).trans ?_
    norm_num [sum_Icc_succ_top]
  · set m := N.sqrt + 1
    have hm3 : 3 ≤ m := by have := Nat.le_sqrt.mpr (by lia : 2 * 2 ≤ N); lia
    have hm1 : (1 : ℝ) < m := mod_cast (by lia : 1 < m)
    have hlogm_pos : 0 < Real.log m := Real.log_pos hm1
    have hsub : (Nat.primesLE N).filter (N.sqrt < ·) ⊆
        (Nat.primesLE ⌊(N : ℝ)⌋₊).filter (fun p : ℕ ↦ (m : ℝ) ≤ (p : ℝ)) := fun p hp ↦ by
      obtain ⟨hpN, hgt⟩ := mem_filter.mp hp
      rw [Nat.floor_natCast]
      exact mem_filter.mpr ⟨hpN, mod_cast hgt⟩
    refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity).trans
      ((Chebyshev.sum_primesLE_filter_ge_inv_le (mod_cast (by lia : 1 ≤ N)) hm1).trans ?_)
    have hlog3 : (2 : ℝ) / 3 ≤ Real.log m := by
      have hm3' : (3 : ℝ) ≤ m := mod_cast hm3
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 3)
      rw [one_div, Real.log_inv] at h
      linarith [Real.log_le_log (by norm_num) hm3']
    have hlogN : Real.log N ≤ 2 * Real.log m := by
      have hsq : (N : ℝ) < (m : ℝ) ^ 2 := by
        simpa [m, sq] using (Nat.cast_lt (α := ℝ)).mpr (Nat.lt_succ_sqrt N)
      have := Real.log_lt_log (by positivity) hsq
      rw [Real.log_pow] at this; push_cast at this; linarith
    rw [div_le_iff₀ hlogm_pos]
    linarith [Real.log_four_le_two]

/-- Reciprocal sum over large prime powers `√N < p ^ k ≤ N` is at most `12`. -/
private lemma sum_large_prime_powers_inv_le (N : ℕ) :
    let L := ((Nat.primesLE N).sigma fun p ↦ Icc 1 (p.log N)).filter fun x ↦ N.sqrt < x.1 ^ x.2
    ∑ x ∈ L, ((x.1 : ℝ) ^ x.2)⁻¹ ≤ 12 := by
  intro L
  rw [← sum_filter_add_sum_filter_not L (fun x ↦ x.2 = 1)]
  have h1 : ∑ x ∈ L.filter (fun x ↦ x.2 = 1), ((x.1 : ℝ) ^ x.2)⁻¹ ≤ 11 :=
    sum_large_prime_powers_exp_one_inv_le N
  have h2 : ∑ x ∈ L.filter (fun x ↦ ¬ x.2 = 1), ((x.1 : ℝ) ^ x.2)⁻¹ ≤ 1 := by
    have hsub : L.filter (fun x ↦ ¬ x.2 = 1) ⊆
        (Nat.primesLE N).sigma fun p ↦ Icc 2 (p.log N) := fun x hx ↦ by
      obtain ⟨hxL, hne1⟩ := mem_filter.mp hx
      obtain ⟨hp, hk⟩ := mem_sigma.mp (mem_filter.mp hxL).1
      rw [mem_Icc] at hk
      exact mem_sigma.mpr ⟨hp, mem_Icc.mpr ⟨by lia, hk.2⟩⟩
    refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity).trans ?_
    rw [sum_sigma]
    exact Nat.sum_primesLE_sum_Icc_two_inv_pow_le_one N
  exact (add_le_add h1 h2).trans (by norm_num)

/-- Uncentered second moment of the large-prime-power part `f_L` on `Icc 1 N`. -/
private lemma sum_large_prime_powers_sq_le (N : ℕ) (f : ArithmeticFunction ℝ) :
    let L := ((Nat.primesLE N).sigma fun p ↦ Icc 1 (p.log N)).filter fun x ↦ N.sqrt < x.1 ^ x.2
    let fL : ℕ → ℝ := fun n ↦ ∑ x ∈ L, if n.factorization x.1 = x.2 then f (x.1 ^ x.2) else 0
    ∑ n ∈ Icc 1 N, fL n ^ 2 ≤
      (N : ℝ) * ∑ x ∈ L, f (x.1 ^ x.2) ^ 2 / (x.1 : ℝ) ^ x.2 := by
  intro L fL
  have hpt : ∀ n ∈ Icc 1 N,
      fL n ^ 2 = ∑ x ∈ L, if n.factorization x.1 = x.2 then f (x.1 ^ x.2) ^ 2 else 0 :=
    fun n hn ↦ L.sum_ite_pow_of_subsingleton (fun x ↦ n.factorization x.1 = x.2)
      (fun x ↦ f (x.1 ^ x.2)) two_ne_zero (large_prime_powers_subsingleton hn)
  rw [sum_congr rfl hpt, sum_comm, mul_sum]
  refine sum_le_sum fun x hx ↦ ?_
  have hp := Nat.prime_of_mem_primesLE (mem_sigma.mp (mem_filter.mp hx).1).1
  calc (∑ n ∈ Icc 1 N, if n.factorization x.1 = x.2 then f (x.1 ^ x.2) ^ 2 else 0)
      = f (x.1 ^ x.2) ^ 2 *
          ∑ n ∈ Icc 1 N, (if n.factorization x.1 = x.2 then (1 : ℝ) else 0) := by
        rw [mul_sum]; refine sum_congr rfl fun _ _ ↦ by split_ifs <;> ring
    _ ≤ f (x.1 ^ x.2) ^ 2 * ((N : ℝ) / (x.1 : ℝ) ^ x.2) :=
        mul_le_mul_of_nonneg_left (sum_ite_factorization_bounds N hp).1.2 (sq_nonneg _)
    _ = (N : ℝ) * (f (x.1 ^ x.2) ^ 2 / (x.1 : ℝ) ^ x.2) := by ring

/-- First-moment discrepancy of the large-prime-power part `f_L` on `Icc 1 N`. -/
private lemma abs_sum_large_prime_powers_sub_le (N : ℕ) (f : ArithmeticFunction ℝ) :
    let L := ((Nat.primesLE N).sigma fun p ↦ Icc 1 (p.log N)).filter fun x ↦ N.sqrt < x.1 ^ x.2
    let fL : ℕ → ℝ := fun n ↦ ∑ x ∈ L, if n.factorization x.1 = x.2 then f (x.1 ^ x.2) else 0
    let AL : ℝ := ∑ x ∈ L, f (x.1 ^ x.2) / (x.1 : ℝ) ^ x.2
    |(∑ n ∈ Icc 1 N, fL n) - (N : ℝ) * AL| ≤
      (N : ℝ) * ∑ x ∈ L, |f (x.1 ^ x.2)| / (x.1 : ℝ) ^ x.2 := by
  intro L fL AL
  have hS1_eq : (∑ n ∈ Icc 1 N, fL n) - (N : ℝ) * AL = ∑ x ∈ L, f (x.1 ^ x.2) *
      ((∑ n ∈ Icc 1 N, (if n.factorization x.1 = x.2 then (1 : ℝ) else 0)) -
        (N : ℝ) / (x.1 : ℝ) ^ x.2) := by
    simp only [fL, AL, mul_sum]
    rw [sum_comm, ← sum_sub_distrib]
    refine sum_congr rfl fun x _ ↦ ?_
    have : (∑ n ∈ Icc 1 N, if n.factorization x.1 = x.2 then f (x.1 ^ x.2) else 0) =
        f (x.1 ^ x.2) * ∑ n ∈ Icc 1 N, (if n.factorization x.1 = x.2 then (1 : ℝ) else 0) := by
      rw [mul_sum]; refine sum_congr rfl fun _ _ ↦ by split_ifs <;> ring
    rw [this]; ring
  rw [hS1_eq, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x hx ↦ ?_)
  have hp := Nat.prime_of_mem_primesLE (mem_sigma.mp (mem_filter.mp hx).1).1
  obtain ⟨hC0, hCle⟩ := (sum_ite_factorization_bounds N hp (k := x.2)).1
  have hD0 : 0 ≤ (N : ℝ) / (x.1 : ℝ) ^ x.2 := by positivity
  have habs : |(∑ n ∈ Icc 1 N, (if n.factorization x.1 = x.2 then (1 : ℝ) else 0)) -
      (N : ℝ) / (x.1 : ℝ) ^ x.2| ≤ (N : ℝ) / (x.1 : ℝ) ^ x.2 := by
    generalize (N : ℝ) / (x.1 : ℝ) ^ x.2 = D at hCle hD0 ⊢
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left habs (abs_nonneg _)).trans_eq (by ring)

/-- Large prime powers `M < p ^ k ≤ N` (`M = Nat.sqrt N`) satisfy
`∑_{n ≤ N} (f_L(n) - A_L) ^ 2 ≤ 13 * N * B_L`. -/
private lemma sum_large_prime_powers_sub_sq_le (N : ℕ) (f : ArithmeticFunction ℝ) :
    let L := ((Nat.primesLE N).sigma fun p ↦ Icc 1 (p.log N)).filter fun x ↦ N.sqrt < x.1 ^ x.2
    let fL : ℕ → ℝ := fun n ↦ ∑ x ∈ L, if n.factorization x.1 = x.2 then f (x.1 ^ x.2) else 0
    let AL : ℝ := ∑ x ∈ L, f (x.1 ^ x.2) / (x.1 : ℝ) ^ x.2
    let BL : ℝ := ∑ x ∈ L, f (x.1 ^ x.2) ^ 2 / (x.1 : ℝ) ^ x.2
    ∑ n ∈ Icc 1 N, (fL n - AL) ^ 2 ≤ 13 * (N : ℝ) * BL := by
  intro L fL AL BL
  rcases eq_or_ne N 0 with rfl | hN0
  · simp [BL]
  have hN_pos : (0 : ℝ) < N := mod_cast Nat.pos_of_ne_zero hN0
  have hB_nonneg : 0 ≤ BL := sum_nonneg fun _ _ ↦ div_nonneg (sq_nonneg _) (by positivity)
  have hcs : (∑ x ∈ L, |f (x.1 ^ x.2)| / (x.1 : ℝ) ^ x.2) ^ 2 ≤ 12 * BL := by
    calc (∑ x ∈ L, |f (x.1 ^ x.2)| / (x.1 : ℝ) ^ x.2) ^ 2
        ≤ BL * ∑ x ∈ L, ((x.1 : ℝ) ^ x.2)⁻¹ := by
          refine sum_sq_le_sum_mul_sum_of_sq_le_mul L (fun _ _ ↦ by positivity)
            (fun _ _ ↦ by positivity) fun x hx ↦ ?_
          have hp0 : (x.1 : ℝ) ≠ 0 :=
            mod_cast (Nat.prime_of_mem_primesLE (mem_sigma.mp (mem_filter.mp hx).1).1).ne_zero
          rw [div_pow, sq_abs]; field_simp; exact le_rfl
      _ ≤ BL * 12 := mul_le_mul_of_nonneg_left (sum_large_prime_powers_inv_le N) hB_nonneg
      _ = 12 * BL := mul_comm _ _
  have hvar : ∑ n ∈ Icc 1 N, (fL n - AL) ^ 2 ≤
      (∑ n ∈ Icc 1 N, fL n ^ 2) + ((∑ n ∈ Icc 1 N, fL n) - (N : ℝ) * AL) ^ 2 / (N : ℝ) := by
    simpa using (Icc 1 N).sum_sub_sq_le_sum_sq_add_div fL AL
  have hmean : ((∑ n ∈ Icc 1 N, fL n) - (N : ℝ) * AL) ^ 2 / (N : ℝ) ≤ 12 * (N : ℝ) * BL := by
    rw [div_le_iff₀ hN_pos]
    calc ((∑ n ∈ Icc 1 N, fL n) - (N : ℝ) * AL) ^ 2
        = |(∑ n ∈ Icc 1 N, fL n) - (N : ℝ) * AL| ^ 2 := (sq_abs _).symm
      _ ≤ ((N : ℝ) * ∑ x ∈ L, |f (x.1 ^ x.2)| / (x.1 : ℝ) ^ x.2) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (abs_sum_large_prime_powers_sub_le N f) 2
      _ = (N : ℝ) ^ 2 * (∑ x ∈ L, |f (x.1 ^ x.2)| / (x.1 : ℝ) ^ x.2) ^ 2 := mul_pow _ _ 2
      _ ≤ (N : ℝ) ^ 2 * (12 * BL) := mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ = 12 * (N : ℝ) * BL * (N : ℝ) := by ring
  exact hvar.trans ((add_le_add (sum_large_prime_powers_sq_le N f) hmean).trans_eq (by ring))

/-- Prime-power pairs `(p, k)` with `p ≤ N`, `1 ≤ k ≤ p.log N`, and `p ^ k ≤ N.sqrt` are precisely
the pairs with `p ≤ N.sqrt` and `1 ≤ k ≤ p.log N.sqrt`. -/
private lemma primesLE_sigma_Icc_log_filter_not_gt_sqrt (N : ℕ) :
    (((Nat.primesLE N).sigma fun p ↦ Icc 1 (p.log N)).filter fun x ↦ ¬ N.sqrt < x.1 ^ x.2) =
      (Nat.primesLE N.sqrt).sigma fun p ↦ Icc 1 (p.log N.sqrt) := by
  ext ⟨p, k⟩
  simp only [mem_filter, mem_sigma, Nat.mem_primesLE, mem_Icc, not_lt]
  refine ⟨fun ⟨⟨⟨_, hp⟩, hk1, _⟩, hpk⟩ ↦ ?_, fun ⟨⟨hpM, hp⟩, hk1, hkM⟩ ↦ ?_⟩
  · exact ⟨⟨(le_self_pow₀ hp.one_lt.le (by lia : k ≠ 0)).trans hpk, hp⟩,
      hk1, Nat.le_log_of_pow_le hp.one_lt hpk⟩
  · have := hp.two_le
    have hM0 : N.sqrt ≠ 0 := by lia
    have hMN : N.sqrt ≤ N := Nat.sqrt_le_self N
    exact ⟨⟨⟨hpM.trans hMN, hp⟩, hk1, hkM.trans (Nat.log_mono_right hMN)⟩,
      Nat.pow_le_of_le_log hM0 hkM⟩

end SplitBounds

/-! ### The Turán–Kubilius inequality -/

namespace IsAdditive

/-- Prime-power cutoff expansion of an additive function on `n ∈ Icc 1 N`. -/
theorem apply_eq_sum_primesLE_Icc_log {R : Type*} [AddCommMonoid R] {f : ArithmeticFunction R}
    (hf : f.IsAdditive) {N n : ℕ} (hn : n ∈ Icc 1 N) :
    f n = ∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N),
      if n.factorization p = k then f (p ^ k) else 0 := by
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
  have hn_pos : 0 < n := by lia
  rw [hf.sum_primeFactors_pow_factorization n]
  have hsub : n.primeFactors ⊆ Nat.primesLE N := fun p hp ↦
    Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd hn_pos (Nat.dvd_of_mem_primeFactors hp)).trans hnN,
      Nat.prime_of_mem_primeFactors hp⟩
  refine (sum_congr rfl fun p hp ↦ ?_).trans (sum_subset hsub fun p _ hp ↦ ?_)
  · have hp' := Nat.prime_of_mem_primeFactors hp
    have hk1 : 1 ≤ n.factorization p :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (Nat.support_factorization n ▸ hp))
    have hkN : n.factorization p ≤ p.log N :=
      Nat.le_log_of_pow_le hp'.one_lt ((Nat.le_of_dvd hn_pos (Nat.ordProj_dvd n p)).trans hnN)
    symm
    rw [sum_eq_single (n.factorization p) (fun k _ hk ↦ ite_eq_right hk.symm)
      (fun h ↦ absurd (mem_Icc.mpr ⟨hk1, hkN⟩) h), ite_eq_left rfl]
  · have h0 : n.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (Nat.support_factorization n ▸ hp)
    exact sum_eq_zero fun k hk ↦ ite_eq_right (by rw [h0]; have := (mem_Icc.mp hk).1; lia)

/-- **The Turán–Kubilius inequality** (`Icc 1 (p.log N)` form). For any real-valued additive
arithmetic function `f` and any `N : ℕ`,
`∑ n ∈ Icc 1 N, (f n - A) ^ 2 ≤ 30 * N * B`, where
`A = ∑_{p ≤ N} ∑_{1 ≤ k ≤ log_p N} f(p ^ k) / p ^ k` and
`B = ∑_{p ≤ N} ∑_{1 ≤ k ≤ log_p N} f(p ^ k) ^ 2 / p ^ k`. -/
theorem sum_Icc_log_sub_sq_le {f : ArithmeticFunction ℝ} (hf : f.IsAdditive) (N : ℕ) :
    let A := ∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), f (p ^ k) / (p : ℝ) ^ k
    let B := ∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), f (p ^ k) ^ 2 / (p : ℝ) ^ k
    ∑ n ∈ Icc 1 N, (f n - A) ^ 2 ≤ 30 * (N : ℝ) * B := by
  intro A B
  set I := (Nat.primesLE N).sigma fun p ↦ Icc 1 (p.log N)
  set L := I.filter fun x ↦ N.sqrt < x.1 ^ x.2
  have hsplit : ∀ g : (Σ _ : ℕ, ℕ) → ℝ,
      (∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), g ⟨p, k⟩) =
        (∑ p ∈ Nat.primesLE N.sqrt, ∑ k ∈ Icc 1 (p.log N.sqrt), g ⟨p, k⟩) + ∑ x ∈ L, g x := by
    intro g
    rw [← sum_sigma, ← sum_filter_add_sum_filter_not I (fun x ↦ N.sqrt < x.1 ^ x.2),
      primesLE_sigma_Icc_log_filter_not_gt_sqrt N, sum_sigma, add_comm]
  set fS : ℕ → ℝ := fun n ↦ ∑ p ∈ Nat.primesLE N.sqrt, ∑ k ∈ Icc 1 (p.log N.sqrt),
    if n.factorization p = k then f (p ^ k) else 0
  set fL : ℕ → ℝ := fun n ↦ ∑ x ∈ L, if n.factorization x.1 = x.2 then f (x.1 ^ x.2) else 0
  set AS : ℝ := ∑ p ∈ Nat.primesLE N.sqrt, ∑ k ∈ Icc 1 (p.log N.sqrt), f (p ^ k) / (p : ℝ) ^ k
  set AL : ℝ := ∑ x ∈ L, f (x.1 ^ x.2) / (x.1 : ℝ) ^ x.2
  set BS : ℝ := ∑ p ∈ Nat.primesLE N.sqrt, ∑ k ∈ Icc 1 (p.log N.sqrt),
    f (p ^ k) ^ 2 / (p : ℝ) ^ k
  set BL : ℝ := ∑ x ∈ L, f (x.1 ^ x.2) ^ 2 / (x.1 : ℝ) ^ x.2
  have hf_eq : ∀ n ∈ Icc 1 N, f n = fS n + fL n := fun n hn ↦
    (hf.apply_eq_sum_primesLE_Icc_log hn).trans
      (hsplit fun x ↦ if n.factorization x.1 = x.2 then f (x.1 ^ x.2) else 0)
  have hA_eq : A = AS + AL := hsplit fun x ↦ f (x.1 ^ x.2) / (x.1 : ℝ) ^ x.2
  have hB_eq : B = BS + BL := hsplit fun x ↦ f (x.1 ^ x.2) ^ 2 / (x.1 : ℝ) ^ x.2
  have hBS_nonneg : 0 ≤ BS :=
    sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ div_nonneg (sq_nonneg _) (by positivity)
  have hBL_nonneg : 0 ≤ BL := sum_nonneg fun _ _ ↦ div_nonneg (sq_nonneg _) (by positivity)
  have hsmall := sum_small_prime_powers_sub_sq_le N f
  have hlarge := sum_large_prime_powers_sub_sq_le N f
  calc ∑ n ∈ Icc 1 N, (f n - A) ^ 2
      ≤ ∑ n ∈ Icc 1 N, (2 * (fS n - AS) ^ 2 + 2 * (fL n - AL) ^ 2) := by
        refine sum_le_sum fun n hn ↦ ?_
        rw [hf_eq n hn, hA_eq]
        nlinarith [sq_nonneg ((fS n - AS) - (fL n - AL))]
    _ = 2 * (∑ n ∈ Icc 1 N, (fS n - AS) ^ 2) + 2 * (∑ n ∈ Icc 1 N, (fL n - AL) ^ 2) := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    _ ≤ 30 * (N : ℝ) * B := by
        rw [hB_eq]; nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- **The Turán–Kubilius inequality.** For any real-valued additive arithmetic function `f` and
any `N : ℕ`, `∑ n ∈ Icc 1 N, (f n - A) ^ 2 ≤ 30 * N * B`, where `A` and `B` sum `f (p ^ k) / p ^ k`
and `f (p ^ k) ^ 2 / p ^ k` over primes `p ≤ N` and exponents `1 ≤ k ≤ N` with `p ^ k ≤ N`. -/
theorem sum_Icc_sub_sq_le {f : ArithmeticFunction ℝ} (hf : f.IsAdditive) (N : ℕ) :
    let A := ∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 N,
      if p ^ k ≤ N then f (p ^ k) / (p ^ k : ℕ) else 0
    let B := ∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 N,
      if p ^ k ≤ N then f (p ^ k) ^ 2 / (p ^ k : ℕ) else 0
    ∑ n ∈ Icc 1 N, (f n - A) ^ 2 ≤ 30 * (N : ℝ) * B := by
  intro A B
  have hA : A = ∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), f (p ^ k) / (p : ℝ) ^ k := by
    refine sum_congr rfl fun p hp ↦ ?_
    simpa [Nat.cast_pow] using Nat.sum_Icc_ite_pow_le_eq_sum_Icc_log
      (Nat.prime_of_mem_primesLE hp).one_lt N (fun k ↦ f (p ^ k) / (p ^ k : ℕ))
  have hB : B = ∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), f (p ^ k) ^ 2 / (p : ℝ) ^ k := by
    refine sum_congr rfl fun p hp ↦ ?_
    simpa [Nat.cast_pow] using Nat.sum_Icc_ite_pow_le_eq_sum_Icc_log
      (Nat.prime_of_mem_primesLE hp).one_lt N (fun k ↦ f (p ^ k) ^ 2 / (p ^ k : ℕ))
  rw [hA, hB]
  exact hf.sum_Icc_log_sub_sq_le N

end IsAdditive

namespace IsStronglyAdditive

/-- For a strongly additive function, the full prime-power variance proxy
`∑_{p ≤ N} ∑_{1 ≤ k ≤ log_p N} f(p ^ k) ^ 2 / p ^ k` is at most twice `∑_{p ≤ N} f(p) ^ 2 / p`. -/
theorem sum_primesLE_Icc_log_sq_le {f : ArithmeticFunction ℝ} (hf : f.IsStronglyAdditive)
    (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), f (p ^ k) ^ 2 / (p : ℝ) ^ k) ≤
      2 * ∑ p ∈ Nat.primesLE N, f p ^ 2 / (p : ℝ) := by
  rw [mul_sum]
  refine sum_le_sum fun p hp ↦ ?_
  have hp' := Nat.prime_of_mem_primesLE hp
  have hp2 : (2 : ℝ) ≤ p := mod_cast hp'.two_le
  have hrew : ∑ k ∈ Icc 1 (p.log N), f (p ^ k) ^ 2 / (p : ℝ) ^ k =
      f p ^ 2 * ∑ k ∈ Icc 1 (p.log N), ((p : ℝ) ^ k)⁻¹ := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk ↦ ?_
    rw [hf.map_prime_pow hp' (by have := (mem_Icc.mp hk).1; lia), div_eq_mul_inv]
  rw [hrew]
  have hinv : ∑ k ∈ Icc 1 (p.log N), ((p : ℝ) ^ k)⁻¹ ≤ 2 / (p : ℝ) := by
    have h1 : 1 ≤ p.log N := Nat.log_pos hp'.one_lt (Nat.le_of_mem_primesLE hp)
    have hsplit : Icc 1 (p.log N) = insert 1 (Icc 2 (p.log N)) := by
      ext k; simp only [mem_insert, mem_Icc]; lia
    rw [hsplit, sum_insert (by simp), pow_one, ← one_div]
    have htail := TauCeti.sum_Icc_inv_pow_le hp'.ne_one (p.log N)
    have hp_pos : (0 : ℝ) < p := by linarith
    have hle : 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 / (p : ℝ) :=
      one_div_le_one_div_of_le hp_pos (by nlinarith)
    have htwo : (2 : ℝ) / (p : ℝ) = 1 / (p : ℝ) + 1 / (p : ℝ) := by ring
    linarith
  calc f p ^ 2 * ∑ k ∈ Icc 1 (p.log N), ((p : ℝ) ^ k)⁻¹
      ≤ f p ^ 2 * (2 / (p : ℝ)) := mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
    _ = 2 * (f p ^ 2 / (p : ℝ)) := by ring

/-- For a strongly additive function, subtracting the prime sum `∑_{p ≤ N} f(p) / p` from the full
prime-power sum leaves the higher-power tail `∑_{p ≤ N} f(p) * ∑_{2 ≤ k ≤ log_p N} (p ^ k)⁻¹`. -/
theorem sum_primesLE_Icc_log_sub_eq {f : ArithmeticFunction ℝ} (hf : f.IsStronglyAdditive)
    (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), f (p ^ k) / (p : ℝ) ^ k) -
        (∑ p ∈ Nat.primesLE N, f p / (p : ℝ)) =
      ∑ p ∈ Nat.primesLE N, f p * ∑ k ∈ Icc 2 (p.log N), ((p : ℝ) ^ k)⁻¹ := by
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun p hp ↦ ?_
  have hp' := Nat.prime_of_mem_primesLE hp
  have h1 : 1 ≤ p.log N := Nat.log_pos hp'.one_lt (Nat.le_of_mem_primesLE hp)
  have hsplit : Icc 1 (p.log N) = insert 1 (Icc 2 (p.log N)) := by
    ext k; simp only [mem_insert, mem_Icc]; lia
  rw [hsplit, sum_insert (by simp), pow_one]
  have h2 : (∑ k ∈ Icc 2 (p.log N), f (p ^ k) / (p : ℝ) ^ k) =
      f p * ∑ k ∈ Icc 2 (p.log N), ((p : ℝ) ^ k)⁻¹ := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk ↦ ?_
    rw [hf.map_prime_pow hp' (by have := (mem_Icc.mp hk).1; lia), div_eq_mul_inv]
  rw [h2]; ring

/-- For a strongly additive function, the squared higher-power expectation tail `(A_full - A) ^ 2`
is bounded by `∑_{p ≤ N} f(p) ^ 2 / p`. -/
theorem sub_sum_primesLE_sq_le {f : ArithmeticFunction ℝ} (hf : f.IsStronglyAdditive) (N : ℕ) :
    ((∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), f (p ^ k) / (p : ℝ) ^ k) -
        ∑ p ∈ Nat.primesLE N, f p / (p : ℝ)) ^ 2 ≤
      ∑ p ∈ Nat.primesLE N, f p ^ 2 / (p : ℝ) := by
  set B := ∑ p ∈ Nat.primesLE N, f p ^ 2 / (p : ℝ)
  have hB_nonneg : 0 ≤ B := sum_nonneg fun _ _ ↦ div_nonneg (sq_nonneg _) (by positivity)
  have habs : |(∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), f (p ^ k) / (p : ℝ) ^ k) -
      ∑ p ∈ Nat.primesLE N, f p / (p : ℝ)| ≤
      ∑ p ∈ Nat.primesLE N, |f p| / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [hf.sum_primesLE_Icc_log_sub_eq N]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p hp ↦ ?_)
    have hp' := Nat.prime_of_mem_primesLE hp
    have h0 : 0 ≤ ∑ k ∈ Icc 2 (p.log N), ((p : ℝ) ^ k)⁻¹ := sum_nonneg fun _ _ ↦ by positivity
    rw [abs_mul, abs_of_nonneg h0, div_eq_mul_inv, ← one_div]
    exact mul_le_mul_of_nonneg_left (TauCeti.sum_Icc_inv_pow_le hp'.ne_one _) (abs_nonneg _)
  have hcs : (∑ p ∈ Nat.primesLE N, |f p| / ((p : ℝ) * ((p : ℝ) - 1))) ^ 2 ≤
      B * ∑ p ∈ Nat.primesLE N, 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    refine sum_sq_le_sum_mul_sum_of_sq_le_mul (Nat.primesLE N)
      (fun _ _ ↦ div_nonneg (sq_nonneg _) (by positivity))
      (fun p hp ↦ by
        have hp2 : (2 : ℝ) ≤ p := mod_cast (Nat.prime_of_mem_primesLE hp).two_le
        exact div_nonneg zero_le_one (mul_nonneg (by linarith) (by linarith)))
      fun p hp ↦ ?_
    have hp2 : (2 : ℝ) ≤ p := mod_cast (Nat.prime_of_mem_primesLE hp).two_le
    have hp0 : (0 : ℝ) < p := by linarith
    rw [div_pow, sq_abs]
    calc f p ^ 2 / ((p : ℝ) * ((p : ℝ) - 1)) ^ 2
        = f p ^ 2 / (p : ℝ) * (1 / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)) := by field_simp
      _ ≤ f p ^ 2 / (p : ℝ) * (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
          refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (sq_nonneg _) hp0.le)
          exact one_div_le_one_div_of_le (mul_pos hp0 (by linarith)) (by nlinarith)
  calc ((∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), f (p ^ k) / (p : ℝ) ^ k) -
        ∑ p ∈ Nat.primesLE N, f p / (p : ℝ)) ^ 2
      = |(∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), f (p ^ k) / (p : ℝ) ^ k) -
          ∑ p ∈ Nat.primesLE N, f p / (p : ℝ)| ^ 2 := (sq_abs _).symm
    _ ≤ (∑ p ∈ Nat.primesLE N, |f p| / ((p : ℝ) * ((p : ℝ) - 1))) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ ≤ B * ∑ p ∈ Nat.primesLE N, 1 / ((p : ℝ) * ((p : ℝ) - 1)) := hcs
    _ ≤ B * 1 := mul_le_mul_of_nonneg_left (Nat.sum_primesLE_inv_mul_sub_one_le_one N) hB_nonneg
    _ = B := mul_one B

/-- **Distinct-prime Turán–Kubilius inequality for strongly additive functions.** For any
real-valued strongly additive function `f` and any `N : ℕ`, replacing the full prime-power sums by
the prime sums `A = ∑_{p ≤ N} f(p) / p` and `B = ∑_{p ≤ N} f(p) ^ 2 / p` yields
`∑ n ∈ Icc 1 N, (f n - A) ^ 2 ≤ 77 * N * B`. -/
theorem sum_Icc_sub_sq_le {f : ArithmeticFunction ℝ} (hf : f.IsStronglyAdditive) (N : ℕ) :
    let A := ∑ p ∈ Nat.primesLE N, f p / (p : ℝ)
    let B := ∑ p ∈ Nat.primesLE N, f p ^ 2 / (p : ℝ)
    ∑ n ∈ Icc 1 N, (f n - A) ^ 2 ≤ 77 * (N : ℝ) * B := by
  intro A B
  set Afull := ∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), f (p ^ k) / (p : ℝ) ^ k
  have hfull := hf.isAdditive.sum_Icc_log_sub_sq_le N
  have hBfull := hf.sum_primesLE_Icc_log_sq_le N
  have hAdiff := hf.sub_sum_primesLE_sq_le N
  have hconst (r : ℝ) : ∑ _n ∈ Icc 1 N, r = (N : ℝ) * r := by simp
  calc ∑ n ∈ Icc 1 N, (f n - A) ^ 2
      ≤ ∑ n ∈ Icc 1 N, ((7 / 6 : ℝ) * (f n - Afull) ^ 2 + 7 * (Afull - A) ^ 2) :=
        sum_le_sum fun n _ ↦ by nlinarith [sq_nonneg ((f n - Afull) - 6 * (Afull - A))]
    _ = (7 / 6 : ℝ) * (∑ n ∈ Icc 1 N, (f n - Afull) ^ 2) + 7 * (N : ℝ) * (Afull - A) ^ 2 := by
        simp only [sum_add_distrib, ← mul_sum, hconst]; ring
    _ ≤ 77 * (N : ℝ) * B := by nlinarith [Nat.cast_nonneg (α := ℝ) N]

end IsStronglyAdditive

/-- **Turán's inequality (1934)** for the distinct-prime-factor counting function
`ω = cardDistinctFactors`: for every `N : ℕ`,
`∑ n ∈ Icc 1 N, (ω n - ∑_{p ≤ N} 1 / p) ^ 2 ≤ 77 * N * ∑_{p ≤ N} 1 / p`. -/
theorem sum_Icc_cardDistinctFactors_sub_sq_le (N : ℕ) :
    ∑ n ∈ Icc 1 N,
        ((cardDistinctFactors n : ℝ) - ∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹) ^ 2 ≤
      77 * (N : ℝ) * ∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹ := by
  have h := (isStronglyAdditive_cardDistinctFactors.natCast (R := ℝ)).sum_Icc_sub_sq_le N
  simp only [natCoe_apply] at h
  have h1 : (∑ p ∈ Nat.primesLE N, (cardDistinctFactors p : ℝ) / (p : ℝ)) =
      ∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹ :=
    sum_congr rfl fun p hp ↦ by
      simp [cardDistinctFactors_apply_prime (Nat.prime_of_mem_primesLE hp), one_div]
  have h2 : (∑ p ∈ Nat.primesLE N, (cardDistinctFactors p : ℝ) ^ 2 / (p : ℝ)) =
      ∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹ :=
    sum_congr rfl fun p hp ↦ by
      simp [cardDistinctFactors_apply_prime (Nat.prime_of_mem_primesLE hp), one_div]
  simpa only [h1, h2] using h

end ArithmeticFunction
