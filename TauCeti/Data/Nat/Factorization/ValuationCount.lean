/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TauCeti.Data.Nat.Cast.Order.Field
import TauCeti.Data.Nat.Div
import TauCeti.Data.Nat.Factorization.Basic
import TauCeti.Data.Nat.Interval

/-!
# Prime-valuation counts and discrepancy bounds on intervals

By `Nat.Prime.factorization_eq_iff_pow_dvd_and_not_pow_dvd`, a nonzero natural number `n` has
`p`-adic valuation `n.factorization p = k` at a prime `p` precisely when `p ^ k ∣ n` and
`¬p ^ (k + 1) ∣ n`. Combining inclusion–exclusion with `Nat.card_filter_Icc_one_dvd` on
`Finset.Icc 1 N` gives exact counts for one prime (`N / p ^ k - N / p ^ (k + 1)`) and for two
distinct primes (`p ≠ q`), together with the unconditional upper bound `≤ N / p ^ k` valid without
assuming `p` is prime (when `p` is not prime, `n.factorization p = 0` for every `n`).

Casting these counts to an `AddCommGroupWithOne` or linearly ordered `Semifield` gives exact
indicator-sum identities and the upper bound `≤ (N : α) / (p : α) ^ k`. In a linearly ordered
`Field`, expressing each integer quotient `N / d` via its fractional remainder
`(N : α) / d - (N / d : ℕ) ∈ [0, 1)` bounds the single-prime discrepancy around
`N * (1 / p ^ k - 1 / p ^ (k + 1))` strictly below `1`, the joint two-prime discrepancy strictly
below `2`, and the empirical correlation of centered valuation indicators at distinct primes `p ≠ q`
strictly below `3` across all `k, l : ℕ` (handling the `k = 0` and `l = 0` boundary cases by
noting that `1 - (1 - 1 / p) = 1 / p` cancels the single-prime remainder).

## Main results

* `Nat.card_filter_Icc_factorization_eq`, `Nat.card_filter_Icc_factorization_eq_le`,
  `Nat.card_filter_Icc_factorization_eq_and_eq`: exact single-prime and coprime two-prime valuation
  counts on `Finset.Icc 1 N`, and the unconditional upper bound `≤ N / p ^ k`.
* `Nat.sum_Icc_ite_factorization_eq`, `Nat.sum_Icc_ite_factorization_le`,
  `Nat.sum_Icc_ite_factorization_eq_and_eq`: indicator-sum forms over `Finset.Icc 1 N`.
* `Nat.abs_sum_Icc_ite_factorization_sub_lt_one`,
  `Nat.abs_sum_Icc_ite_factorization_mul_sub_lt_two`: single-prime (`< 1`) and two-prime (`< 2`)
  discrepancy bounds in any linearly ordered field.
* `Nat.abs_sum_Icc_ite_factorization_sub_mul_sub_lt_three`: centered pairwise correlation bound
  (`< 3`) for distinct primes `p ≠ q` and all `k, l : ℕ`.
-/

public section

open scoped Finset

namespace Nat

/-- For a prime `p`, the number of `n ∈ [1, N]` with `n.factorization p = k` equals
`N / p ^ k - N / p ^ (k + 1)`. -/
theorem card_filter_Icc_factorization_eq (N : ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    #{n ∈ Finset.Icc 1 N | n.factorization p = k} = N / p ^ k - N / p ^ (k + 1) := by
  have hsdiff : ({n ∈ Finset.Icc 1 N | n.factorization p = k} : Finset ℕ) =
      {n ∈ Finset.Icc 1 N | p ^ k ∣ n} \ {n ∈ Finset.Icc 1 N | p ^ (k + 1) ∣ n} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_sdiff]
    refine ⟨fun ⟨hn, hval⟩ ↦ ?_, fun ⟨⟨hn, hk⟩, hnk⟩ ↦ ⟨hn, ?_⟩⟩
    · obtain ⟨hk, hnk⟩ := (hp.factorization_eq_iff_pow_dvd_and_not_pow_dvd (by omega)).mp hval
      exact ⟨⟨hn, hk⟩, fun ⟨_, h⟩ ↦ hnk h⟩
    · exact (hp.factorization_eq_iff_pow_dvd_and_not_pow_dvd (by omega)).mpr
        ⟨hk, fun h ↦ hnk ⟨hn, h⟩⟩
  have hsub : ({n ∈ Finset.Icc 1 N | p ^ (k + 1) ∣ n} : Finset ℕ) ⊆
      {n ∈ Finset.Icc 1 N | p ^ k ∣ n} := fun n hn ↦ by
    obtain ⟨hn', hdvd⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hn', (pow_dvd_pow p (Nat.le_succ k)).trans hdvd⟩
  rw [hsdiff, Finset.card_sdiff_of_subset hsub, card_filter_Icc_one_dvd, card_filter_Icc_one_dvd]

/-- For all `N, p, k : ℕ` (without assuming `p` is prime), at most `N / p ^ k` numbers in `[1, N]`
satisfy `n.factorization p = k`. -/
theorem card_filter_Icc_factorization_eq_le (N p k : ℕ) :
    #{n ∈ Finset.Icc 1 N | n.factorization p = k} ≤ N / p ^ k := by
  by_cases hp : p.Prime
  · rw [card_filter_Icc_factorization_eq N hp k]
    exact Nat.sub_le _ _
  · have hzero : ∀ n : ℕ, n.factorization p = 0 := fun n ↦
      factorization_eq_zero_of_not_prime n hp
    rcases eq_or_ne k 0 with rfl | hk
    · simp [hzero]
    · simp [hzero, hk.symm]

/-- For distinct primes `p ≠ q`, the number of `n ∈ [1, N]` with `n.factorization p = k` and
`n.factorization q = l` is given by inclusion–exclusion over multiples of `p ^ i * q ^ j`
(`i ∈ {k, k + 1}`, `j ∈ {l, l + 1}`). -/
theorem card_filter_Icc_factorization_eq_and_eq (N : ℕ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (k l : ℕ) :
    #{n ∈ Finset.Icc 1 N | n.factorization p = k ∧ n.factorization q = l} =
      N / (p ^ k * q ^ l) - N / (p ^ k * q ^ (l + 1)) - N / (p ^ (k + 1) * q ^ l) +
        N / (p ^ (k + 1) * q ^ (l + 1)) := by
  have hiff : ∀ i j n : ℕ, p ^ i * q ^ j ∣ n ↔ p ^ i ∣ n ∧ q ^ j ∣ n := fun i j n ↦
    ⟨fun h ↦ ⟨(dvd_mul_right _ _).trans h, (dvd_mul_left _ _).trans h⟩, fun ⟨h1, h2⟩ ↦
      (((coprime_primes hp hq).mpr hpq).pow i j).mul_dvd_of_dvd_of_dvd h1 h2⟩
  let s : ℕ → ℕ → Finset ℕ := fun i j ↦ {n ∈ Finset.Icc 1 N | p ^ i * q ^ j ∣ n}
  have hs_card : ∀ i j, #(s i j) = N / (p ^ i * q ^ j) := fun i j ↦ card_filter_Icc_one_dvd N _
  have htarget : ({n ∈ Finset.Icc 1 N | n.factorization p = k ∧ n.factorization q = l} : Finset ℕ) =
      s k l \ (s k (l + 1) ∪ s (k + 1) l) := by
    ext n
    simp only [s, Finset.mem_filter, Finset.mem_Icc, Finset.mem_sdiff, Finset.mem_union, hiff]
    refine ⟨fun ⟨hn, hvp, hvq⟩ ↦ ?_, fun ⟨⟨hn, hpk, hql⟩, hnot⟩ ↦ ⟨hn, ?_, ?_⟩⟩
    · have hn0 : n ≠ 0 := by omega
      obtain ⟨hpk, hnpk⟩ := (hp.factorization_eq_iff_pow_dvd_and_not_pow_dvd hn0).mp hvp
      obtain ⟨hql, hnql⟩ := (hq.factorization_eq_iff_pow_dvd_and_not_pow_dvd hn0).mp hvq
      exact ⟨⟨hn, hpk, hql⟩, fun h ↦ h.elim (fun ⟨_, _, h'⟩ ↦ hnql h') (fun ⟨_, h', _⟩ ↦ hnpk h')⟩
    · have hn0 : n ≠ 0 := by omega
      exact (hp.factorization_eq_iff_pow_dvd_and_not_pow_dvd hn0).mpr
        ⟨hpk, fun h ↦ hnot (Or.inr ⟨hn, h, hql⟩)⟩
    · have hn0 : n ≠ 0 := by omega
      exact (hq.factorization_eq_iff_pow_dvd_and_not_pow_dvd hn0).mpr
        ⟨hql, fun h ↦ hnot (Or.inl ⟨hn, hpk, h⟩)⟩
  have hsub : s k (l + 1) ∪ s (k + 1) l ⊆ s k l := Finset.union_subset
    (fun n hn ↦ by
      simp only [s, Finset.mem_filter, hiff] at hn ⊢
      exact ⟨hn.1, hn.2.1, (pow_dvd_pow q (Nat.le_succ l)).trans hn.2.2⟩)
    (fun n hn ↦ by
      simp only [s, Finset.mem_filter, hiff] at hn ⊢
      exact ⟨hn.1, (pow_dvd_pow p (Nat.le_succ k)).trans hn.2.1, hn.2.2⟩)
  have hinter : s k (l + 1) ∩ s (k + 1) l = s (k + 1) (l + 1) := by
    ext n
    simp only [s, Finset.mem_inter, Finset.mem_filter, hiff]
    exact ⟨fun ⟨⟨hn, _, hql1⟩, _, hpk1, _⟩ ↦ ⟨hn, hpk1, hql1⟩, fun ⟨hn, hpk1, hql1⟩ ↦
      ⟨⟨hn, (pow_dvd_pow p (Nat.le_succ k)).trans hpk1, hql1⟩,
        hn, hpk1, (pow_dvd_pow q (Nat.le_succ l)).trans hql1⟩⟩
  have h1 := Finset.card_sdiff_add_card_eq_card hsub
  have h2 := Finset.card_union_add_card_inter (s k (l + 1)) (s (k + 1) l)
  rw [← htarget, hs_card] at h1
  rw [hinter, hs_card, hs_card, hs_card] at h2
  have hle := div_mul_add_div_mul_le_div N (p ^ k * q ^ l) hq.two_le hp.two_le
  rw [mul_assoc, ← pow_succ, mul_right_comm, ← pow_succ] at hle
  omega

/-- Indicator-sum form of `Nat.card_filter_Icc_factorization_eq` in any `AddCommGroupWithOne`. -/
theorem sum_Icc_ite_factorization_eq {α : Type*} [AddCommGroupWithOne α] (N : ℕ)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (if n.factorization p = k then (1 : α) else 0) =
      ((N / p ^ k : ℕ) : α) - ((N / p ^ (k + 1) : ℕ) : α) := by
  have hle : N / p ^ (k + 1) ≤ N / p ^ k :=
    Nat.div_le_div_left (Nat.pow_le_pow_right hp.pos (Nat.le_succ k)) (pow_pos hp.pos k)
  rw [Finset.sum_boole, card_filter_Icc_factorization_eq N hp k, Nat.cast_sub hle]

/-- For all `N, p, k : ℕ` (without assuming `p` is prime), the indicator sum of
`n.factorization p = k` over `Finset.Icc 1 N` in a linearly ordered semifield is at most
`N / p ^ k`. -/
theorem sum_Icc_ite_factorization_le {α : Type*} [Semifield α] [LinearOrder α]
    [IsStrictOrderedRing α] (N p k : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (if n.factorization p = k then (1 : α) else 0) ≤
      (N : α) / (p : α) ^ k := by
  rw [Finset.sum_boole]
  exact (Nat.cast_le.mpr (card_filter_Icc_factorization_eq_le N p k)).trans
    (by simpa [Nat.cast_pow] using Nat.cast_div_le (α := α) (m := N) (n := p ^ k))

/-- Indicator-sum form of `Nat.card_filter_Icc_factorization_eq_and_eq` in any
`AddCommGroupWithOne`. -/
theorem sum_Icc_ite_factorization_eq_and_eq {α : Type*} [AddCommGroupWithOne α] (N : ℕ)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (k l : ℕ) :
    ∑ n ∈ Finset.Icc 1 N,
        (if n.factorization p = k ∧ n.factorization q = l then (1 : α) else 0) =
      ((N / (p ^ k * q ^ l) : ℕ) : α) - ((N / (p ^ k * q ^ (l + 1)) : ℕ) : α) -
        ((N / (p ^ (k + 1) * q ^ l) : ℕ) : α) +
          ((N / (p ^ (k + 1) * q ^ (l + 1)) : ℕ) : α) := by
  have hle := div_mul_add_div_mul_le_div N (p ^ k * q ^ l) hq.two_le hp.two_le
  rw [mul_assoc, ← pow_succ, mul_right_comm, ← pow_succ] at hle
  rw [Finset.sum_boole, card_filter_Icc_factorization_eq_and_eq N hp hq hpq k l, Nat.cast_add,
    Nat.cast_sub (Nat.le_sub_of_add_le' hle), Nat.cast_sub (Nat.le_of_add_right_le hle)]

/-- For a prime `p`, the exact-valuation indicator sum over `Finset.Icc 1 N` is strictly within `1`
of `N * (1 / p ^ k - 1 / p ^ (k + 1))` in any linearly ordered field. -/
theorem abs_sum_Icc_ite_factorization_sub_lt_one {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α] (N : ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    |(∑ n ∈ Finset.Icc 1 N, (if n.factorization p = k then (1 : α) else 0)) -
      (N : α) * (1 / (p : α) ^ k - 1 / (p : α) ^ (k + 1))| < 1 := by
  have hr1_0 : (0 : α) ≤ (N : α) / ((p ^ k : ℕ) : α) - ((N / p ^ k : ℕ) : α) :=
    sub_nonneg.mpr Nat.cast_div_le
  have hr1_1 : (N : α) / ((p ^ k : ℕ) : α) - ((N / p ^ k : ℕ) : α) < 1 :=
    Nat.div_sub_cast_div_lt_one N (p ^ k)
  have hr2_0 : (0 : α) ≤ (N : α) / ((p ^ (k + 1) : ℕ) : α) - ((N / p ^ (k + 1) : ℕ) : α) :=
    sub_nonneg.mpr Nat.cast_div_le
  have hr2_1 : (N : α) / ((p ^ (k + 1) : ℕ) : α) - ((N / p ^ (k + 1) : ℕ) : α) < 1 :=
    Nat.div_sub_cast_div_lt_one N (p ^ (k + 1))
  push_cast at hr1_0 hr1_1 hr2_0 hr2_1
  have hdiff : (∑ n ∈ Finset.Icc 1 N, (if n.factorization p = k then (1 : α) else 0)) -
      (N : α) * (1 / (p : α) ^ k - 1 / (p : α) ^ (k + 1)) =
      ((N : α) / (p : α) ^ (k + 1) - ((N / p ^ (k + 1) : ℕ) : α)) -
        ((N : α) / (p : α) ^ k - ((N / p ^ k : ℕ) : α)) := by
    rw [sum_Icc_ite_factorization_eq N hp k]; ring
  rw [hdiff, abs_lt]
  exact ⟨by linarith, by linarith⟩

/-- For distinct primes `p ≠ q`, the joint exact-valuation indicator sum over `Finset.Icc 1 N` is
strictly within `2` of `N * (1 / p ^ k - 1 / p ^ (k + 1)) * (1 / q ^ l - 1 / q ^ (l + 1))` in any
linearly ordered field. -/
theorem abs_sum_Icc_ite_factorization_mul_sub_lt_two {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α] (N : ℕ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (k l : ℕ) :
    |(∑ n ∈ Finset.Icc 1 N, (if n.factorization p = k then (1 : α) else 0) *
        (if n.factorization q = l then (1 : α) else 0)) -
      (N : α) * (1 / (p : α) ^ k - 1 / (p : α) ^ (k + 1)) *
        (1 / (q : α) ^ l - 1 / (q : α) ^ (l + 1))| < 2 := by
  have hboole : ∀ n : ℕ, (if n.factorization p = k then (1 : α) else 0) *
      (if n.factorization q = l then (1 : α) else 0) =
      if n.factorization p = k ∧ n.factorization q = l then (1 : α) else 0 := fun n ↦ by
    split_ifs <;> simp_all
  have hsum : (∑ n ∈ Finset.Icc 1 N, (if n.factorization p = k then (1 : α) else 0) *
        (if n.factorization q = l then (1 : α) else 0)) =
      ((N / (p ^ k * q ^ l) : ℕ) : α) - ((N / (p ^ k * q ^ (l + 1)) : ℕ) : α) -
        ((N / (p ^ (k + 1) * q ^ l) : ℕ) : α) +
          ((N / (p ^ (k + 1) * q ^ (l + 1)) : ℕ) : α) := by
    simp_rw [hboole]
    exact sum_Icc_ite_factorization_eq_and_eq N hp hq hpq k l
  set r : ℕ → α := fun d ↦ (N : α) / (d : α) - ((N / d : ℕ) : α)
  have hr0 : ∀ d, 0 ≤ r d := fun _ ↦ sub_nonneg.mpr Nat.cast_div_le
  have hr1 : ∀ d, r d < 1 := fun d ↦ Nat.div_sub_cast_div_lt_one N d
  have hdiff : (∑ n ∈ Finset.Icc 1 N, (if n.factorization p = k then (1 : α) else 0) *
        (if n.factorization q = l then (1 : α) else 0)) -
      (N : α) * (1 / (p : α) ^ k - 1 / (p : α) ^ (k + 1)) *
        (1 / (q : α) ^ l - 1 / (q : α) ^ (l + 1)) =
      (r (p ^ k * q ^ (l + 1)) - r (p ^ k * q ^ l)) +
        (r (p ^ (k + 1) * q ^ l) - r (p ^ (k + 1) * q ^ (l + 1))) := by
    simp only [hsum, r, Nat.cast_mul, Nat.cast_pow]; ring
  rw [hdiff, abs_lt]
  constructor
  · linarith [hr0 (p ^ k * q ^ (l + 1)), hr1 (p ^ k * q ^ l),
      hr0 (p ^ (k + 1) * q ^ l), hr1 (p ^ (k + 1) * q ^ (l + 1))]
  · linarith [hr1 (p ^ k * q ^ (l + 1)), hr0 (p ^ k * q ^ l),
      hr1 (p ^ (k + 1) * q ^ l), hr0 (p ^ (k + 1) * q ^ (l + 1))]

/-- Helper for `Nat.abs_sum_Icc_ite_factorization_sub_mul_sub_lt_three`: the `k = 0` case, where
`1 - (1 - 1 / p) = 1 / p` cancels the `q`-only remainder term. -/
private lemma abs_sum_Icc_ite_factorization_zero_sub_mul_sub_lt_three {α : Type*} [Field α]
    [LinearOrder α] [IsStrictOrderedRing α] (N : ℕ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (l : ℕ) :
    |∑ n ∈ Finset.Icc 1 N,
        ((if n.factorization p = 0 then (1 : α) else 0) -
          (1 / (p : α) ^ 0 - 1 / (p : α) ^ (0 + 1))) *
        ((if n.factorization q = l then (1 : α) else 0) -
          (1 / (q : α) ^ l - 1 / (q : α) ^ (l + 1)))| < 3 := by
  set dq : α := 1 / (q : α) ^ l - 1 / (q : α) ^ (l + 1)
  set r : ℕ → α := fun d ↦ (N : α) / (d : α) - ((N / d : ℕ) : α)
  have hr0 : ∀ d, 0 ≤ r d := fun _ ↦ sub_nonneg.mpr Nat.cast_div_le
  have hr1 : ∀ d, r d < 1 := fun d ↦ Nat.div_sub_cast_div_lt_one N d
  have hboole : ∀ n : ℕ, (if n.factorization p = 0 then (1 : α) else 0) *
      (if n.factorization q = l then (1 : α) else 0) =
      if n.factorization p = 0 ∧ n.factorization q = l then (1 : α) else 0 := fun _ ↦ by
    split_ifs <;> simp_all
  have hval : ∑ n ∈ Finset.Icc 1 N,
      ((if n.factorization p = 0 then (1 : α) else 0) -
         (1 / (p : α) ^ 0 - 1 / (p : α) ^ (0 + 1))) *
      ((if n.factorization q = l then (1 : α) else 0) - dq) =
      1 / (p : α) * (r (q ^ (l + 1)) - r (q ^ l)) +
        (r (p * q ^ l) - r (p * q ^ (l + 1))) - dq * r p := by
    simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, hboole]
    rw [sum_Icc_ite_factorization_eq_and_eq N hp hq hpq 0 l,
      sum_Icc_ite_factorization_eq N hp 0, sum_Icc_ite_factorization_eq N hq l]
    simp only [dq, r, pow_zero, one_mul, pow_one, Nat.div_one, Nat.cast_mul, Nat.cast_pow,
      zero_add, div_one]; ring
  have hp1 : (1 : α) ≤ p := Nat.one_le_cast.mpr hp.one_lt.le
  have hq1 : (1 : α) ≤ q := Nat.one_le_cast.mpr hq.one_lt.le
  have ht1 : |1 / (p : α) * (r (q ^ (l + 1)) - r (q ^ l))| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (div_nonneg zero_le_one (by linarith))]
    exact (mul_le_of_le_one_left (abs_nonneg _)
      (div_le_one_of_le₀ hp1 (by linarith))).trans
      (abs_le.mpr ⟨by linarith [hr0 (q ^ (l + 1)), hr1 (q ^ l)],
        by linarith [hr1 (q ^ (l + 1)), hr0 (q ^ l)]⟩)
  have hdq0 : 0 ≤ dq := sub_nonneg.mpr (one_div_le_one_div_of_le (pow_pos (by linarith) l)
    (pow_le_pow_right₀ hq1 (Nat.le_succ l)))
  have hdq1 : dq ≤ 1 := (sub_le_self _ (div_nonneg zero_le_one
    (pow_nonneg (by linarith) _))).trans (div_le_one_of_le₀ (one_le_pow₀ hq1)
      (pow_nonneg (by linarith) _))
  have hmul0 : 0 ≤ dq * r p := mul_nonneg hdq0 (hr0 p)
  have hmul1 : dq * r p < 1 := (mul_le_of_le_one_left (hr0 p) hdq1).trans_lt (hr1 p)
  rw [hval, abs_lt]
  rw [abs_le] at ht1
  exact ⟨by linarith [hr0 (p * q ^ l), hr1 (p * q ^ (l + 1))],
    by linarith [hr1 (p * q ^ l), hr0 (p * q ^ (l + 1))]⟩

/-- Centered valuation indicators at distinct primes `p ≠ q` have empirical correlation strictly
bounded by `3` over `Finset.Icc 1 N` in any linearly ordered field, for all `k, l : ℕ`. -/
theorem abs_sum_Icc_ite_factorization_sub_mul_sub_lt_three {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α] (N : ℕ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (k l : ℕ) :
    |∑ n ∈ Finset.Icc 1 N,
        ((if n.factorization p = k then (1 : α) else 0) -
          (1 / (p : α) ^ k - 1 / (p : α) ^ (k + 1))) *
        ((if n.factorization q = l then (1 : α) else 0) -
          (1 / (q : α) ^ l - 1 / (q : α) ^ (l + 1)))| < 3 := by
  rcases eq_or_ne k 0 with rfl | hk
  · exact abs_sum_Icc_ite_factorization_zero_sub_mul_sub_lt_three N hp hq hpq l
  rcases eq_or_ne l 0 with rfl | hl
  · rw [Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _]
    exact abs_sum_Icc_ite_factorization_zero_sub_mul_sub_lt_three N hq hp hpq.symm k
  -- Main case `k ≠ 0`, `l ≠ 0`: `dp, dq ≤ 1 / 2` gives `|E12 - dq * E1 - dp * E2| < 2 + 1/2 + 1/2`.
  have hdens {r m : ℕ} (hr : r.Prime) (hm : m ≠ 0) :
      (0 : α) ≤ 1 / (r : α) ^ m - 1 / (r : α) ^ (m + 1) ∧
        1 / (r : α) ^ m - 1 / (r : α) ^ (m + 1) ≤ 1 / 2 := by
    have hr1 : (1 : α) ≤ r := Nat.one_le_cast.mpr hr.one_lt.le
    have hr2 : (2 : α) ≤ r := by exact_mod_cast hr.two_le
    exact ⟨sub_nonneg.mpr (one_div_le_one_div_of_le (pow_pos (by linarith) m)
        (pow_le_pow_right₀ hr1 (Nat.le_succ m))),
      (sub_le_self _ (div_nonneg zero_le_one (pow_nonneg (by linarith) _))).trans
        (one_div_le_one_div_of_le zero_lt_two (hr2.trans (le_self_pow₀ hr1 hm)))⟩
  set dp : α := 1 / (p : α) ^ k - 1 / (p : α) ^ (k + 1)
  set dq : α := 1 / (q : α) ^ l - 1 / (q : α) ^ (l + 1)
  obtain ⟨hdp0, hdp⟩ := hdens hp hk
  obtain ⟨hdq0, hdq⟩ := hdens hq hl
  have hJ := abs_sum_Icc_ite_factorization_mul_sub_lt_two (α := α) N hp hq hpq k l
  have hCp := abs_sum_Icc_ite_factorization_sub_lt_one (α := α) N hp k
  have hCq := abs_sum_Icc_ite_factorization_sub_lt_one (α := α) N hq l
  set E12 := (∑ n ∈ Finset.Icc 1 N, (if n.factorization p = k then (1 : α) else 0) *
      (if n.factorization q = l then (1 : α) else 0)) - (N : α) * dp * dq
  set E1 := (∑ n ∈ Finset.Icc 1 N, (if n.factorization p = k then (1 : α) else 0)) - (N : α) * dp
  set E2 := (∑ n ∈ Finset.Icc 1 N, (if n.factorization q = l then (1 : α) else 0)) - (N : α) * dq
  have hid : ∑ n ∈ Finset.Icc 1 N,
      ((if n.factorization p = k then (1 : α) else 0) - dp) *
      ((if n.factorization q = l then (1 : α) else 0) - dq) =
      E12 - dq * E1 - dp * E2 := by
    simp_rw [E12, E1, E2, sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
    ring
  rw [hid]
  have h1 := abs_sub (E12 - dq * E1) (dp * E2)
  have h2 := abs_sub E12 (dq * E1)
  rw [abs_mul, abs_of_nonneg hdp0] at h1
  rw [abs_mul, abs_of_nonneg hdq0] at h2
  have hm1 : dq * |E1| ≤ 1 / 2 := (mul_le_of_le_one_right hdq0 hCp.le).trans hdq
  have hm2 : dp * |E2| ≤ 1 / 2 := (mul_le_of_le_one_right hdp0 hCq.le).trans hdp
  linarith

end Nat
