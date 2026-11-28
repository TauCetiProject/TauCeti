/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.MaxPrimeFac
public import Mathlib.NumberTheory.SmoothNumbers

/-!
# Smooth numbers and the largest prime factor

An integer `n > 1` is `k`-smooth in Mathlib's sense (all prime factors less than `k`) exactly when
its largest prime factor is less than `k`. For a prime `p`, an integer `n` has largest prime
factor `p` exactly when `p ∣ n` and `n / p` has all its prime factors at most `p`; so
multiplication by `p` is a bijection from the positive integers up to `N / p` with all prime
factors at most `p` onto the integers in `[1, N]` with largest prime factor `p`.

Sorting the integers in `[1, N]` that are not `(k + 1)`-smooth by their largest prime factor
`p > k` gives the identity

  `#{n ≤ N : n is (k + 1)-smooth} + ∑_{k < p ≤ N} #{m ≤ N / p : m is (p + 1)-smooth} = N`,

the sum being over primes. For real cutoffs this is the recursion
`Ψ(x, y) + ∑_{y < p ≤ x} Ψ(x / p, p) = ⌊x⌋₊` for the smooth-number counting function, which
underlies the delay differential equation of the Dickman function (Hildebrand and Tenenbaum,
p. 414).

## Main definitions

* `Nat.Prime.smoothNumbersUpToEquiv`: for a prime `p`, multiplication by `p` as an equivalence
  from `Nat.smoothNumbersUpTo (N / p) (p + 1)` onto the integers in `[1, N]` with largest prime
  factor `p`.

## Main results

* `Nat.mem_smoothNumbers_iff_maxPrimeFac_lt`: for `n > 1`, `n` is `k`-smooth exactly when
  `n.maxPrimeFac < k`.
* `Nat.Prime.maxPrimeFac_eq_iff`: `n.maxPrimeFac = p ↔ p ∣ n ∧ n / p ∈ Nat.smoothNumbers (p + 1)`.
* `Nat.Prime.card_filter_Icc_maxPrimeFac_eq`: the number of integers in `[1, N]` with largest
  prime factor `p`.
* `Nat.smoothNumbersUpTo_card_add_sum`: the identity above.

## References

* A. Hildebrand, G. Tenenbaum, *Integers without large prime factors*, J. Théor. Nombres
  Bordeaux 5 (1993), 411–484, p. 414, for the role of the recursion in the fixed-`u` limit of
  `Ψ(x, x ^ (1 / u)) / x` and the delay equation of the Dickman function. The proofs here are
  not taken from it.
-/

public section

open Finset

/-- An integer `n > 1` has all its prime factors less than `k` exactly when its largest prime
factor is less than `k`. -/
@[simp]
theorem Nat.mem_smoothNumbers_iff_maxPrimeFac_lt {n k : ℕ} (hn : 1 < n) :
    n ∈ Nat.smoothNumbers k ↔ n.maxPrimeFac < k := by
  rw [Nat.mem_smoothNumbers', (Nat.isGreatest_maxPrimeFac hn).lt_iff]
  simp only [Set.mem_ofPred_eq, and_imp]

/-- For a prime `p`, the largest prime factor of `n` is `p` exactly when `p` divides `n` and all
prime factors of `n / p` are at most `p`. -/
theorem Nat.Prime.maxPrimeFac_eq_iff {p : ℕ} (hp : p.Prime) {n : ℕ} :
    n.maxPrimeFac = p ↔ p ∣ n ∧ n / p ∈ Nat.smoothNumbers (p + 1) := by
  constructor
  · intro h
    have hn : 1 < n := Nat.one_lt_maxPrimeFac_iff.1 (by rw [h]; exact hp.one_lt)
    have hdvd : p ∣ n := by
      rw [← h]
      exact Nat.maxPrimeFac_dvd
    have hsmooth : n ∈ Nat.smoothNumbers (p + 1) :=
      (Nat.mem_smoothNumbers_iff_maxPrimeFac_lt hn).2 (by omega)
    exact ⟨hdvd, Nat.mem_smoothNumbers_of_dvd hsmooth (Nat.div_dvd_of_dvd hdvd)⟩
  · rintro ⟨⟨m, rfl⟩, hm⟩
    rw [Nat.mul_div_cancel_left m hp.pos] at hm
    have hmax : m.maxPrimeFac ≤ p := by
      rcases Nat.lt_or_ge 1 m with h1 | h1
      · exact Nat.lt_add_one_iff.1 ((Nat.mem_smoothNumbers_iff_maxPrimeFac_lt h1).1 hm)
      · obtain rfl : m = 1 := by
          have := Nat.ne_zero_of_mem_smoothNumbers hm
          omega
        simpa using hp.one_le
    rw [Nat.maxPrimeFac_mul hp.ne_zero (Nat.ne_zero_of_mem_smoothNumbers hm),
      hp.maxPrimeFac_eq_self, max_eq_left hmax]

/-- For a prime `p`, an integer `n` lies in `[1, N]` and has largest prime factor `p` exactly
when `p` divides `n` and `n / p` is an integer up to `N / p` with all prime factors at most
`p`. -/
theorem Nat.Prime.mem_filter_Icc_maxPrimeFac_eq_iff {p : ℕ} (hp : p.Prime) {N n : ℕ} :
    n ∈ (Icc 1 N).filter (fun n ↦ n.maxPrimeFac = p) ↔
      p ∣ n ∧ n / p ∈ Nat.smoothNumbersUpTo (N / p) (p + 1) := by
  rw [mem_filter, mem_Icc, hp.maxPrimeFac_eq_iff, Nat.mem_smoothNumbersUpTo]
  constructor
  · rintro ⟨⟨-, hnN⟩, hdvd, hs⟩
    exact ⟨hdvd, Nat.div_le_div_right hnN, hs⟩
  · rintro ⟨⟨m, rfl⟩, hmN, hs⟩
    rw [Nat.mul_div_cancel_left m hp.pos] at hmN hs
    refine ⟨⟨Nat.mul_pos hp.pos (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hs)),
      (Nat.mul_comm p m).trans_le ((Nat.le_div_iff_mul_le hp.pos).1 hmN)⟩, dvd_mul_right p m, ?_⟩
    rwa [Nat.mul_div_cancel_left m hp.pos]

/-- For a prime `p`, multiplication by `p` as an equivalence from the positive integers up to
`N / p` with all prime factors at most `p` onto the integers in `[1, N]` whose largest prime
factor is `p`. Its inverse is division by `p`. -/
def Nat.Prime.smoothNumbersUpToEquiv {p : ℕ} (hp : p.Prime) (N : ℕ) :
    Nat.smoothNumbersUpTo (N / p) (p + 1) ≃ (Icc 1 N).filter (fun n ↦ n.maxPrimeFac = p) where
  toFun m := ⟨p * m, hp.mem_filter_Icc_maxPrimeFac_eq_iff.2 ⟨dvd_mul_right p m, by
    rw [Nat.mul_div_cancel_left _ hp.pos]
    exact m.property⟩⟩
  invFun n := ⟨n / p, (hp.mem_filter_Icc_maxPrimeFac_eq_iff.1 n.property).2⟩
  left_inv m := Subtype.ext (Nat.mul_div_cancel_left _ hp.pos)
  right_inv n := Subtype.ext
    (Nat.mul_div_cancel' (hp.mem_filter_Icc_maxPrimeFac_eq_iff.1 n.property).1)

/-- `Nat.Prime.smoothNumbersUpToEquiv` is multiplication by `p`. -/
@[simp]
theorem Nat.Prime.coe_smoothNumbersUpToEquiv_apply {p : ℕ} (hp : p.Prime) (N : ℕ)
    (m : Nat.smoothNumbersUpTo (N / p) (p + 1)) :
    (hp.smoothNumbersUpToEquiv N m : ℕ) = p * m :=
  (rfl)

/-- The inverse of `Nat.Prime.smoothNumbersUpToEquiv` is division by `p`. -/
@[simp]
theorem Nat.Prime.coe_smoothNumbersUpToEquiv_symm_apply {p : ℕ} (hp : p.Prime) (N : ℕ)
    (n : (Icc 1 N).filter (fun n ↦ n.maxPrimeFac = p)) :
    ((hp.smoothNumbersUpToEquiv N).symm n : ℕ) = n / p :=
  (rfl)

/-- For a prime `p`, the integers in `[1, N]` whose largest prime factor is `p` are as many as
the positive integers up to `N / p` with all prime factors at most `p`. -/
theorem Nat.Prime.card_filter_Icc_maxPrimeFac_eq {p : ℕ} (hp : p.Prime) (N : ℕ) :
    #{n ∈ Icc 1 N | n.maxPrimeFac = p} = #(Nat.smoothNumbersUpTo (N / p) (p + 1)) :=
  (card_eq_of_equiv (hp.smoothNumbersUpToEquiv N)).symm

/-- **Decomposition by the largest prime factor.** The integers in `[1, N]` are those with all
prime factors at most `k` together with, for each prime `k < p ≤ N`, the products `p * m` with
`m` an integer up to `N / p` with all prime factors at most `p`. -/
theorem Nat.smoothNumbersUpTo_card_add_sum (N k : ℕ) :
    #(Nat.smoothNumbersUpTo N (k + 1)) +
      ∑ p ∈ Ioc k N with p.Prime, #(Nat.smoothNumbersUpTo (N / p) (p + 1)) = N := by
  -- An integer in `[1, N]` that is not `(k + 1)`-smooth has largest prime factor in `(k, N]`.
  have hmaps : Set.MapsTo Nat.maxPrimeFac (Nat.roughNumbersUpTo N (k + 1) : Set ℕ)
      ({p ∈ Ioc k N | p.Prime} : Finset ℕ) := by
    intro n hn
    simp only [Nat.roughNumbersUpTo, mem_coe, mem_filter, mem_range] at hn
    obtain ⟨hnN, hn0, hns⟩ := hn
    have h1 : 1 < n := by
      by_contra h
      obtain rfl : n = 1 := by omega
      exact hns (Nat.mem_smoothNumbers'.2 fun q hq hq1 ↦ absurd (Nat.dvd_one.1 hq1) hq.ne_one)
    have hk : ¬n.maxPrimeFac < k + 1 := mt (Nat.mem_smoothNumbers_iff_maxPrimeFac_lt h1).2 hns
    rw [mem_coe, mem_filter, mem_Ioc]
    exact ⟨⟨by omega, Nat.maxPrimeFac_le.trans (by omega)⟩, Nat.prime_maxPrimeFac_of_one_lt h1⟩
  -- Conversely, an integer with largest prime factor `p > k` is not `(k + 1)`-smooth.
  have hfiber : ∀ p ∈ ({p ∈ Ioc k N | p.Prime} : Finset ℕ),
      #{n ∈ Nat.roughNumbersUpTo N (k + 1) | n.maxPrimeFac = p} =
        #(Nat.smoothNumbersUpTo (N / p) (p + 1)) := by
    intro p hp
    rw [mem_filter, mem_Ioc] at hp
    rw [← hp.2.card_filter_Icc_maxPrimeFac_eq N]
    congr 1
    ext n
    simp only [Nat.roughNumbersUpTo, mem_filter, mem_range, mem_Icc]
    constructor
    · rintro ⟨⟨hnN, hn0, -⟩, hmax⟩
      exact ⟨⟨by omega, by omega⟩, hmax⟩
    · rintro ⟨⟨-, hnN⟩, hmax⟩
      have h1 : 1 < n := Nat.one_lt_maxPrimeFac_iff.1 (by rw [hmax]; exact hp.2.one_lt)
      refine ⟨⟨by omega, by omega, fun hs ↦ ?_⟩, hmax⟩
      have := (Nat.mem_smoothNumbers_iff_maxPrimeFac_lt h1).1 hs
      omega
  have h := Nat.smoothNumbersUpTo_card_add_roughNumbersUpTo_card N (k + 1)
  rwa [card_eq_sum_card_fiberwise hmaps, sum_congr rfl hfiber] at h
