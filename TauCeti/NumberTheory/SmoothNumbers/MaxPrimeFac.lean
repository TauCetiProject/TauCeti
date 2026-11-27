/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Data.Nat.MaxPrimeFac
public import TauCeti.NumberTheory.SmoothNumbers.Count

/-!
# Decomposing the integers up to `x` by their largest prime factor

Every positive integer `n ≤ x` is either `y`-smooth or has a largest prime factor `p > y`, and in
the second case `n / p` is a `p`-smooth integer up to `x / p`. Conversely `p * m` has largest prime
factor `p` for every `p`-smooth `m`. Counting gives the identity

  `Ψ(x, y) + ∑_{y < p ≤ x} Ψ(x / p, p) = ⌊x⌋`,

the sum being over primes. It is the recursion behind the delay differential equation of the
Dickman function.

## Main results

* `Nat.mem_smoothNumbers_iff_maxPrimeFac_lt`: for `n > 1`, `n` is `k`-smooth in Mathlib's sense
  exactly when its largest prime factor is less than `k`.
* `Nat.Prime.card_filter_Icc_maxPrimeFac_eq`: for a prime `p`, the integers in `[1, N]` with
  largest prime factor `p` correspond to the `p`-smooth integers up to `N / p`.
* `Nat.card_smoothNumbersUpTo_add_sum`: the identity for natural cutoffs.
* `TauCeti.smoothCount_add_sum_smoothCount_div`: the identity for `Ψ`, for all real `x` and `y`.
-/

public section

open Finset

/-- An integer `n > 1` has all its prime factors less than `k` exactly when its largest prime
factor is less than `k`. -/
theorem Nat.mem_smoothNumbers_iff_maxPrimeFac_lt {n k : ℕ} (hn : 1 < n) :
    n ∈ Nat.smoothNumbers k ↔ n.maxPrimeFac < k := by
  rw [Nat.mem_smoothNumbers']
  exact ⟨fun h ↦ h _ (Nat.prime_maxPrimeFac_of_one_lt hn) Nat.maxPrimeFac_dvd,
    fun h q hq hqn ↦ (Nat.le_maxPrimeFac (by omega) hq hqn).trans_lt h⟩

/-- For a prime `p`, multiplication by `p` is a bijection from the `p`-smooth positive integers up
to `N / p` onto the integers in `[1, N]` whose largest prime factor is `p`. -/
theorem Nat.Prime.card_filter_Icc_maxPrimeFac_eq {p : ℕ} (hp : p.Prime) (N : ℕ) :
    #{n ∈ Icc 1 N | n.maxPrimeFac = p} = #(Nat.smoothNumbersUpTo (N / p) (p + 1)) := by
  symm
  refine card_nbij' (p * ·) (· / p) ?_ ?_ ?_ ?_
  · intro m hm
    obtain ⟨hmN, hm⟩ := Nat.mem_smoothNumbersUpTo.1 hm
    have hm0 := Nat.ne_zero_of_mem_smoothNumbers hm
    have hmax : m.maxPrimeFac ≤ p := by
      rcases Nat.lt_or_ge 1 m with h1 | h1
      · exact Nat.lt_add_one_iff.1 ((Nat.mem_smoothNumbers_iff_maxPrimeFac_lt h1).1 hm)
      · obtain rfl : m = 1 := by omega
        simpa using hp.one_le
    rw [mem_coe, mem_filter, mem_Icc, Nat.maxPrimeFac_mul hp.ne_zero hm0, hp.maxPrimeFac_eq_self,
      max_eq_left hmax]
    exact ⟨⟨Nat.mul_pos hp.pos (Nat.pos_of_ne_zero hm0),
      (Nat.mul_comm p m).trans_le ((Nat.le_div_iff_mul_le hp.pos).1 hmN)⟩, rfl⟩
  · intro n hn
    rw [mem_coe, mem_filter, mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, hmax⟩ := hn
    obtain ⟨m, rfl⟩ : p ∣ n := hmax ▸ Nat.maxPrimeFac_dvd
    have hm0 : m ≠ 0 := by
      rintro rfl
      omega
    simp only [mem_coe, Nat.mul_div_cancel_left m hp.pos, Nat.mem_smoothNumbersUpTo]
    refine ⟨(Nat.le_div_iff_mul_le hp.pos).2 ((Nat.mul_comm m p).trans_le hnN),
      Nat.mem_smoothNumbers'.2 fun q hq hqm ↦ Nat.lt_add_one_iff.2 ?_⟩
    exact hmax ▸ Nat.le_maxPrimeFac (Nat.mul_ne_zero hp.ne_zero hm0) hq (hqm.mul_left p)
  · intro m _
    exact Nat.mul_div_cancel_left m hp.pos
  · intro n hn
    rw [mem_coe, mem_filter] at hn
    exact Nat.mul_div_cancel' (hn.2 ▸ Nat.maxPrimeFac_dvd)

/-- **Decomposition by the largest prime factor.** The integers in `[1, N]` are the `k`-smooth
ones (all prime factors at most `k`) together with, for each prime `k < p ≤ N`, the products
`p * m` with `m` a `p`-smooth integer up to `N / p`. -/
theorem Nat.card_smoothNumbersUpTo_add_sum (N k : ℕ) :
    #(Nat.smoothNumbersUpTo N (k + 1)) +
      ∑ p ∈ Ioc k N with p.Prime, #(Nat.smoothNumbersUpTo (N / p) (p + 1)) = N := by
  have hsmooth : {n ∈ Icc 1 N | n ∈ Nat.smoothNumbers (k + 1)} =
      Nat.smoothNumbersUpTo N (k + 1) := by
    ext n
    rw [mem_filter, mem_Icc, Nat.mem_smoothNumbersUpTo]
    exact ⟨fun h ↦ ⟨h.1.2, h.2⟩, fun h ↦
      ⟨⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers h.2), h.1⟩, h.2⟩⟩
  -- A non-smooth `n` has a largest prime factor `p` with `k < p ≤ N`.
  have hmaps : Set.MapsTo Nat.maxPrimeFac
      ({n ∈ Icc 1 N | n ∉ Nat.smoothNumbers (k + 1)} : Finset ℕ)
      ({p ∈ Ioc k N | p.Prime} : Finset ℕ) := by
    intro n hn
    rw [mem_coe, mem_filter, mem_Icc, Nat.mem_smoothNumbers'] at hn
    obtain ⟨⟨hn1, hnN⟩, hns⟩ := hn
    push Not at hns
    obtain ⟨q, hq, hqn, hkq⟩ := hns
    have hn0 : n ≠ 0 := by omega
    have h1 : 1 < n := lt_of_lt_of_le hq.one_lt (Nat.le_of_dvd (by omega) hqn)
    rw [mem_coe, mem_filter, mem_Ioc]
    exact ⟨⟨lt_of_lt_of_le (Nat.lt_of_add_one_le hkq) (Nat.le_maxPrimeFac hn0 hq hqn),
      Nat.maxPrimeFac_le.trans hnN⟩, Nat.prime_maxPrimeFac_of_one_lt h1⟩
  -- If the largest prime factor of `n` exceeds `k`, then `n` is not `k`-smooth.
  have hfiber : ∀ p ∈ ({p ∈ Ioc k N | p.Prime} : Finset ℕ),
      #{n ∈ {n ∈ Icc 1 N | n ∉ Nat.smoothNumbers (k + 1)} | n.maxPrimeFac = p} =
        #(Nat.smoothNumbersUpTo (N / p) (p + 1)) := by
    intro p hp
    rw [mem_filter, mem_Ioc] at hp
    rw [← hp.2.card_filter_Icc_maxPrimeFac_eq N, filter_filter]
    refine congrArg _ (filter_congr fun n _ ↦ and_iff_right_of_imp fun hmax hs ↦ ?_)
    have h := Nat.mem_smoothNumbers'.1 hs p hp.2 (hmax ▸ Nat.maxPrimeFac_dvd)
    omega
  have hcard := card_filter_add_card_filter_not (s := Icc 1 N)
    (fun n ↦ n ∈ Nat.smoothNumbers (k + 1))
  rw [hsmooth, card_eq_sum_card_fiberwise hmaps, sum_congr rfl hfiber, Nat.card_Icc,
    Nat.add_sub_cancel] at hcard
  exact hcard

namespace TauCeti

/-- **Decomposition by the largest prime factor.** For all real `x` and `y`,
`Ψ(x, y) + ∑_{y < p ≤ x} Ψ(x / p, p) = ⌊x⌋₊`, the sum being over the primes `p` with
`⌊y⌋₊ < p ≤ ⌊x⌋₊`. -/
theorem smoothCount_add_sum_smoothCount_div (x y : ℝ) :
    smoothCount x y + ∑ p ∈ Ioc ⌊y⌋₊ ⌊x⌋₊ with p.Prime, smoothCount (x / p) p = ⌊x⌋₊ := by
  have h := Nat.card_smoothNumbersUpTo_add_sum ⌊x⌋₊ ⌊y⌋₊
  rw [smoothCount_def]
  refine (congrArg _ (sum_congr rfl fun p _ ↦ ?_)).trans h
  rw [smoothCount_def, Nat.floor_div_natCast, Nat.floor_natCast]

/-- Of the ten integers up to `10`, four are powers of `2`; the others have largest prime factor
`3` (namely `3, 6, 9`), `5` (namely `5, 10`) or `7`. -/
example :
    smoothCount 10 2 + ∑ p ∈ (Ioc 2 10 : Finset ℕ) with p.Prime, smoothCount (10 / p) p = 10 := by
  simpa using smoothCount_add_sum_smoothCount_div 10 2

end TauCeti
