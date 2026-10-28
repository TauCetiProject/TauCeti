/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.Data.Nat.Digits.Defs

/-!
# Binomial coefficients prime to `p` and base-`p` digits

Let `p` be a prime. Lucas' theorem (`Choose.choose_modEq_choose_mod_mul_choose_div_nat`)
computes `n choose k` modulo `p` digit by digit. This file draws two counting consequences.

* The number of `k ≤ n` with `p ∤ n choose k` is `∏ⱼ (nⱼ + 1)`, where the `nⱼ` are the base-`p`
  digits of `n`: such `k` are exactly those whose every digit satisfies `kⱼ ≤ nⱼ`.
* Every `n choose k` with `k ≤ n` is prime to `p` exactly when `n + 1 = (a + 1) pᵐ` for some
  `a < p` and some `m`, that is, when every base-`p` digit of `n` except the leading one is
  `p - 1`.

Both are proved by peeling off the last digit, writing `n = r + p q` with `r < p`, from the
one-digit divisibility criterion `Nat.dvd_choose_add_mul_iff`.

These are the numerical inputs to the representation theory of `SL₂` in characteristic `p`: the
simple module of highest weight `n` has dimension `∏ⱼ (nⱼ + 1)`, and the binary forms of degree
`n` are simple exactly when `n + 1 = (a + 1) pᵐ`.

## Main results

* `Nat.dvd_choose_add_mul_iff`: for `r, a < p`, `p ∣ (r + p q) choose (a + p b)` exactly when
  `r < a` or `p ∣ q choose b`.
* `Nat.card_filter_not_dvd_choose`: the number of `k ≤ n` with `p ∤ n choose k` is the product of
  the base-`p` digits of `n`, each increased by one.
* `Nat.forall_not_dvd_choose_iff`: every `n choose k` with `k ≤ n` is prime to `p` exactly when
  `n + 1 = (a + 1) pᵐ` with `a < p`.

## References

* N. J. Fine, *Binomial coefficients modulo a prime*, Amer. Math. Monthly **54** (1947), 589–592.
* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Part II, Chapter 3.
-/

public section

open Finset

namespace Nat

/-- Membership in the set of `k ≤ n` with `p ∤ n choose k` only depends on the divisibility:
`n choose k = 0` is divisible by `p` for `k > n`. -/
private theorem mem_filter_range_not_dvd_choose {p n k : ℕ} :
    k ∈ {k ∈ range (n + 1) | ¬p ∣ n.choose k} ↔ ¬p ∣ n.choose k := by
  refine ⟨fun h ↦ (mem_filter.mp h).2, fun h ↦ mem_filter.mpr ⟨mem_range.mpr ?_, h⟩⟩
  by_contra! hk
  exact h (by simp [choose_eq_zero_of_lt (lt_of_succ_le hk)])

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Lucas' theorem for divisibility, one digit at a time.** For last digits `r, a < p`, the
prime `p` divides `(r + p q) choose (a + p b)` exactly when `r < a` or `p` divides
`q choose b`. -/
theorem dvd_choose_add_mul_iff {q r a b : ℕ} (hr : r < p) (ha : a < p) :
    p ∣ (r + p * q).choose (a + p * b) ↔ r < a ∨ p ∣ q.choose b := by
  have hp0 : 0 < p := hp.out.pos
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := r + p * q)
    (k := a + p * b)
  simp only [add_mul_mod_self_left, mod_eq_of_lt hr, mod_eq_of_lt ha, add_mul_div_left _ _ hp0,
    div_eq_of_lt hr, div_eq_of_lt ha, zero_add] at h
  rw [h.dvd_iff dvd_rfl, hp.out.dvd_mul]
  -- A binomial coefficient with upper index below `p` is prime to `p` unless it vanishes.
  refine or_congr_left ⟨fun hra ↦ ?_, fun hra ↦ by simp [choose_eq_zero_of_lt hra]⟩
  by_contra! har
  exact (hp.out.coprime_iff_not_dvd.mp (hp.out.coprime_choose_of_lt hr har)) hra

/-- **The count of binomial coefficients prime to `p` is multiplicative in the digits.** For a last
digit `r < p`, the number of `k ≤ r + p q` with `p ∤ (r + p q) choose k` is `r + 1` times the number
of `k ≤ q` with `p ∤ q choose k`. -/
theorem card_filter_not_dvd_choose_add_mul {q r : ℕ} (hr : r < p) :
    #{k ∈ range (r + p * q + 1) | ¬p ∣ (r + p * q).choose k} =
      (r + 1) * #{k ∈ range (q + 1) | ¬p ∣ q.choose k} := by
  have hp0 : 0 < p := hp.out.pos
  rw [← card_range (r + 1), ← card_product]
  -- Split `k` into its last digit `k % p` and the remaining digits `k / p`.
  refine card_nbij' (fun k ↦ (k % p, k / p)) (fun x ↦ x.1 + p * x.2) ?_ ?_ ?_ ?_
  · intro k hk
    rw [mem_coe, mem_filter_range_not_dvd_choose, ← mod_add_div k p,
      dvd_choose_add_mul_iff hr (mod_lt _ hp0), not_or, not_lt] at hk
    exact mem_product.mpr ⟨mem_range.mpr (Nat.lt_add_one_iff.mpr hk.1),
      mem_filter_range_not_dvd_choose.mpr hk.2⟩
  · rintro ⟨a, b⟩ hab
    simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio, mem_coe,
      mem_filter_range_not_dvd_choose] at hab
    rw [mem_coe, mem_filter_range_not_dvd_choose, dvd_choose_add_mul_iff hr (by omega), not_or,
      not_lt]
    exact ⟨Nat.lt_add_one_iff.mp hab.1, hab.2⟩
  · intro k _
    exact mod_add_div k p
  · rintro ⟨a, b⟩ hab
    simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio] at hab
    have ha : a < p := by omega
    simp [add_mul_mod_self_left, mod_eq_of_lt ha, add_mul_div_left _ _ hp0, div_eq_of_lt ha]

/-- **Fine's theorem.** The number of `k ≤ n` for which `p ∤ n choose k` is `∏ⱼ (nⱼ + 1)`, the
product over the base-`p` digits `nⱼ` of `n`. -/
theorem card_filter_not_dvd_choose (n : ℕ) :
    #{k ∈ range (n + 1) | ¬p ∣ n.choose k} = ((p.digits n).map (· + 1)).prod := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp [filter_singleton, hp.out.ne_one]
    have key := card_filter_not_dvd_choose_add_mul (q := n / p) (mod_lt n hp.out.pos)
    rw [mod_add_div] at key
    rw [key, digits_eq_cons_digits_div hp.out.one_lt hn, List.map_cons, List.prod_cons,
      ih _ (div_lt_self (pos_of_ne_zero hn) hp.out.one_lt)]

/-- The binomial coefficients `(r + p q) choose k`, `k ≤ r + p q`, with last digit `r < p`, are all
prime to `p` exactly when those of `q` are and, unless `q = 0`, the last digit is `r = p - 1`. -/
theorem forall_not_dvd_choose_add_mul_iff {q r : ℕ} (hr : r < p) :
    (∀ k ≤ r + p * q, ¬p ∣ (r + p * q).choose k) ↔
      (q = 0 ∨ r + 1 = p) ∧ ∀ k ≤ q, ¬p ∣ q.choose k := by
  have hp0 : 0 < p := hp.out.pos
  constructor
  · intro h
    refine ⟨?_, fun b hb ↦ ?_⟩
    · -- Otherwise the digit `r + 1 < p` gives a binomial coefficient divisible by `p`.
      by_contra! hq
      have hrp : r + 1 < p := lt_of_le_of_ne hr hq.2
      have hle : r + 1 ≤ r + p * q := by
        have := Nat.le_mul_of_pos_right p (pos_of_ne_zero hq.1)
        omega
      refine h (r + 1 + p * 0) (by simpa using hle) ?_
      exact (dvd_choose_add_mul_iff hr hrp).mpr (Or.inl (lt_succ_self r))
    · have := h (0 + p * b) (by have := Nat.mul_le_mul_left p hb; omega)
      rwa [dvd_choose_add_mul_iff hr hp0, not_or, and_iff_right (by omega)] at this
  · rintro ⟨hrq, h⟩ k hk
    rw [← mod_add_div k p, dvd_choose_add_mul_iff hr (mod_lt _ hp0), not_or, not_lt]
    have hkq : k / p ≤ q := by
      have : k < (q + 1) * p := by rw [add_one_mul, mul_comm q p]; omega
      exact Nat.lt_add_one_iff.mp ((Nat.div_lt_iff_lt_mul hp0).mpr this)
    refine ⟨?_, h _ hkq⟩
    rcases hrq with rfl | hrp
    · rw [mul_zero, add_zero] at hk
      exact (mod_le k p).trans hk
    · have := mod_lt k hp0
      omega

/-- **All binomial coefficients `n choose k` are prime to `p` exactly when
`n + 1 = (a + 1) pᵐ`** for some `a < p` and some `m`, that is, when every base-`p` digit of `n`
except the leading one is `p - 1`. -/
theorem forall_not_dvd_choose_iff (n : ℕ) :
    (∀ k ≤ n, ¬p ∣ n.choose k) ↔ ∃ a < p, ∃ m, n + 1 = (a + 1) * p ^ m := by
  have hp0 : 0 < p := hp.out.pos
  induction n using Nat.strongRecOn with
  | ind n ih =>
    obtain ⟨r, q, hr, rfl⟩ : ∃ r q, r < p ∧ r + p * q = n :=
      ⟨n % p, n / p, mod_lt n hp0, mod_add_div n p⟩
    rw [forall_not_dvd_choose_add_mul_iff hr]
    rcases eq_or_ne q 0 with rfl | hq
    · -- A single digit: all binomial coefficients are prime to `p`, and `r + 1 = (r + 1) p⁰`.
      exact iff_of_true ⟨Or.inl rfl, by simp [hp.out.ne_one]⟩ ⟨r, hr, 0, by simp⟩
    have hpq : p ≤ p * q := Nat.le_mul_of_pos_right p (pos_of_ne_zero hq)
    have hqlt : q < r + p * q := by nlinarith [hp.out.two_le, pos_of_ne_zero hq]
    rw [or_iff_right hq]
    constructor
    · rintro ⟨hrp, h⟩
      obtain ⟨a, ha, m, hm⟩ := (ih q hqlt).mp h
      refine ⟨a, ha, m + 1, ?_⟩
      calc r + p * q + 1 = p * (q + 1) := by rw [← hrp]; ring
        _ = (a + 1) * p ^ (m + 1) := by rw [hm]; ring
    · rintro ⟨a, ha, m, hm⟩
      rcases m with _ | m
      · -- `r + p q + 1 ≥ p + 1` cannot equal `a + 1 ≤ p`.
        rw [pow_zero, mul_one] at hm
        omega
      -- Now `p` divides `r + 1 + p q`, so the last digit is `r = p - 1`.
      have hdvd : p ∣ r + 1 := by
        have h1 : p ∣ r + 1 + p * q := ⟨(a + 1) * p ^ m, by rw [add_right_comm, hm]; ring⟩
        exact (Nat.dvd_add_left (dvd_mul_right p q)).mp h1
      have hrp : r + 1 = p := le_antisymm hr (le_of_dvd (succ_pos r) hdvd)
      refine ⟨hrp, (ih q hqlt).mpr ⟨a, ha, m, Nat.eq_of_mul_eq_mul_left hp0 ?_⟩⟩
      calc p * (q + 1) = r + p * q + 1 := by rw [← hrp]; ring
        _ = p * ((a + 1) * p ^ m) := by rw [hm]; ring

end Nat
