/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Prime.Basic

/-!
# Finite sets of primes: ordered prime factorizations and smallest prime factors

By unique factorization, a natural number `s` has at most two ordered factorizations `s = p * q`
into two primes, namely `(p, q)` and `(q, p)`. Also, the smallest prime factor of any `1 < n ≤ N`
is a prime in `[1, N]`.

## Main results

* `Nat.card_le_two_of_forall_prime_mul_eq`: a finite set of ordered pairs of primes with a fixed
  product `s` has at most two elements.
* `Nat.minFac_mem_filter_prime_Icc`: for `1 < n ≤ N`, `n.minFac` is a prime in `Finset.Icc 1 N`.
-/

public section

namespace Nat

/-- A finite set of ordered pairs `(p, q)` of primes with `p * q = s` has at most two elements: by
unique factorization it is contained in `{(p₁, p₂), (p₂, p₁)}` for any one of its elements. -/
theorem card_le_two_of_forall_prime_mul_eq {T : Finset (ℕ × ℕ)} {s : ℕ}
    (hT : ∀ x ∈ T, x.1.Prime ∧ x.2.Prime ∧ x.1 * x.2 = s) : T.card ≤ 2 := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | ⟨⟨p₁, p₂⟩, h12⟩
  · simp
  obtain ⟨hp₁, hp₂, hmul⟩ := hT _ h12
  refine (Finset.card_le_card fun ⟨p, q⟩ hpq => ?_).trans
    (Finset.card_le_two (a := (p₁, p₂)) (b := (p₂, p₁)))
  obtain ⟨hp, -, hmul'⟩ := hT _ hpq
  dsimp only at hp₁ hp₂ hmul hp hmul'
  rcases hp.dvd_mul.mp (⟨q, hmul.trans hmul'.symm⟩ : p ∣ p₁ * p₂) with h | h
  · obtain rfl := (prime_dvd_prime_iff_eq hp hp₁).mp h
    obtain rfl : q = p₂ := mul_left_cancel₀ hp.ne_zero (hmul'.trans hmul.symm)
    simp
  · obtain rfl := (prime_dvd_prime_iff_eq hp hp₂).mp h
    obtain rfl : q = p₁ :=
      mul_left_cancel₀ hp.ne_zero (hmul'.trans (hmul.symm.trans (mul_comm _ _)))
    simp

/-- For `1 < n ≤ N`, the smallest prime factor `n.minFac` is a prime in `Finset.Icc 1 N`. -/
theorem minFac_mem_filter_prime_Icc {n N : ℕ} (hn : 1 < n) (hnN : n ≤ N) :
    n.minFac ∈ (Finset.Icc 1 N).filter Nat.Prime := by
  have hp := minFac_prime hn.ne'
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hp.one_le, (minFac_le (zero_lt_one.trans hn)).trans hnN⟩, hp⟩

end Nat
