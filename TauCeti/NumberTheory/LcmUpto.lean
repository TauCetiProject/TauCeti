/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.IsPrimePow
public import Mathlib.NumberTheory.Chebyshev

/-!
# Divisibility and powersmoothness for `Nat.lcmUpto`

Mathlib's `Nat.lcmUpto n` is the least common multiple `(Finset.Icc 1 n).lcm id` of `{1, …, n}`,
with prime-power product expansion `Nat.lcmUpto_eq_prod_pow_log`. Every positive integer `m ≤ n`
divides `Nat.lcmUpto n`, and in general a natural number `d` divides `Nat.lcmUpto n` precisely
when `d` is `n`-*powersmooth*: every prime-power divisor `q` of `d` satisfies `q ≤ n`,
equivalently `d ≠ 0` and the full `p`-primary part `ordProj[p] d` is at most `n` at every prime
divisor `p` of `d`.

This condition is strictly stronger than bounding only the prime divisors of `d` by `n` (for
example, `16` has sole prime divisor `2 ≤ 10` yet does not divide `Nat.lcmUpto 10 = 2520`), and
governs when the stage-1 multiplier `B₁.lcmUpto` is a multiple of a point or group order in
smooth-order factorization methods such as Pollard's `p - 1` method and Lenstra's elliptic-curve
method.

## Main results

* `Nat.lcmUpto_zero`, `Nat.lcmUpto_one`, `Nat.lcmUpto_two`: small values of `Nat.lcmUpto`.
* `Nat.dvd_lcmUpto`: every positive integer `m ≤ n` divides `Nat.lcmUpto n`.
* `Nat.Prime.pow_dvd_lcmUpto_iff`, `Nat.Prime.dvd_lcmUpto_iff`, `IsPrimePow.dvd_lcmUpto_iff`:
  a prime power divides `Nat.lcmUpto n` if and only if it is at most `n`.
* `Nat.dvd_lcmUpto_iff`, `Nat.dvd_lcmUpto_iff_ordProj_le`: `n`-powersmoothness characterizations
  of `d ∣ Nat.lcmUpto n`.

## References

* H. W. Lenstra Jr., *Factoring integers with elliptic curves*, Ann. of Math. 126 (1987),
  649–673, §2.
* P. Zimmermann, *20 years of ECM*, ANTS VII, LNCS 4076 (2006), 525–542, §1.1.
-/

public section

namespace Nat

/-! ### Small values and basic divisibility -/

/-- `lcmUpto 0` is the empty least common multiple `1`. -/
@[simp]
theorem lcmUpto_zero : lcmUpto 0 = 1 := rfl

/-- `lcmUpto 1` equals `1`. -/
@[simp]
theorem lcmUpto_one : lcmUpto 1 = 1 := by decide

/-- `lcmUpto 2` equals `2`. -/
@[simp]
theorem lcmUpto_two : lcmUpto 2 = 2 := by decide

/-- Every positive integer at most `n` divides `lcmUpto n`. -/
theorem dvd_lcmUpto {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) : m ∣ lcmUpto n :=
  Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hm, hmn⟩)

end Nat

/-! ### Prime-power divisibility and powersmoothness -/

/-- A positive power `p ^ k` of a prime `p` divides `Nat.lcmUpto n` if and only if `p ^ k ≤ n`. -/
theorem Nat.Prime.pow_dvd_lcmUpto_iff {p : ℕ} (hp : p.Prime) {k n : ℕ} (hk : k ≠ 0) :
    p ^ k ∣ Nat.lcmUpto n ↔ p ^ k ≤ n := by
  refine ⟨fun h ↦ ?_, fun h ↦ Nat.dvd_lcmUpto (pow_pos hp.pos k) h⟩
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.lcmUpto_zero, Nat.dvd_one] at h
    exact absurd h (Nat.one_lt_pow hk hp.one_lt).ne'
  · rw [hp.pow_dvd_iff_le_factorization (Nat.lcmUpto_ne_zero n),
      Nat.factorization_lcmUpto n hp] at h
    exact Nat.pow_le_of_le_log hn h

/-- A prime `p` divides `Nat.lcmUpto n` if and only if `p ≤ n`. -/
theorem Nat.Prime.dvd_lcmUpto_iff {p n : ℕ} (hp : p.Prime) :
    p ∣ Nat.lcmUpto n ↔ p ≤ n := by
  simpa using hp.pow_dvd_lcmUpto_iff one_ne_zero

/-- A prime power `q` divides `Nat.lcmUpto n` if and only if `q ≤ n`. -/
theorem IsPrimePow.dvd_lcmUpto_iff {q n : ℕ} (hq : IsPrimePow q) :
    q ∣ Nat.lcmUpto n ↔ q ≤ n := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).mp hq
  exact hp.pow_dvd_lcmUpto_iff hk.ne'

namespace Nat

/-- **Powersmoothness criterion for `Nat.lcmUpto`**: a natural number `d` divides `lcmUpto n` if
and only if every prime-power divisor of `d` is at most `n`. Nonzeroness of `d` is automatic on the
right-hand side because arbitrarily large primes divide `0`. Compare
`Nat.dvd_lcmUpto_iff_ordProj_le`. -/
theorem dvd_lcmUpto_iff {d n : ℕ} :
    d ∣ lcmUpto n ↔ ∀ q, IsPrimePow q → q ∣ d → q ≤ n := by
  refine ⟨fun h q hq hqd ↦ hq.dvd_lcmUpto_iff.mp (hqd.trans h), fun h ↦ ?_⟩
  rw [dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpkd
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · exact (hp.pow_dvd_lcmUpto_iff hk).mpr (h (p ^ k) (hp.prime.isPrimePow.pow hk) hpkd)

/-- **Maximal prime-power criterion for `Nat.lcmUpto`**: `d` divides `lcmUpto n` if and only if
`d ≠ 0` and at every prime divisor `p` of `d`, the full `p`-primary part `ordProj[p] d` is at most
`n`. Unlike `Nat.dvd_lcmUpto_iff`, `d ≠ 0` is required here because `(0 : ℕ).factorization`
vanishes. -/
theorem dvd_lcmUpto_iff_ordProj_le {d n : ℕ} :
    d ∣ lcmUpto n ↔ d ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ d → ordProj[p] d ≤ n := by
  refine ⟨fun h ↦ ?_, fun ⟨hd, h⟩ ↦ ?_⟩
  · have hd : d ≠ 0 := ne_zero_of_dvd_ne_zero (lcmUpto_ne_zero n) h
    refine ⟨hd, fun p hp hpd ↦ ?_⟩
    have hk : d.factorization p ≠ 0 :=
      Nat.ne_of_gt ((hp.dvd_iff_one_le_factorization hd).mp hpd)
    exact dvd_lcmUpto_iff.mp h (ordProj[p] d) (hp.prime.isPrimePow.pow hk) (ordProj_dvd d p)
  · rw [dvd_lcmUpto_iff]
    intro q hq hqd
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).mp hq
    have hpd : p ∣ d := (dvd_pow_self p hk.ne').trans hqd
    have hkle : k ≤ d.factorization p := (hp.pow_dvd_iff_le_factorization hd).mp hqd
    exact (Nat.pow_le_pow_right hp.pos hkle).trans (h p hp hpd)

end Nat
