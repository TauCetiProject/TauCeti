/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.IsPrimePow
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Data.Nat.Log

/-!
# Divisibility and powersmoothness for `Nat.lcmUpto`

Mathlib's `Nat.lcmUpto n` is the least common multiple `(Finset.Icc 1 n).lcm id` of `{1, …, n}`,
with prime-power product expansion `Nat.lcmUpto_eq_prod_pow_log`. A natural number `d` divides
`Nat.lcmUpto n` precisely when `d` is `n`-*powersmooth*: every prime-power divisor `q` of `d`
satisfies `q ≤ n`, equivalently `d ≠ 0` and `p ^ d.factorization p ≤ n` at every prime divisor `p`
of `d`.

This condition is strictly stronger than `(n + 1)`-smoothness (`d ∈ Nat.smoothNumbers (n + 1)`),
which bounds only the primes dividing `d` and not their multiplicities. Every divisor of
`Nat.lcmUpto n` lies in `Nat.smoothNumbers (n + 1)`, and the two conditions coincide on squarefree
integers (where both agree with divisibility of `primorial n`), whereas higher prime powers such as
`16` at bound `10` are `11`-smooth without dividing `Nat.lcmUpto 10 = 2520`.

The step behavior of `Nat.lcmUpto` reflects its prime-power factors: `Nat.lcmUpto (n + 1)` equals
`Nat.lcmUpto n` when `n + 1` is not a prime power, and jumps by `(n + 1).minFac` when `n + 1` is a
prime power. In any monoid, raising to `n.lcmUpto` (or scalar-multiplying by `n.lcmUpto` in an
additive monoid) annihilates `x` if and only if every prime-power divisor of `orderOf x` is at
most `n`; this is the stage-1 multiplier mechanism in smooth-order factorization methods such as
Pollard's `p - 1` method and Lenstra's elliptic-curve method.

## Main results

* `Nat.lcmUpto_zero`, `Nat.lcmUpto_one`, `Nat.lcmUpto_two`, `Nat.lcmUpto_eq_one_iff`,
  `Nat.one_lt_lcmUpto_iff`: small values and comparison with `1`.
* `Nat.dvd_lcmUpto`, `Nat.lcmUpto_mono`, `Nat.self_le_lcmUpto`: basic divisibility and
  monotonicity.
* `Nat.Prime.pow_dvd_lcmUpto_iff`, `Nat.Prime.dvd_lcmUpto_iff`, `IsPrimePow.dvd_lcmUpto_iff`:
  a prime power divides `Nat.lcmUpto n` if and only if it is at most `n`.
* `Nat.dvd_lcmUpto_iff`, `Nat.dvd_lcmUpto_iff_pow_factorization_le`: `n`-powersmoothness
  characterizations of `d ∣ Nat.lcmUpto n`.
* `Nat.lcmUpto_succ_of_not_isPrimePow`, `Nat.Prime.lcmUpto_pow`,
  `IsPrimePow.lcmUpto_eq_minFac_mul`: step recurrence at non-prime-powers and prime powers.
* `Nat.lcmUpto_mem_smoothNumbers_succ`, `Nat.mem_smoothNumbers_succ_of_dvd_lcmUpto`,
  `Squarefree.dvd_lcmUpto_iff_mem_smoothNumbers_succ`: comparison with `Nat.smoothNumbers` and
  `primorial`.
* `TauCeti.pow_lcmUpto_eq_one_iff`, `TauCeti.lcmUpto_nsmul_eq_zero_iff`,
  `TauCeti.pow_lcmUpto_eq_one_of_isPrimePow_dvd_card_le`,
  `TauCeti.lcmUpto_nsmul_eq_zero_of_isPrimePow_dvd_card_le`: annihilation of monoid elements and
  groups of powersmooth `Nat.card` by `Nat.lcmUpto`.

## References

* H. W. Lenstra Jr., *Factoring integers with elliptic curves*, Ann. of Math. 126 (1987),
  649–673, §2.
* P. Zimmermann, *20 years of ECM*, ANTS VII, LNCS 4076 (2006), 525–542, §1.1.
-/

public section

namespace Nat

/-! ### Small values, monotonicity, and basic divisibility -/

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

/-- A positive integer `n` divides `lcmUpto n`. -/
theorem dvd_lcmUpto_self {n : ℕ} (hn : 0 < n) : n ∣ lcmUpto n :=
  dvd_lcmUpto hn le_rfl

/-- `lcmUpto` is monotone with respect to `≤`. -/
@[mono, gcongr]
theorem lcmUpto_mono {m n : ℕ} (h : m ≤ n) : lcmUpto m ≤ lcmUpto n :=
  le_of_dvd (lcmUpto_pos n) (lcmUpto_dvd_lcmUpto h)

/-- `Monotone` bundled form of `Nat.lcmUpto_mono`. -/
theorem lcmUpto_monotone : Monotone lcmUpto :=
  fun _ _ ↦ lcmUpto_mono

/-- Every natural number is at most `lcmUpto n`. -/
theorem self_le_lcmUpto (n : ℕ) : n ≤ lcmUpto n := by
  rcases eq_zero_or_pos n with rfl | hn
  · simp
  · exact le_of_dvd (lcmUpto_pos n) (dvd_lcmUpto_self hn)

/-- `lcmUpto n` exceeds `1` if and only if `n` exceeds `1`. -/
@[simp]
theorem one_lt_lcmUpto_iff {n : ℕ} : 1 < lcmUpto n ↔ 1 < n := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.trans_le (self_le_lcmUpto n)⟩
  by_contra! hn
  interval_cases n <;> simp_all

/-- `lcmUpto n` equals `1` if and only if `n ≤ 1`. -/
@[simp]
theorem lcmUpto_eq_one_iff {n : ℕ} : lcmUpto n = 1 ↔ n ≤ 1 := by
  rw [← not_iff_not, ← ne_eq, ← not_lt, ← one_lt_lcmUpto_iff]
  have := lcmUpto_pos n
  omega

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
right-hand side because arbitrarily large primes divide `0`. -/
theorem dvd_lcmUpto_iff {d n : ℕ} :
    d ∣ lcmUpto n ↔ ∀ q, IsPrimePow q → q ∣ d → q ≤ n := by
  refine ⟨fun h q hq hqd ↦ hq.dvd_lcmUpto_iff.mp (hqd.trans h), fun h ↦ ?_⟩
  have hd : d ≠ 0 := by
    rintro rfl
    obtain ⟨p, hnp, hp⟩ := exists_infinite_primes (n + 1)
    exact absurd (h p hp.prime.isPrimePow (dvd_zero p)) (by omega)
  rw [← factorization_prime_le_iff_dvd hd (lcmUpto_ne_zero n)]
  intro p hp
  rcases eq_or_ne (d.factorization p) 0 with hk | hk
  · simp [hk]
  · have hle : p ^ d.factorization p ≤ n :=
      h (p ^ d.factorization p) (hp.prime.isPrimePow.pow hk) (ordProj_dvd d p)
    exact (hp.pow_dvd_iff_le_factorization (lcmUpto_ne_zero n)).mp
      ((hp.pow_dvd_lcmUpto_iff hk).mpr hle)

/-- **Maximal prime-power criterion for `Nat.lcmUpto`**: `d` divides `lcmUpto n` if and only if
`d ≠ 0` and at every prime divisor `p` of `d`, the full `p`-primary part `p ^ d.factorization p` is
at most `n`. Unlike `Nat.dvd_lcmUpto_iff`, `d ≠ 0` is required here because `(0 : ℕ).factorization`
vanishes. -/
theorem dvd_lcmUpto_iff_pow_factorization_le {d n : ℕ} :
    d ∣ lcmUpto n ↔ d ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ d → p ^ d.factorization p ≤ n := by
  rw [dvd_lcmUpto_iff]
  refine ⟨fun h ↦ ?_, fun ⟨hd, h⟩ q hq hqd ↦ ?_⟩
  · have hd : d ≠ 0 := by
      rintro rfl
      obtain ⟨p, hnp, hp⟩ := exists_infinite_primes (n + 1)
      exact absurd (h p hp.prime.isPrimePow (dvd_zero p)) (by omega)
    refine ⟨hd, fun p hp hpd ↦ ?_⟩
    have hle := (hp.dvd_iff_one_le_factorization hd).mp hpd
    have hk : d.factorization p ≠ 0 := by omega
    exact h (p ^ d.factorization p) (hp.prime.isPrimePow.pow hk) (ordProj_dvd d p)
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).mp hq
    have hpd : p ∣ d := (dvd_pow_self p hk.ne').trans hqd
    have hkle : k ≤ d.factorization p := (hp.pow_dvd_iff_le_factorization hd).mp hqd
    exact (Nat.pow_le_pow_right hp.pos hkle).trans (h p hp hpd)

/-! ### Step recurrence -/

/-- When `n + 1` is not a prime power, `lcmUpto (n + 1) = lcmUpto n`. -/
theorem lcmUpto_succ_of_not_isPrimePow {n : ℕ} (hn : ¬ IsPrimePow (n + 1)) :
    lcmUpto (n + 1) = lcmUpto n := by
  refine dvd_antisymm ?_ (lcmUpto_dvd_lcmUpto n.le_succ)
  rw [dvd_lcmUpto_iff]
  intro q hq hqd
  have hle : q ≤ n + 1 := hq.dvd_lcmUpto_iff.mp hqd
  have hne : q ≠ n + 1 := fun h ↦ hn (h ▸ hq)
  omega

end Nat

/-- At a positive prime power `p ^ k`, `Nat.lcmUpto (p ^ k)` jumps by a factor of `p` over
`Nat.lcmUpto (p ^ k - 1)`. -/
theorem Nat.Prime.lcmUpto_pow {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k ≠ 0) :
    Nat.lcmUpto (p ^ k) = p * Nat.lcmUpto (p ^ k - 1) := by
  refine Nat.eq_of_factorization_eq (Nat.lcmUpto_ne_zero _)
    (mul_ne_zero hp.ne_zero (Nat.lcmUpto_ne_zero _)) fun q ↦ ?_
  by_cases hq : q.Prime
  · rw [Nat.factorization_lcmUpto _ hq,
      Nat.factorization_mul hp.ne_zero (Nat.lcmUpto_ne_zero _), Finsupp.add_apply,
      Nat.factorization_lcmUpto _ hq]
    rcases eq_or_ne p q with rfl | hpq
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      rw [hp.factorization_self, Nat.log_pow hp.one_lt]
      have hlog : Nat.log p (p ^ (m + 1) - 1) = m := by
        refine Nat.log_eq_of_pow_le_of_lt_pow ?_ (Nat.sub_lt (pow_pos hp.pos _) Nat.one_pos)
        have hpm : 1 ≤ p ^ m := Nat.one_le_pow m p hp.pos
        have hp2 : 2 * p ^ m ≤ p ^ (m + 1) := by
          rw [pow_succ']
          exact Nat.mul_le_mul_right _ hp.two_le
        omega
      rw [hlog]
      omega
    · have hfac : p.factorization q = 0 := by
        simp [hp.factorization, hpq]
      rw [hfac, zero_add]
      refine le_antisymm ?_ (Nat.log_mono_right (Nat.sub_le _ 1))
      rcases eq_or_ne (Nat.log q (p ^ k)) 0 with hr | hr
      · simp [hr]
      · have hle : q ^ Nat.log q (p ^ k) ≤ p ^ k :=
          Nat.pow_log_le_self q (pow_ne_zero k hp.ne_zero)
        have hne : q ^ Nat.log q (p ^ k) ≠ p ^ k := by
          intro heq
          have hqp' : q ∣ p := hq.dvd_of_dvd_pow (heq ▸ dvd_pow_self q hr)
          exact hpq.symm ((Nat.prime_dvd_prime_iff_eq hq hp).mp hqp')
        exact Nat.le_log_of_pow_le hq.one_lt (by omega)
  · simp [Nat.factorization_eq_zero_of_not_prime _ hq]

/-- When `n + 1` is a prime power, `Nat.lcmUpto (n + 1) = (n + 1).minFac * Nat.lcmUpto n`. -/
theorem IsPrimePow.lcmUpto_eq_minFac_mul {n : ℕ} (hn : IsPrimePow (n + 1)) :
    Nat.lcmUpto (n + 1) = (n + 1).minFac * Nat.lcmUpto n := by
  obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff (n + 1)).mp hn
  have hmin : (n + 1).minFac = p := by
    have hmp : (p ^ k).minFac.Prime := Nat.minFac_prime (hpk ▸ hn.ne_one)
    rw [← hpk]
    exact (Nat.prime_dvd_prime_iff_eq hmp hp).mp (hmp.dvd_of_dvd_pow (Nat.minFac_dvd (p ^ k)))
  rw [hmin, ← hpk, hp.lcmUpto_pow hk.ne', hpk, Nat.add_sub_cancel]

/-! ### Comparison with smooth numbers and primorials -/

namespace Nat

/-- `lcmUpto n` is `(n + 1)`-smooth: all of its prime factors are at most `n`. -/
theorem lcmUpto_mem_smoothNumbers_succ (n : ℕ) : lcmUpto n ∈ smoothNumbers (n + 1) := by
  rw [mem_smoothNumbers_iff_primeFactors_subset, primeFactors_lcmUpto]
  exact ⟨lcmUpto_ne_zero n, le_rfl⟩

/-- Every divisor of `lcmUpto n` is `(n + 1)`-smooth. The converse fails for non-squarefree
integers whose prime-power factors exceed `n`. -/
theorem mem_smoothNumbers_succ_of_dvd_lcmUpto {d n : ℕ} (h : d ∣ lcmUpto n) :
    d ∈ smoothNumbers (n + 1) :=
  mem_smoothNumbers_of_dvd (lcmUpto_mem_smoothNumbers_succ n) h

end Nat

/-- A squarefree natural number divides `primorial n` if and only if it is `(n + 1)`-smooth. -/
theorem Squarefree.dvd_primorial_iff {d n : ℕ} (hd : Squarefree d) :
    d ∣ primorial n ↔ d ∈ Nat.smoothNumbers (n + 1) := by
  refine ⟨fun h ↦ Nat.mem_smoothNumbers_succ_of_dvd_lcmUpto
      (h.trans (Nat.primorial_dvd_lcmUpto n)), fun h ↦ ?_⟩
  rw [← Nat.prod_primeFactors_of_squarefree hd, primorial_eq_prod_primesLE]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Nat.primeFactors_subset_of_mem_smoothNumbers h)

/-- For squarefree `d`, `n`-powersmoothness (`d ∣ Nat.lcmUpto n`) is equivalent to
`(n + 1)`-smoothness (`d ∈ Nat.smoothNumbers (n + 1)`). -/
theorem Squarefree.dvd_lcmUpto_iff_mem_smoothNumbers_succ {d n : ℕ} (hd : Squarefree d) :
    d ∣ Nat.lcmUpto n ↔ d ∈ Nat.smoothNumbers (n + 1) :=
  ⟨Nat.mem_smoothNumbers_succ_of_dvd_lcmUpto,
    fun h ↦ (hd.dvd_primorial_iff.mpr h).trans (Nat.primorial_dvd_lcmUpto n)⟩

/-- A squarefree natural number divides `Nat.lcmUpto n` if and only if it divides `primorial n`. -/
theorem Squarefree.dvd_lcmUpto_iff_dvd_primorial {d n : ℕ} (hd : Squarefree d) :
    d ∣ Nat.lcmUpto n ↔ d ∣ primorial n :=
  hd.dvd_lcmUpto_iff_mem_smoothNumbers_succ.trans hd.dvd_primorial_iff.symm

/-! ### Annihilation of elements of finite order -/

namespace TauCeti

/-- Raising an element `x` of a monoid to `n.lcmUpto` gives `1` if and only if every prime-power
divisor of `orderOf x` is at most `n`. Elements of infinite order have `orderOf x = 0`, making both
sides false because arbitrarily large primes divide `0`. -/
@[to_additive lcmUpto_nsmul_eq_zero_iff
/-- Scalar-multiplying an element `x` of an additive monoid by `n.lcmUpto` gives `0` if and only if
every prime-power divisor of `addOrderOf x` is at most `n`. Elements of infinite additive order
have `addOrderOf x = 0`, making both sides false because arbitrarily large primes divide `0`. -/]
theorem pow_lcmUpto_eq_one_iff {G : Type*} [Monoid G] (x : G) (n : ℕ) :
    x ^ n.lcmUpto = 1 ↔ ∀ q, IsPrimePow q → q ∣ orderOf x → q ≤ n := by
  rw [← orderOf_dvd_iff_pow_eq_one, Nat.dvd_lcmUpto_iff]

/-- If every prime-power divisor of `Nat.card G` is at most `n`, then `n.lcmUpto` annihilates every
element of the group `G`. -/
@[to_additive lcmUpto_nsmul_eq_zero_of_isPrimePow_dvd_card_le
/-- If every prime-power divisor of `Nat.card G` is at most `n`, then `n.lcmUpto` annihilates every
element of the additive group `G`. -/]
theorem pow_lcmUpto_eq_one_of_isPrimePow_dvd_card_le {G : Type*} [Group G] (x : G) {n : ℕ}
    (hG : ∀ q, IsPrimePow q → q ∣ Nat.card G → q ≤ n) :
    x ^ n.lcmUpto = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp
    ((orderOf_dvd_natCard x).trans (Nat.dvd_lcmUpto_iff.mpr hG))

end TauCeti
