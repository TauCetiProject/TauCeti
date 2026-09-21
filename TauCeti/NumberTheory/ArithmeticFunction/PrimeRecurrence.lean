/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# Sequences with a Hecke-type recurrence at the primes

A sequence `a : ℕ → R` satisfying, at every prime `p` coprime to an auxiliary `L` and every `m`
coprime to `L`, a recurrence `a_{pm} = c · a_m − d · a_{m/p}` (the last term present only when
`p ∣ m`) for some scalars `c`, `d`, vanishes at every `n ≠ 0` coprime to `L` as soon as `a₁ = 0`.
This is the combinatorial content of the vanishing of the Fourier coefficients of a Hecke
eigenform with `a₁ = 0` at the good indices, where `c` is the eigenvalue at `p` and
`d = χ(p) p^{k−1}`.

## Main results

* `TauCeti.eq_zero_of_forall_prime_mul_eq_of_one_eq_zero_of_ne_zero_of_coprime`: the vanishing
  at the indices coprime to `L`.
* `TauCeti.prime_mul_eq_of_prime_pow_recurrence_of_coprime_mul_eq`: conversely, a sequence that
  is multiplicative at coprime indices away from `L` and satisfies the recurrence **along the
  powers of a single prime `p`** satisfies it at every index coprime to `L`. Its hypotheses are
  the fixed-prime and `L`-restricted instances of conditions (2) and (3) of Diamond–Shurman's
  Proposition 5.8.5, and its conclusion is the fixed-prime instance of the recurrence the first
  lemma consumes — and, on a nebentypus space, the coefficient side of the eigen-relation
  at `p`.

## References

* [T. Miyake, *Modular forms*][miyake1989], §4.6 — the vanishing induction this lemma is the
  arithmetic core of.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.8 —
  in particular Proposition 5.8.5, whose conditions (2) and (3) are the hypotheses of the second
  lemma below.
-/

public section

namespace TauCeti

variable {R : Type*} [NonUnitalNonAssocRing R]

/-- **A sequence with a Hecke-type prime recurrence and `a₁ = 0` vanishes at the indices
coprime to `L`.** If at every prime `p` coprime to `L` there are scalars `c`, `d` with
`a_{pm} = c · a_m − d · a_{m/p}` (the last term only when `p ∣ m`) for every `m` coprime to `L`,
and `a₁ = 0`, then `a_n = 0` for every `n ≠ 0` coprime to `L`. -/
theorem eq_zero_of_forall_prime_mul_eq_of_one_eq_zero_of_ne_zero_of_coprime {a : ℕ → R} {L : ℕ}
    (ha : ∀ p : ℕ, p.Prime → Nat.Coprime p L → ∃ c d : R, ∀ m : ℕ, Nat.Coprime m L →
      a (p * m) = c * a m - if p ∣ m then d * a (m / p) else 0)
    (h1 : a 1 = 0) (n : ℕ) (hn0 : n ≠ 0) (hn : Nat.Coprime n L) : a n = 0 := by
  -- Strong induction on `n`: the recurrence at the least prime factor of `n` expresses `a n`
  -- through terms at smaller indices, which remain coprime to `L`.
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · interval_cases n
    · exact absurd rfl hn0
    · exact h1
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  obtain ⟨m, hm⟩ := Nat.minFac_dvd n
  have hpL : Nat.Coprime n.minFac L := Nat.Coprime.coprime_dvd_left (Nat.minFac_dvd n) hn
  have hmL : Nat.Coprime m L := Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ hm.symm) hn
  have hm0 : m ≠ 0 := fun h0 ↦ hn0 (by rw [hm, h0, mul_zero])
  have hmn : m < n :=
    hm ▸ (Nat.lt_mul_iff_one_lt_left (Nat.pos_of_ne_zero hm0)).mpr hp.one_lt
  obtain ⟨c, d, hcd⟩ := ha _ hp hpL
  rw [hm, hcd m hmL, ih m hmn hm0 hmL, mul_zero, zero_sub]
  split_ifs with hpm
  · rw [ih (m / n.minFac) ((Nat.div_le_self m _).trans_lt hmn)
      (Nat.div_ne_zero_iff_of_dvd hpm |>.mpr ⟨hm0, hp.ne_zero⟩)
      (Nat.Coprime.coprime_div_left hmL hpm), mul_zero, neg_zero]
  · exact neg_zero

section NonUnitalRing

variable {R : Type*} [NonUnitalRing R]

/-- **The recurrence along the powers of `p`, plus multiplicativity, gives it at every index.**
Let `a : ℕ → R` be multiplicative at coprime indices away from `L`, and suppose that along the
powers of a prime `p ∤ L` it satisfies `a_{p^{r+2}} = a_p · a_{p^{r+1}} − d · a_{p^r}`. Then it
satisfies the full Hecke recurrence `a_{pm} = a_p · a_m − d · a_{m/p}` at every `m ≠ 0` coprime
to `L`, the last term present only when `p ∣ m`.

The hypotheses are the fixed-prime and `L`-restricted instances of conditions (3) and (2) of
Diamond–Shurman's Proposition 5.8.5, whose own statements are global; the conclusion is the
**fixed-prime instance** of the recurrence hypothesis of
`eq_zero_of_forall_prime_mul_eq_of_one_eq_zero_of_ne_zero_of_coprime` above, which asks for it at
every prime coprime to `L` — and, on a nebentypus space, the coefficient side of the
`Tₚ`-eigen-relation. -/
theorem prime_mul_eq_of_prime_pow_recurrence_of_coprime_mul_eq {a : ℕ → R} {L p : ℕ} {d : R}
    (hp : p.Prime) (hpL : Nat.Coprime p L)
    (hmul : ∀ u v : ℕ, Nat.Coprime u v → Nat.Coprime u L → Nat.Coprime v L →
      a (u * v) = a u * a v)
    (hrec : ∀ r : ℕ, a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - d * a (p ^ r))
    (m : ℕ) (hm0 : m ≠ 0) (hmL : Nat.Coprime m L) :
    a (p * m) = a p * a m - if p ∣ m then d * a (m / p) else 0 := by
  -- Split off the `p`-part, `m = p ^ w * n` with `p ∤ n`. Multiplicativity then moves each of the
  -- three terms to `a (p ^ j) * a n`, leaving the power recurrence at `r = w - 1`; at `w = 0`
  -- there is no `a_{m/p}` term and the claim is multiplicativity itself.
  obtain ⟨w, n, hpn, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 p hp.ne_one
  have hpn' : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).2 hpn
  have hnL : Nat.Coprime n L := hmL.coprime_dvd_left ⟨p ^ w, mul_comm _ _⟩
  -- Multiplicativity sends every term to `a (p ^ j) * a n`.
  have hpow : ∀ j : ℕ, a (p ^ j * n) = a (p ^ j) * a n := fun j ↦
    hmul _ _ (hpn'.pow_left j) (hpL.pow_left j) hnL
  cases w with
  | zero =>
    -- `p ∤ m`, so there is no second term and the claim is multiplicativity itself.
    rw [pow_zero, one_mul]
    split_ifs
    rw [hmul p n hpn' hpL hnL, sub_zero]
  | succ w =>
    have hpm : p ∣ p ^ (w + 1) * n := (dvd_pow_self p (Nat.succ_ne_zero w)).mul_right _
    have e1 : a (p * (p ^ (w + 1) * n)) = a (p ^ (w + 2)) * a n := by
      rw [← hpow (w + 2)]; ring_nf
    have e3 : a (p ^ (w + 1) * n / p) = a (p ^ w) * a n := by
      rw [← hpow w]
      congr 1
      rw [pow_succ, mul_comm (p ^ w) p, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
    -- What is left is the power recurrence at `r = w`.
    split_ifs
    rw [e1, e3, hpow (w + 1), hrec w, sub_mul, mul_assoc, mul_assoc]

end NonUnitalRing

end TauCeti
