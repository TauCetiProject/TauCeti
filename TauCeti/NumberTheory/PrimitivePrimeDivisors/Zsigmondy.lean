/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.PrimitivePrimeDivisors.Order
public import TauCeti.RingTheory.Polynomial.Cyclotomic.Homogeneous
import TauCeti.NumberTheory.PrimitivePrimeDivisors.Cyclotomic
import TauCeti.NumberTheory.PrimitivePrimeDivisors.Estimates
import TauCeti.NumberTheory.PrimitivePrimeDivisors.SmallExponents
import TauCeti.RingTheory.Polynomial.Cyclotomic.Eval

/-!
# The Bang–Zsigmondy theorem and its multiplicative-order corollaries

For coprime natural numbers `a > b > 0` and `n ≥ 2`, a primitive prime divisor of `a ^ n - b ^ n`
is a prime dividing `a ^ n - b ^ n` and none of the numbers `a ^ k - b ^ k` for `0 < k < n`. The
Bang–Zsigmondy theorem asserts that such a prime exists except in two cases:

* `n = 2` and `a + b` is a power of two;
* `(a, b, n) = (2, 1, 6)`, where `2 ^ 6 - 1 = 63 = 3 ^ 2 * 7` with `3 ∣ 2 ^ 2 - 1` and
  `7 ∣ 2 ^ 3 - 1`.

At `n = 2` the theorem reduces to the existence of an odd prime factor of `a + b`. For `n ≥ 3`, if
`a ^ n - b ^ n` had no primitive prime divisor, then `Φ_n(a, b)` (`TauCeti.homogeneousCyclotomic`)
would equal `1` or the largest prime factor `p` of `n`. The size estimates rule out both values:
`Φ_n(a, b) > 1` for every `n ≥ 2`, while writing `n = p ^ (e + 1) * m` with `p ∤ m` gives
`m ∣ p - 1` and splits `Φ_n(a, b) > p` into `e ≥ 1` (where `a ^ p ^ e - b ^ p ^ e ≥ 2`),
`(e, m) = (0, 1)` (the geometric sum `Φ_p(a, b) > p`), and `e = 0`, `m ≥ 2` (where
`Φ_{p m}(a, b) > ((a ^ p - b ^ p) / (a + b)) ^ φ(m) > p` except at `(a, b, p) = (2, 1, 3)`, which
forces `m = 2` and `n = 6`).

Conversely, a primitive prime divisor `q` of the reduced difference of powers exceeds `n` and
divides `Φ_n`, so for arbitrary positive natural bases `b < a` (without coprimality) and `n ≥ 2`,
`n < Φ_n(a, b)` fails only at `(a, b, n) = (2, 1, 6)`, and for a prime `p ∣ n ≠ 0`,
`p < Φ_n(a, b)` fails only at `(a, b, n, p) = (2, 1, 6, 3)`.

Translating primitivity into the multiplicative order of `a / b` in `ZMod p` yields primes at which
`a / b` (or `a` at `b = 1`, and in particular `2` for `n ≠ 1, 6` or any `a ≥ 3` for `n ≥ 3`) has
prescribed order `n`, and applying the theorem at exponent `2 * n` yields primes dividing
`a ^ n + b ^ n` and none of `a ^ k - b ^ k` for `0 < k < 2 * n`.

## Main results

* `TauCeti.exists_prime_dvd_pow_sub_pow`, `TauCeti.exists_prime_dvd_pow_sub_pow_iff`: the
  Bang–Zsigmondy theorem and exact characterization for `a ^ n - b ^ n`.
* `TauCeti.natCast_lt_homogeneousCyclotomic_iff`,
  `Nat.Prime.natCast_lt_homogeneousCyclotomic_iff`: for `0 < b < a`, `n < Φ_n(a, b)` (`n ≥ 2`) and
  `p < Φ_n(a, b)` (`p ∣ n ≠ 0`), with the sole exceptions `(2, 1, 6)` and `(2, 1, 6, 3)`.
* `TauCeti.exists_prime_orderOf_div_eq`, `TauCeti.exists_prime_orderOf_div_eq_iff`: existence and
  characterization of a prime `p ∤ a * b` with `orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = n`.
* `TauCeti.exists_prime_orderOf_eq_iff`, `TauCeti.exists_prime_orderOf_eq`,
  `TauCeti.exists_prime_orderOf_two_eq_iff`, `TauCeti.exists_prime_orderOf_two_eq`: primes at which
  `a : ZMod p` or `2 : ZMod p` has multiplicative order `n`.
* `TauCeti.exists_prime_dvd_pow_add_pow`, `TauCeti.exists_prime_dvd_pow_add_pow_iff`: existence and
  characterization of a prime dividing `a ^ n + b ^ n` and no `a ^ k - b ^ k` with `0 < k < 2 * n`.

## References

* [K. Zsigmondy, *Zur Theorie der Potenzreste*, Monatsh. Math. Phys. 3 (1892), 265–284], p. 283.
* [G. D. Birkhoff and H. S. Vandiver, *On the integral divisors of `a ^ n - b ^ n`*, Ann. of Math.
  (2) 5 (1904), 173–180], Theorem V, pp. 178–179.
* [M. Roitman, *On Zsigmondy primes*, Proc. Amer. Math. Soc. 125 (1997), 1913–1919], Lemma 1 and
  Theorem 3, pp. 1913–1915.
* [Ö. Avcı, *Large Zsigmondy primes*, arXiv:2011.06136v2 (2023)], p. 1.
-/

public section

namespace TauCeti

/-- **The Bang–Zsigmondy theorem.** For coprime natural numbers `a > b > 0` and `n ≥ 2`, there is a
prime dividing `a ^ n - b ^ n` and none of `a ^ k - b ^ k` for `0 < k < n`, unless `n = 2` and
`a + b` is a power of two, or `(a, b, n) = (2, 1, 6)`. All standing hypotheses are sharp:
`(a, b, n) = (1, 0, 3)`, `(1, 1, 3)`, `(4, 2, 6)` and `(2, 1, 1)` have no primitive prime
divisor. -/
theorem exists_prime_dvd_pow_sub_pow {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b) (hn : 2 ≤ n)
    (h₂ : n = 2 → ¬∃ k : ℕ, a + b = 2 ^ k)
    (h₆ : n = 6 → a ≠ 2 ∨ b ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ a ^ n - b ^ n ∧
      ∀ k : ℕ, 0 < k → k < n → ¬p ∣ a ^ k - b ^ k := by
  rcases hn.eq_or_lt with rfl | hn3
  · exact (exists_prime_dvd_sq_sub_sq_iff hba.le hab).2 (h₂ rfl)
  by_contra hnot
  have hbZ : (0 : ℤ) < b := by positivity
  have hbaZ : (b : ℤ) < a := by exact_mod_cast hba
  rcases hab.homogeneousCyclotomic_eq_one_or_eq_prime_of_not_exists_prime_dvd_pow_sub_pow hba
      (by omega) hnot with h1 | ⟨p, hp, hpn, -, hΦ⟩
  · exact (Int.one_lt_homogeneousCyclotomic hn hbZ hbaZ).ne' h1
  -- Write `n = p ^ (e + 1) * m` with `p ∤ m`; since `p ∣ Φ_n(a, b)`, `m` divides `p - 1`.
  have hn0 : n ≠ 0 := by omega
  have hpΦ : (p : ℤ) ∣ homogeneousCyclotomic n (a : ℤ) b := dvd_of_eq hΦ.symm
  have hprod := hab.not_dvd_mul_of_dvd_homogeneousCyclotomic hp hpΦ
  have hb' : ¬(p : ℤ) ∣ (b : ℤ) := fun h =>
    hprod (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.1 h) a)
  have hm_dvd : ordCompl[p] n ∣ p - 1 :=
    hp.ordCompl_dvd_sub_one_of_dvd_homogeneousCyclotomic hb' hpΦ
  set m := ordCompl[p] n
  have hm_pos : 0 < m := Nat.ordCompl_pos p hn0
  have hpm : ¬p ∣ m := Nat.not_dvd_ordCompl hp hn0
  have hfac_pos : 0 < n.factorization p := hp.factorization_pos_of_dvd hn0 hpn
  set e := n.factorization p - 1
  have he_succ : e + 1 = n.factorization p := Nat.sub_add_cancel hfac_pos
  have hn_eq : p ^ (e + 1) * m = n := by
    rw [he_succ]
    exact Nat.ordProj_mul_ordCompl_eq_self n p
  -- Each shape of `(e, m)` forces `p < Φ_n(a, b)`, contradicting `Φ_n(a, b) = p`.
  suffices hlt : (p : ℤ) < homogeneousCyclotomic n (a : ℤ) b from hlt.ne' hΦ
  rw [← hn_eq]
  rcases eq_or_ne e 0 with he0 | he
  · rw [he0, zero_add, pow_one] at hn_eq ⊢
    rcases eq_or_ne m 1 with hm1 | hm1
    · rw [hm1, mul_one]
      have ha1 : (1 : ℤ) < a := by omega
      have hb1 : (1 : ℤ) ≤ b := by omega
      exact natCast_lt_homogeneousCyclotomic_prime hp ha1 hb1
    · -- Here `m ≥ 2` divides `p - 1`, so `p ≥ 3` and `(a, b, p) ≠ (2, 1, 3)` since `n ≠ 6`.
      have hm2 : 2 ≤ m := by omega
      have hmp : m ≤ p - 1 := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) hm_dvd
      have hp3 : 3 ≤ p := by omega
      have hex3 : ¬(a = 2 ∧ b = 1 ∧ p = 3) := by
        rintro ⟨rfl, rfl, rfl⟩
        rcases h₆ (by omega) with ha | hb0 <;> exact absurd rfl ‹_›
      have hreal : (p : ℝ) < homogeneousCyclotomic (p * m) (a : ℝ) b :=
        (lt_pow_sub_pow_div_add_pow hb hba hp3 hex3 (Nat.totient_pos.2 hm_pos)).trans
          (pow_sub_pow_div_add_pow_totient_lt_homogeneousCyclotomic hp hpm
            (by positivity) (by exact_mod_cast hba))
      rw [← Int.cast_lt (R := ℝ)]
      simpa using hreal
  · exact Int.natCast_prime_lt_homogeneousCyclotomic_prime_pow_mul hp he hm_pos.ne' hbZ hbaZ

/-- **Exact characterization of primitive prime divisors.** For coprime natural numbers
`a > b > 0` and `n ≥ 2`, `a ^ n - b ^ n` has a primitive prime divisor if and only if neither
`n = 2` with `a + b` a power of two nor `(a, b, n) = (2, 1, 6)` holds. -/
theorem exists_prime_dvd_pow_sub_pow_iff {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b) (hn : 2 ≤ n) :
    (∃ p : ℕ, p.Prime ∧ p ∣ a ^ n - b ^ n ∧
      ∀ k : ℕ, 0 < k → k < n → ¬p ∣ a ^ k - b ^ k) ↔
      ¬(n = 2 ∧ ∃ k : ℕ, a + b = 2 ^ k) ∧
      ¬(a = 2 ∧ b = 1 ∧ n = 6) := by
  constructor
  · rintro ⟨p, hp, hdvd, hprim⟩
    refine ⟨?_, ?_⟩
    · rintro ⟨rfl, k, hk⟩
      exact hprim 1 Nat.one_pos Nat.one_lt_two
        (by simpa using hp.dvd_sub_of_dvd_sq_sub_sq_of_add_eq_two_pow hk hdvd)
    · rintro ⟨rfl, rfl, rfl⟩
      exact not_exists_prime_dvd_two_pow_six_sub_one_pow_six ⟨p, hp, hdvd, hprim⟩
  · rintro ⟨h₂, h₆⟩
    refine exists_prime_dvd_pow_sub_pow hb hba hab hn (fun hn2 hk => h₂ ⟨hn2, hk⟩) fun hn6 => ?_
    by_contra! h
    exact h₆ ⟨h.1, h.2, hn6⟩

/-- **Index lower bound for homogeneous cyclotomic values.** For natural numbers `0 < b < a` and
`n ≥ 2` (without assuming `a` and `b` coprime), `n < Φ_n(a, b)` except at `(a, b, n) = (2, 1, 6)`,
where `Φ_6(2, 1) = 3`. At `n = 1` this fails for `(a, b) = (2, 1)`, and at `b = 0` for
`a = 1`. -/
theorem natCast_lt_homogeneousCyclotomic_iff {a b n : ℕ} (hb : 0 < b) (hba : b < a)
    (hn : 2 ≤ n) :
    (n : ℤ) < homogeneousCyclotomic n (a : ℤ) b ↔ ¬(a = 2 ∧ b = 1 ∧ n = 6) := by
  constructor
  · rintro h ⟨rfl, rfl, rfl⟩
    simp only [homogeneousCyclotomic_six] at h
    norm_num at h
  · intro hex
    rcases hn.eq_or_lt with rfl | hn3
    · simp only [homogeneousCyclotomic_two]
      omega
    -- Factor out `g = gcd(a, b)`: `Φ_n(a, b) = g ^ φ(n) * Φ_n(a', b')` with `a', b'` coprime.
    obtain ⟨g, a', b', hg, hab', rfl, rfl⟩ := Nat.exists_coprime' (Nat.gcd_pos_of_pos_right a hb)
    have hb' : 0 < b' := Nat.pos_of_ne_zero (left_ne_zero_of_mul hb.ne')
    have hba' : b' < a' := (Nat.mul_lt_mul_right hg).1 hba
    have hhom : homogeneousCyclotomic n ((a' * g : ℕ) : ℤ) (b' * g : ℕ) =
        (g : ℤ) ^ n.totient * homogeneousCyclotomic n (a' : ℤ) b' := by
      push_cast
      rw [mul_comm (a' : ℤ) g, mul_comm (b' : ℤ) g, homogeneousCyclotomic_mul_mul]
    rw [hhom]
    by_cases hex' : a' = 2 ∧ b' = 1 ∧ n = 6
    · rcases hex' with ⟨rfl, rfl, rfl⟩
      have hg2 : 2 ≤ g := by omega
      have htot : Nat.totient 6 = 2 := by decide
      rw [htot]
      simp only [Nat.cast_ofNat, Nat.cast_one, homogeneousCyclotomic_six]
      have hg_sq : (4 : ℤ) ≤ (g : ℤ) ^ 2 := by
        have : (2 : ℤ) ≤ g := by exact_mod_cast hg2
        nlinarith
      omega
    · -- A primitive prime divisor `q` of `a' ^ n - b' ^ n` satisfies `n < q` and `q ∣ Φ_n(a', b')`.
      obtain ⟨q, hq, hqdvd, hqprim⟩ := exists_prime_dvd_pow_sub_pow hb' hba' hab' hn (by omega)
        fun hn6 => by by_contra! h; exact hex' ⟨h.1, h.2, hn6⟩
      have hnq : n < q := hq.exponent_lt_of_primitive hqdvd hqprim
      have hqΦ : (q : ℤ) ∣ homogeneousCyclotomic n (a' : ℤ) b' :=
        ((hq.primitive_divisor_iff_dvd_homogeneousCyclotomic hab' hba'.le
          (by omega)).1 ⟨hqdvd, hqprim⟩).1
      have hΦpos : 0 < homogeneousCyclotomic n (a' : ℤ) b' :=
        homogeneousCyclotomic_pos (Int.natCast_nonneg b') (by exact_mod_cast hba') n
      have hqle : (q : ℤ) ≤ homogeneousCyclotomic n (a' : ℤ) b' := Int.le_of_dvd hΦpos hqΦ
      have hg1 : (1 : ℤ) ≤ (g : ℤ) ^ n.totient := one_le_pow₀ (by omega)
      calc (n : ℤ) < q := by exact_mod_cast hnq
        _ ≤ homogeneousCyclotomic n (a' : ℤ) b' := hqle
        _ ≤ (g : ℤ) ^ n.totient * homogeneousCyclotomic n (a' : ℤ) b' :=
          le_mul_of_one_le_left hΦpos.le hg1

end TauCeti

namespace Nat.Prime

/-- **Prime-divisor lower bound for homogeneous cyclotomic values.** For a prime `p` dividing
`n ≠ 0` and natural numbers `0 < b < a`, `p < Φ_n(a, b)` except at `(a, b, n, p) = (2, 1, 6, 3)`,
where `Φ_6(2, 1) = 3` equals the largest prime factor of `6` (while `2 < Φ_6(2, 1)` still holds).
No coprimality assumption on `a` and `b` is needed. -/
theorem natCast_lt_homogeneousCyclotomic_iff {p : ℕ} (hp : p.Prime) {a b n : ℕ}
    (hpn : p ∣ n) (hn : n ≠ 0) (hb : 0 < b) (hba : b < a) :
    (p : ℤ) < TauCeti.homogeneousCyclotomic n (a : ℤ) b ↔
      ¬(a = 2 ∧ b = 1 ∧ n = 6 ∧ p = 3) := by
  constructor
  · rintro h ⟨rfl, rfl, rfl, rfl⟩
    simp only [TauCeti.homogeneousCyclotomic_six] at h
    norm_num at h
  · intro hex
    by_cases h216 : a = 2 ∧ b = 1 ∧ n = 6
    · rcases h216 with ⟨rfl, rfl, rfl⟩
      have hp3 : p ≠ 3 := fun hp3 => hex ⟨rfl, rfl, rfl, hp3⟩
      -- Since `p` is prime and divides `6 = 2 * 3` with `p ≠ 3`, `p = 2 < 3 = Φ_6(2, 1)`.
      have h23 : p ∣ 2 * 3 := hpn
      rcases hp.dvd_mul.1 h23 with hp2 | hp3'
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hp2
        simp only [TauCeti.homogeneousCyclotomic_six]
        norm_num
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hp3') hp3
    · have hpn_le : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn
      have hn2 : 2 ≤ n := hp.two_le.trans hpn_le
      exact (Nat.cast_le.2 hpn_le).trans_lt
        ((TauCeti.natCast_lt_homogeneousCyclotomic_iff hb hba hn2).2 h216)

end Nat.Prime

namespace TauCeti

/-! ### Multiplicative orders and sums of powers -/

/-- **Two-variable multiplicative-order characterization.** For coprime natural numbers `a > b > 0`
and `n ≥ 2`, there is a prime `p` not dividing `a * b` at which `a / b` (`a * b⁻¹` in `ZMod p`) has
multiplicative order `n` iff neither `n = 2` with `a + b` a power of two nor `(a, b, n) = (2, 1, 6)`
holds. Coprimality is sharp: `(a, b, n) = (9, 3, 2)` and `(4, 2, 6)` have no such prime. For any
such `p`, `n ∣ p - 1` (`Nat.Prime.orderOf_ratio_dvd_sub_one`) and `n < p` (`ZMod.orderOf_lt`). -/
theorem exists_prime_orderOf_div_eq_iff {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b) (hn : 2 ≤ n) :
    (∃ p : ℕ, p.Prime ∧ ¬p ∣ a * b ∧ orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = n) ↔
      ¬(n = 2 ∧ ∃ k : ℕ, a + b = 2 ^ k) ∧
      ¬(a = 2 ∧ b = 1 ∧ n = 6) := by
  rw [← exists_prime_dvd_pow_sub_pow_iff hb hba hab hn]
  exact exists_congr fun p => and_congr_right fun hp =>
    (hp.primitive_divisor_iff_orderOf_eq hab hba.le (by omega)).symm

/-- **Two-variable multiplicative-order form of the Bang–Zsigmondy theorem.** For coprime natural
numbers `a > b > 0` and `n ≥ 2` outside the two exceptional cases, there is a prime `p` not
dividing `a * b` at which `a / b` has multiplicative order `n` in `ZMod p` (Roitman 1997,
p. 1913). -/
theorem exists_prime_orderOf_div_eq {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b) (hn : 2 ≤ n)
    (h₂ : n = 2 → ¬∃ k : ℕ, a + b = 2 ^ k)
    (h₆ : n = 6 → a ≠ 2 ∨ b ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ a * b ∧ orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = n := by
  refine (exists_prime_orderOf_div_eq_iff hb hba hab hn).2 ⟨fun ⟨hn2, hk⟩ => h₂ hn2 hk, ?_⟩
  rintro ⟨rfl, rfl, rfl⟩
  rcases h₆ rfl with ha | hb0 <;> exact absurd rfl ‹_›

/-- **Base-one multiplicative-order characterization.** For `a ≥ 2` and `n ≥ 2`, there is a prime
`p` at which `a` has multiplicative order `n` in `ZMod p` iff neither `n = 2` with `a + 1` a power
of two nor `(a, n) = (2, 6)` holds (Roitman 1997, Theorem 3, p. 1914). Both lower bounds are sharp:
`a = 1` has order `1` modulo every prime, and at `n = 1` no prime divides `2 - 1`. -/
theorem exists_prime_orderOf_eq_iff {a n : ℕ} (ha : 2 ≤ a) (hn : 2 ≤ n) :
    (∃ p : ℕ, p.Prime ∧ orderOf (a : ZMod p) = n) ↔
      ¬(n = 2 ∧ ∃ k : ℕ, a + 1 = 2 ^ k) ∧ ¬(a = 2 ∧ n = 6) := by
  have hiff : (∃ p : ℕ, p.Prime ∧ orderOf (a : ZMod p) = n) ↔
      ∃ p : ℕ, p.Prime ∧ ¬p ∣ a * 1 ∧ orderOf ((a : ZMod p) * ((1 : ℕ) : ZMod p)⁻¹) = n := by
    refine exists_congr fun p => and_congr_right fun hp => ?_
    let : Fact p.Prime := ⟨hp⟩
    have h1 : (a : ZMod p) * ((1 : ℕ) : ZMod p)⁻¹ = (a : ZMod p) := by simp
    refine ⟨fun h => ⟨hp.orderOf_ratio_pos_iff.1 (by rw [h1, h]; omega), ?_⟩, fun ⟨_, h⟩ => ?_⟩
    · rwa [h1]
    · rwa [← h1]
  rw [hiff, exists_prime_orderOf_div_eq_iff Nat.one_pos ha (Nat.coprime_one_right a) hn]
  simp

/-- For `a ≥ 3` and `n ≥ 3`, there is a prime `p` at which `a` has multiplicative order `n` in
`ZMod p` (Roitman 1997, Theorem 3, p. 1914). Both bounds are sharp: `(a, n) = (2, 6)` and
`(a, n) = (3, 2)` have no such prime. -/
theorem exists_prime_orderOf_eq {a n : ℕ} (ha : 3 ≤ a) (hn : 3 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ orderOf (a : ZMod p) = n :=
  (exists_prime_orderOf_eq_iff (by omega) (by omega)).2 ⟨by omega, by omega⟩

/-- Modulo some prime `p`, the residue `2 : ZMod p` achieves multiplicative order `n` iff `n ≠ 1`
and `n ≠ 6`: order `0` is realized at the ramified prime `p = 2` (where `(2 : ZMod 2) = 0`), order
`1` would force `p ∣ 2 - 1`, and order `6` fails because `2 ^ 6 - 1 = 63 = 3 ^ 2 * 7`. -/
theorem exists_prime_orderOf_two_eq_iff {n : ℕ} :
    (∃ p : ℕ, p.Prime ∧ orderOf (2 : ZMod p) = n) ↔ n ≠ 1 ∧ n ≠ 6 := by
  rcases n with _ | _ | n
  · refine ⟨fun _ => by decide, fun _ => ⟨2, Nat.prime_two, ?_⟩⟩
    let : Fact (1 < 2) := ⟨by decide⟩
    have h20 : (2 : ZMod 2) = 0 := by decide
    rw [h20, orderOf_zero]
  · refine ⟨?_, fun h => absurd rfl h.1⟩
    rintro ⟨p, hp, h1⟩
    let : Fact p.Prime := ⟨hp⟩
    have h21 : (2 : ZMod p) - 1 = 0 := sub_eq_zero.2 (orderOf_eq_one_iff.1 h1)
    norm_num at h21
  · have hn2 : 2 ≤ n + 2 := by omega
    have hcast : ∀ p : ℕ, (((2 : ℕ) : ZMod p)) = (2 : ZMod p) := fun _ => Nat.cast_two
    simp_rw [← hcast]
    rw [exists_prime_orderOf_eq_iff (le_refl 2) hn2]
    refine ⟨fun ⟨_, h6⟩ => ⟨by omega, fun h => h6 ⟨rfl, h⟩⟩, fun ⟨_, h6⟩ => ⟨?_, ?_⟩⟩
    · rintro ⟨_, k, hk⟩
      rcases k with _ | _ | k
      · omega
      · omega
      · have : 2 ^ 2 ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
    · rintro ⟨_, h⟩
      exact h6 h

/-- For `n ≥ 2` with `n ≠ 6`, there is a prime `p` at which `2` has multiplicative order `n` in
`ZMod p` (Roitman 1997, Theorem 3, p. 1914, at `a = 2`). -/
theorem exists_prime_orderOf_two_eq {n : ℕ} (hn : 2 ≤ n) (h₆ : n ≠ 6) :
    ∃ p : ℕ, p.Prime ∧ orderOf (2 : ZMod p) = n :=
  exists_prime_orderOf_two_eq_iff.2 ⟨by omega, h₆⟩

/-- **Primitive prime divisors for sums of powers.** For coprime natural numbers `a > b > 0` and
any `n : ℕ`, there is a prime dividing `a ^ n + b ^ n` and none of `a ^ k - b ^ k` with
`0 < k < 2 * n` iff neither `n = 1` with `a + b` a power of two nor `(a, b, n) = (2, 1, 3)` holds.
At `n = 0`, `a ^ 0 + b ^ 0 = 2` is divisible by `2` and the range `0 < k < 0` is empty; for
`n ≥ 1`, any such prime has `a / b` of multiplicative order `2 * n` modulo `p`
(`Nat.Prime.dvd_pow_add_pow_and_not_dvd_iff_orderOf_eq`). The hypotheses `0 < b`, `b < a` and
`a.Coprime b` are sharp: `(1, 0, 2)`, `(1, 1, 2)` and `(4, 2, 3)` have no such prime. -/
theorem exists_prime_dvd_pow_add_pow_iff {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b) :
    (∃ p : ℕ, p.Prime ∧ p ∣ a ^ n + b ^ n ∧
      ∀ k : ℕ, 0 < k → k < 2 * n → ¬p ∣ a ^ k - b ^ k) ↔
      ¬(n = 1 ∧ ∃ k : ℕ, a + b = 2 ^ k) ∧
      ¬(a = 2 ∧ b = 1 ∧ n = 3) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨fun _ => by simp, fun _ => ⟨2, Nat.prime_two, by simp, by omega⟩⟩
  have hiff : (∃ p : ℕ, p.Prime ∧ p ∣ a ^ n + b ^ n ∧
      ∀ k : ℕ, 0 < k → k < 2 * n → ¬p ∣ a ^ k - b ^ k) ↔
      (∃ p : ℕ, p.Prime ∧ p ∣ a ^ (2 * n) - b ^ (2 * n) ∧
        ∀ k : ℕ, 0 < k → k < 2 * n → ¬p ∣ a ^ k - b ^ k) :=
    exists_congr fun p => and_congr_right fun hp => hp.dvd_pow_add_pow_and_not_dvd_iff hn
  rw [hiff, exists_prime_dvd_pow_sub_pow_iff hb hba hab (by omega)]
  constructor <;> rintro ⟨h1, h3⟩ <;> refine ⟨?_, ?_⟩
  · rintro ⟨rfl, hk⟩; exact h1 ⟨rfl, hk⟩
  · rintro ⟨rfl, rfl, rfl⟩; exact h3 ⟨rfl, rfl, rfl⟩
  · rintro ⟨h2n, hk⟩; exact h1 ⟨by omega, hk⟩
  · rintro ⟨rfl, rfl, h2n⟩; exact h3 ⟨rfl, rfl, by omega⟩

/-- For coprime natural numbers `a > b > 0` and any `n : ℕ`, unless `n = 1` with `a + b` a power of
two or `(a, b, n) = (2, 1, 3)`, there is a prime dividing `a ^ n + b ^ n` and none of
`a ^ k - b ^ k` for `0 < k < 2 * n`. -/
theorem exists_prime_dvd_pow_add_pow {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b)
    (h₁ : n = 1 → ¬∃ k : ℕ, a + b = 2 ^ k)
    (h₃ : n = 3 → a ≠ 2 ∨ b ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ a ^ n + b ^ n ∧
      ∀ k : ℕ, 0 < k → k < 2 * n → ¬p ∣ a ^ k - b ^ k := by
  refine (exists_prime_dvd_pow_add_pow_iff hb hba hab).2 ⟨fun ⟨hn1, hk⟩ => h₁ hn1 hk, ?_⟩
  rintro ⟨rfl, rfl, rfl⟩
  rcases h₃ rfl with ha | hb0 <;> exact absurd rfl ‹_›

end TauCeti
