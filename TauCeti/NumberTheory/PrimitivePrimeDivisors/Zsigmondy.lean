/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import TauCeti.RingTheory.Polynomial.Cyclotomic.Homogeneous
import TauCeti.NumberTheory.PrimitivePrimeDivisors.Cyclotomic
import TauCeti.NumberTheory.PrimitivePrimeDivisors.Estimates
import TauCeti.NumberTheory.PrimitivePrimeDivisors.SmallExponents
import TauCeti.RingTheory.Polynomial.Cyclotomic.Eval

/-!
# The Bang–Zsigmondy theorem

For coprime natural numbers `0 < b < a` and `2 ≤ n`, a **primitive prime divisor** of
`a ^ n - b ^ n` is a prime `p` dividing `a ^ n - b ^ n` and none of the `a ^ k - b ^ k` with
`0 < k < n`. The **Bang–Zsigmondy theorem** asserts that such a prime exists except in two cases:
`n = 2` with `a + b` a power of two, and `(a, b, n) = (2, 1, 6)` (where `2 ^ 6 - 1 = 63 = 3 ^ 2 * 7`
has `3 ∣ 2 ^ 2 - 1` and `7 ∣ 2 ^ 3 - 1`).

At `n = 2` the theorem reduces to the existence of an odd prime factor of `a + b`. For `3 ≤ n`, a
difference of powers without a primitive prime divisor forces the homogeneous cyclotomic value
`Φ_n(a, b)` to equal `1` or the largest prime factor `p` of `n`
(`Nat.Coprime.homogeneousCyclotomic_eq_one_or_eq_prime_of_not_exists_prime_dvd_pow_sub_pow`), while
`Φ_n(a, b) > (a - b) ^ φ(n) ≥ 1` rules out `1` and the size estimates on `Φ_{p ^ e m}(a, b)` rule
out `Φ_n(a, b) = p` outside `(2, 1, 6)`. Conversely, once a primitive prime divisor `q` exists, it
divides `Φ_n(a, b)` and exceeds `n`, so `Φ_n(a, b) > n`, hence `Φ_n(a, b)` strictly exceeds every
prime divisor of `n` unless `(a, b, n) = (2, 1, 6)`.

Combining the theorem with the multiplicative-order characterizations of primitive prime divisors
gives primes `p ∤ a * b` modulo which `a / b` has prescribed order `n` in `ZMod p`, the base-one
specializations for `orderOf (a : ZMod p) = n` and `orderOf (2 : ZMod p) = n` (Bang's theorem),
and, at exponent `2 * n`, primes dividing `a ^ n + b ^ n` and no `a ^ k - b ^ k` for
`0 < k < 2 * n`.

## Main results

* `Nat.Prime.natCast_lt_homogeneousCyclotomic_of_dvd_of_dvd`: for `0 < b < a`, a prime `p`
  dividing both `n` and `Φ_n(a, b)` satisfies `p < Φ_n(a, b)` unless `(a, b, n) = (2, 1, 6)`.
* `TauCeti.exists_prime_dvd_pow_sub_pow`, `TauCeti.exists_prime_dvd_pow_sub_pow_iff`: the
  Bang–Zsigmondy theorem and its exact characterization.
* `TauCeti.natCast_lt_homogeneousCyclotomic_iff`,
  `TauCeti.forall_prime_dvd_lt_homogeneousCyclotomic_iff`: for coprime `0 < b < a`, `n < Φ_n(a, b)`
  (for `2 ≤ n`) and `p < Φ_n(a, b)` for every prime `p ∣ n` (for `n ≠ 0`) hold iff
  `(a, b, n) ≠ (2, 1, 6)`.
* `TauCeti.exists_prime_orderOf_div_eq`, `TauCeti.exists_prime_orderOf_div_eq_iff`: the
  two-variable multiplicative-order formulation in `ZMod p`.
* `TauCeti.exists_prime_orderOf_natCast_eq`, `TauCeti.exists_prime_orderOf_natCast_eq_iff`,
  `TauCeti.exists_prime_orderOf_eq`, `TauCeti.exists_prime_orderOf_two_eq`,
  `TauCeti.exists_prime_orderOf_two_eq_iff`: the base-one and base-two order specializations.
* `TauCeti.exists_prime_dvd_pow_add_pow`, `TauCeti.exists_prime_dvd_pow_add_pow_iff`: primes of
  order `2 * n` dividing `a ^ n + b ^ n` and no earlier `a ^ k - b ^ k`.

## References

* [K. Zsigmondy, *Zur Theorie der Potenzreste*, Monatsh. Math. Phys. 3 (1892), 265–284], p. 283.
* [G. D. Birkhoff and H. S. Vandiver, *On the integral divisors of `a ^ n - b ^ n`*,
  Ann. of Math. (2) 5 (1904), 173–180], Theorem V, pp. 178–179.
* [M. Roitman, *On Zsigmondy primes*, Proc. Amer. Math. Soc. 125 (1997), 1913–1919], Lemma 1,
  Proposition 2, and Theorem 3, pp. 1913–1915.
* [Ö. Avcı, *Large Zsigmondy primes*, arXiv:2011.06136v2 (2023)], p. 1.
-/

public section

open TauCeti

namespace Nat.Prime

/-- **Size of a homogeneous cyclotomic value at a nonprimitive prime.** For natural bases
`0 < b < a`, a prime `p` dividing both `n` and `Φ_n(a, b)` strictly underestimates `Φ_n(a, b)`
unless `(a, b, n) = (2, 1, 6)`, where `Φ_6(2, 1) = 3`. Neither coprimality of `a` and `b` nor
`3 ≤ n` is needed: at `n = 2`, `p = 2 < 3 ≤ a + b = Φ_2(a, b)`. -/
theorem natCast_lt_homogeneousCyclotomic_of_dvd_of_dvd {p a b n : ℕ} (hp : p.Prime)
    (hb : 0 < b) (hba : b < a) (hpn : p ∣ n)
    (hdvd : (p : ℤ) ∣ homogeneousCyclotomic n (a : ℤ) b)
    (hex : ¬(a = 2 ∧ b = 1 ∧ n = 6)) :
    (p : ℤ) < homogeneousCyclotomic n (a : ℤ) b := by
  have hn : n ≠ 0 := ne_zero_of_dvd_homogeneousCyclotomic (Nat.prime_iff_prime_int.1 hp).not_isUnit
    hdvd
  obtain ⟨m, rfl⟩ := hpn
  have hm : m ≠ 0 := right_ne_zero_of_mul hn
  by_cases hpm : p ∣ m
  · obtain ⟨k, rfl⟩ := hpm
    exact Int.natCast_lt_homogeneousCyclotomic_of_sq_dvd hp ⟨k, by ring⟩ hn
      (by exact_mod_cast hb) (by exact_mod_cast hba)
  obtain rfl | hm2 : m = 1 ∨ 2 ≤ m := by omega
  · simpa using natCast_lt_homogeneousCyclotomic_prime hp (a := (a : ℤ)) (by omega)
      (by exact_mod_cast hb)
  by_cases hpb : p ∣ b
  · -- If `p ∣ b`, then `p` also divides `a`, so `p ≤ a - b ≤ (a - b) ^ φ(p m) < Φ_{p m}(a, b)`.
    have hdvd_pow : (p : ℤ) ∣ ((a ^ (p * m) : ℕ) : ℤ) - ((b ^ (p * m) : ℕ) : ℤ) := by
      push_cast
      exact hdvd.trans (homogeneousCyclotomic_dvd_pow_sub_pow dvd_rfl _ _)
    have han : (p : ℤ) ∣ ((a ^ (p * m) : ℕ) : ℤ) :=
      (dvd_sub_left (Int.natCast_dvd_natCast.2 (dvd_pow hpb hn))).1 hdvd_pow
    have hpa : p ∣ a := hp.dvd_of_dvd_pow (Int.natCast_dvd_natCast.1 han)
    have hple : p ≤ a - b := Nat.le_of_dvd (Nat.sub_pos_of_lt hba) (Nat.dvd_sub hpa hpb)
    have hsub : (p : ℤ) ≤ (a : ℤ) - b := by omega
    have hpow : (a : ℤ) - b ≤ ((a : ℤ) - b) ^ (p * m).totient :=
      le_self_pow₀ (by omega) (Nat.totient_pos.2 (Nat.pos_of_ne_zero hn)).ne'
    exact (hsub.trans hpow).trans_lt (Int.sub_pow_totient_lt_homogeneousCyclotomic
      (hp.two_le.trans (Nat.le_mul_of_pos_right p (Nat.pos_of_ne_zero hm)))
      (by exact_mod_cast hb) (by exact_mod_cast hba))
  · -- Otherwise `p ∤ b` and `2 ≤ m ∣ p - 1`, so `3 ≤ p`, and `Φ_{p m}(a, b) > p` via `ℝ`.
    have hpb' : ¬(p : ℤ) ∣ (b : ℤ) := fun h => hpb (Int.natCast_dvd_natCast.1 h)
    have hcompl : ordCompl[p] (p * m) = m := by
      have h1 : ordCompl[p] (p * m) = ordCompl[p] m := by
        simpa using Nat.ordCompl_self_pow_mul m 1 hp
      exact h1.trans ((Nat.ordCompl_eq_self_iff_zero_or_not_dvd m hp).2 (Or.inr hpm))
    have hm_dvd : m ∣ p - 1 := hcompl ▸ hp.ordCompl_dvd_sub_one_of_dvd_homogeneousCyclotomic hpb'
      hdvd
    have hp3 : 3 ≤ p := by
      have := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) hm_dvd
      omega
    have hex' : ¬(a = 2 ∧ b = 1 ∧ p = 3) := by
      rintro ⟨rfl, rfl, rfl⟩
      have : m ≤ 2 := Nat.le_of_dvd (by decide) hm_dvd
      exact hex ⟨rfl, rfl, by omega⟩
    rw [← Int.cast_lt (R := ℝ), Int.cast_natCast, Int.cast_homogeneousCyclotomic,
      Int.cast_natCast, Int.cast_natCast]
    exact (lt_pow_sub_pow_div_add_pow hb hba hp3 hex'
      (Nat.totient_pos.2 (Nat.pos_of_ne_zero hm))).trans
      (pow_sub_pow_div_add_pow_totient_lt_homogeneousCyclotomic hp hm hpm
        (by exact_mod_cast hb) (by exact_mod_cast hba))

end Nat.Prime

namespace TauCeti

/-! ### The Bang–Zsigmondy theorem and cyclotomic size bounds -/

/-- **The Bang–Zsigmondy theorem.** For coprime natural numbers `0 < b < a` and `2 ≤ n`, there is
a prime dividing `a ^ n - b ^ n` and none of the `a ^ k - b ^ k` with `0 < k < n`, unless `n = 2`
and `a + b` is a power of two, or `(a, b, n) = (2, 1, 6)` (Zsigmondy 1892, p. 283;
Birkhoff–Vandiver 1904, Theorem V, p. 178). -/
theorem exists_prime_dvd_pow_sub_pow {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b) (hn : 2 ≤ n)
    (h₂ : n = 2 → ¬∃ k : ℕ, a + b = 2 ^ k)
    (h₆ : n = 6 → a ≠ 2 ∨ b ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ a ^ n - b ^ n ∧
      ∀ k : ℕ, 0 < k → k < n → ¬p ∣ a ^ k - b ^ k := by
  obtain rfl | hn3 : n = 2 ∨ 3 ≤ n := by omega
  · exact (exists_prime_dvd_sq_sub_sq_iff hba.le hab).2 (h₂ rfl)
  by_contra hnot
  rcases hab.homogeneousCyclotomic_eq_one_or_eq_prime_of_not_exists_prime_dvd_pow_sub_pow hba
      (by omega) hnot with h1 | ⟨p, hp, hpn, _, hpΦ⟩
  · have hlt := Int.sub_pow_totient_lt_homogeneousCyclotomic hn (a := a) (b := b)
      (by exact_mod_cast hb) (by exact_mod_cast hba)
    have hone : (1 : ℤ) ≤ ((a : ℤ) - b) ^ n.totient := one_le_pow₀ (by omega)
    linarith
  · have hex : ¬(a = 2 ∧ b = 1 ∧ n = 6) := by
      rintro ⟨rfl, rfl, rfl⟩
      rcases h₆ rfl with h | h <;> exact h rfl
    have hlt := hp.natCast_lt_homogeneousCyclotomic_of_dvd_of_dvd hb hba hpn (hpΦ ▸ dvd_rfl) hex
    omega

/-- **Exact characterization of primitive prime divisors.** For coprime natural numbers
`0 < b < a` and `2 ≤ n`, a primitive prime divisor of `a ^ n - b ^ n` exists if and only if
neither `n = 2` with `a + b` a power of two nor `(a, b, n) = (2, 1, 6)` holds (Roitman 1997,
Theorem 3, p. 1914, for `b = 1`). -/
theorem exists_prime_dvd_pow_sub_pow_iff {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b) (hn : 2 ≤ n) :
    (∃ p : ℕ, p.Prime ∧ p ∣ a ^ n - b ^ n ∧
      ∀ k : ℕ, 0 < k → k < n → ¬p ∣ a ^ k - b ^ k) ↔
      ¬(n = 2 ∧ ∃ k : ℕ, a + b = 2 ^ k) ∧
      ¬(a = 2 ∧ b = 1 ∧ n = 6) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rintro ⟨rfl, hk⟩
      exact (exists_prime_dvd_sq_sub_sq_iff hba.le hab).1 h hk
    · rintro ⟨rfl, rfl, rfl⟩
      exact not_exists_prime_dvd_two_pow_six_sub_one_pow_six h
  · rintro ⟨h₂, h₆⟩
    exact exists_prime_dvd_pow_sub_pow hb hba hab hn (fun hn2 hk => h₂ ⟨hn2, hk⟩)
      (fun hn6 => by
        by_contra! h
        exact h₆ ⟨h.1, h.2, hn6⟩)

/-- For coprime natural numbers `0 < b < a` and `2 ≤ n`, the homogeneous cyclotomic value
`Φ_n(a, b)` exceeds `n` if and only if `(a, b, n) ≠ (2, 1, 6)`, where `Φ_6(2, 1) = 3`. For
`n = 1` this fails at `(2, 1, 1)`, where `Φ_1(2, 1) = 1`. -/
theorem natCast_lt_homogeneousCyclotomic_iff {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b) (hn : 2 ≤ n) :
    (n : ℤ) < homogeneousCyclotomic n (a : ℤ) b ↔ ¬(a = 2 ∧ b = 1 ∧ n = 6) := by
  constructor
  · rintro h ⟨rfl, rfl, rfl⟩
    rw [homogeneousCyclotomic_six] at h
    norm_num at h
  · intro hex
    obtain rfl | hn3 : n = 2 ∨ 3 ≤ n := by omega
    · rw [homogeneousCyclotomic_two]
      omega
    obtain ⟨q, hq, hdiv, hprev⟩ := exists_prime_dvd_pow_sub_pow hb hba hab hn (by omega)
      (fun hn6 => by
        by_contra! h
        exact hex ⟨h.1, h.2, hn6⟩)
    have hnq : n < q := hq.exponent_lt_of_primitive hdiv hprev
    have hqΦ : (q : ℤ) ∣ homogeneousCyclotomic n (a : ℤ) b :=
      ((hq.primitive_divisor_iff_dvd_homogeneousCyclotomic hab hba.le (by omega)).1
        ⟨hdiv, hprev⟩).1
    have hpos : 0 < homogeneousCyclotomic n (a : ℤ) b :=
      homogeneousCyclotomic_pos (Int.natCast_nonneg b) (by exact_mod_cast hba) n
    exact (Int.ofNat_lt.2 hnq).trans_le (Int.le_of_dvd hpos hqΦ)

/-- For coprime natural numbers `0 < b < a` and `n ≠ 0`, `Φ_n(a, b)` strictly exceeds every prime
factor of `n` (in particular, the largest prime factor of `n`) if and only if
`(a, b, n) ≠ (2, 1, 6)`, where `Φ_6(2, 1) = 3` equals the largest prime factor of `6`
(Birkhoff–Vandiver 1904, proof of Theorem V, pp. 178–179; Roitman 1997, Lemma 1 and proof of
Theorem 3, pp. 1913–1915). -/
theorem forall_prime_dvd_lt_homogeneousCyclotomic_iff {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b) (hn : n ≠ 0) :
    (∀ p : ℕ, p.Prime → p ∣ n → (p : ℤ) < homogeneousCyclotomic n (a : ℤ) b) ↔
      ¬(a = 2 ∧ b = 1 ∧ n = 6) := by
  constructor
  · rintro h ⟨rfl, rfl, rfl⟩
    have h3 := h 3 Nat.prime_three (by decide)
    rw [homogeneousCyclotomic_six] at h3
    norm_num at h3
  · intro hex p hp hpn
    have hn2 : 2 ≤ n := hp.two_le.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn)
    have hpn_le : (p : ℤ) ≤ n := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn
    exact hpn_le.trans_lt ((natCast_lt_homogeneousCyclotomic_iff hb hba hab hn2).2 hex)

/-! ### Multiplicative-order and sum-of-powers corollaries -/

/-- **Two-variable order characterization.** For coprime natural numbers `0 < b < a` and `2 ≤ n`,
there is a prime `p` not dividing `a * b` at which `a * b⁻¹` has multiplicative order `n` in
`ZMod p` if and only if neither exceptional case holds. The inverse is `ZMod.inv`, which agrees
with the field inverse at a prime; for any such `p`, `n ∣ p - 1`
(`Nat.Prime.orderOf_ratio_dvd_sub_one`) and `n < p` (`ZMod.orderOf_lt`). -/
theorem exists_prime_orderOf_div_eq_iff {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b) (hn : 2 ≤ n) :
    (∃ p : ℕ, p.Prime ∧ ¬p ∣ a * b ∧ orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = n) ↔
      ¬(n = 2 ∧ ∃ k : ℕ, a + b = 2 ^ k) ∧
      ¬(a = 2 ∧ b = 1 ∧ n = 6) := by
  rw [← exists_prime_dvd_pow_sub_pow_iff hb hba hab hn]
  exact exists_congr fun p => and_congr_right fun hp =>
    (hp.primitive_divisor_iff_orderOf_eq hab hba.le (by omega)).symm

/-- **The two-variable order form of Bang–Zsigmondy.** Outside the two exceptions there is a prime
`p` not dividing `a * b` at which `a * b⁻¹` has multiplicative order `n` in `ZMod p` (Roitman
1997, p. 1913). -/
theorem exists_prime_orderOf_div_eq {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b) (hn : 2 ≤ n)
    (h₂ : n = 2 → ¬∃ k : ℕ, a + b = 2 ^ k)
    (h₆ : n = 6 → a ≠ 2 ∨ b ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ a * b ∧ orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = n :=
  (exists_prime_orderOf_div_eq_iff hb hba hab hn).2
    ⟨fun ⟨hn2, hk⟩ => h₂ hn2 hk, fun ⟨ha, hb1, hn6⟩ => (h₆ hn6).elim (· ha) (· hb1)⟩

/-- **Base-one order characterization.** For `2 ≤ a` and `2 ≤ n`, there is a prime `p` at which
`a` has multiplicative order `n` in `ZMod p` if and only if neither `n = 2` with `a + 1` a power
of two nor `(a, n) = (2, 6)` holds (Roitman 1997, Theorem 3, p. 1914). Any such prime satisfies
`p ∤ a`, since `orderOf (0 : ZMod p) = 0`. -/
theorem exists_prime_orderOf_natCast_eq_iff {a n : ℕ} (ha : 2 ≤ a) (hn : 2 ≤ n) :
    (∃ p : ℕ, p.Prime ∧ orderOf (a : ZMod p) = n) ↔
      ¬(n = 2 ∧ ∃ k : ℕ, a + 1 = 2 ^ k) ∧ ¬(a = 2 ∧ n = 6) := by
  have hiff := exists_prime_orderOf_div_eq_iff Nat.one_pos (by omega)
    (Nat.coprime_one_right a) hn
  simp only [true_and, mul_one] at hiff
  rw [← hiff]
  refine exists_congr fun p => and_congr_right fun hp => ?_
  have := Fact.mk hp
  simp only [Nat.cast_one, inv_one, mul_one]
  refine ⟨fun h => ⟨fun hpa => ?_, h⟩, And.right⟩
  rw [(ZMod.natCast_eq_zero_iff a p).2 hpa, orderOf_zero] at h
  omega

/-- For `2 ≤ a` and `2 ≤ n` outside `n = 2` with `a + 1` a power of two and `(a, n) = (2, 6)`,
there is a prime `p` at which `a` has multiplicative order `n` in `ZMod p` (Roitman 1997,
Theorem 3, p. 1914). -/
theorem exists_prime_orderOf_natCast_eq {a n : ℕ} (ha : 2 ≤ a) (hn : 2 ≤ n)
    (h₂ : n = 2 → ¬∃ k : ℕ, a + 1 = 2 ^ k) (h₆ : n = 6 → a ≠ 2) :
    ∃ p : ℕ, p.Prime ∧ orderOf (a : ZMod p) = n :=
  (exists_prime_orderOf_natCast_eq_iff ha hn).2
    ⟨fun ⟨hn2, hk⟩ => h₂ hn2 hk, fun ⟨ha2, hn6⟩ => h₆ hn6 ha2⟩

/-- For `3 ≤ a` and `3 ≤ n` there is a prime `p` at which `a` has multiplicative order `n` in
`ZMod p` (Roitman 1997, Theorem 3, p. 1914: both exceptions are excluded by the hypotheses). -/
theorem exists_prime_orderOf_eq {a n : ℕ} (ha : 3 ≤ a) (hn : 3 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ orderOf (a : ZMod p) = n :=
  exists_prime_orderOf_natCast_eq (by omega) (by omega) (by omega) (by omega)

/-- **Bang's theorem (exact characterization).** For `2 ≤ n`, there is a prime `p` at which `2`
has multiplicative order `n` in `ZMod p` if and only if `n ≠ 6`. -/
theorem exists_prime_orderOf_two_eq_iff {n : ℕ} (hn : 2 ≤ n) :
    (∃ p : ℕ, p.Prime ∧ orderOf (2 : ZMod p) = n) ↔ n ≠ 6 := by
  have hiff := exists_prime_orderOf_natCast_eq_iff (a := 2) le_rfl hn
  simp only [Nat.cast_ofNat, true_and] at hiff
  rw [hiff, and_iff_right]
  rintro ⟨rfl, k, hk⟩
  obtain _ | _ | k := k
  · omega
  · omega
  · have : 4 ≤ 2 ^ (k + 2) :=
      Nat.pow_le_pow_right Nat.two_pos (Nat.le_add_left 2 k)
    omega

/-- **Bang's theorem.** For `2 ≤ n` with `n ≠ 6`, there is a prime `p` at which `2` has
multiplicative order `n` in `ZMod p` (Roitman 1997, Theorem 3, p. 1914, at `a = 2`). -/
theorem exists_prime_orderOf_two_eq {n : ℕ} (hn : 2 ≤ n) (h₆ : n ≠ 6) :
    ∃ p : ℕ, p.Prime ∧ orderOf (2 : ZMod p) = n :=
  (exists_prime_orderOf_two_eq_iff hn).2 h₆

/-- **Sums of powers (exact characterization).** For coprime natural numbers `0 < b < a` and
`1 ≤ n`, there is a prime dividing `a ^ n + b ^ n` and none of the `a ^ k - b ^ k` with
`0 < k < 2 * n` if and only if neither `n = 1` with `a + b` a power of two nor
`(a, b, n) = (2, 1, 3)` holds. -/
theorem exists_prime_dvd_pow_add_pow_iff {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b) (hn : 1 ≤ n) :
    (∃ p : ℕ, p.Prime ∧ p ∣ a ^ n + b ^ n ∧
      ∀ k : ℕ, 0 < k → k < 2 * n → ¬p ∣ a ^ k - b ^ k) ↔
      ¬(n = 1 ∧ ∃ k : ℕ, a + b = 2 ^ k) ∧
      ¬(a = 2 ∧ b = 1 ∧ n = 3) := by
  have heven :
      (∃ p : ℕ, p.Prime ∧ p ∣ a ^ n + b ^ n ∧
        ∀ k : ℕ, 0 < k → k < 2 * n → ¬p ∣ a ^ k - b ^ k) ↔
        ∃ p : ℕ, p.Prime ∧ ¬p ∣ a * b ∧ orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = 2 * n :=
    exists_congr fun p => and_congr_right fun hp =>
      hp.dvd_pow_add_pow_and_forall_not_dvd_iff_orderOf_eq hba.le hn
  have h2 : 2 * n = 2 ↔ n = 1 := by omega
  have h6 : 2 * n = 6 ↔ n = 3 := by omega
  rw [heven, exists_prime_orderOf_div_eq_iff hb hba hab (by omega), h2, h6]

/-- **Primitive prime divisors for sums of powers.** For coprime natural numbers `0 < b < a` and
`1 ≤ n`, unless `n = 1` with `a + b` a power of two or `(a, b, n) = (2, 1, 3)`, there is a prime
dividing `a ^ n + b ^ n` and none of the `a ^ k - b ^ k` with `0 < k < 2 * n` (the Bang–Zsigmondy
theorem at the exponent `2 * n`). -/
theorem exists_prime_dvd_pow_add_pow {a b n : ℕ}
    (hb : 0 < b) (hba : b < a) (hab : a.Coprime b) (hn : 1 ≤ n)
    (h₁ : n = 1 → ¬∃ k : ℕ, a + b = 2 ^ k)
    (h₃ : n = 3 → a ≠ 2 ∨ b ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ a ^ n + b ^ n ∧
      ∀ k : ℕ, 0 < k → k < 2 * n → ¬p ∣ a ^ k - b ^ k :=
  (exists_prime_dvd_pow_add_pow_iff hb hba hab hn).2
    ⟨fun ⟨hn1, hk⟩ => h₁ hn1 hk, fun ⟨ha, hb1, hn3⟩ => (h₃ hn3).elim (· ha) (· hb1)⟩

end TauCeti
