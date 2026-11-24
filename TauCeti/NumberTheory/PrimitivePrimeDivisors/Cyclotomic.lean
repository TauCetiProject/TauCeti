/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Nat.Factorization.Basic
public import TauCeti.NumberTheory.PrimitivePrimeDivisors.Valuation
public import TauCeti.RingTheory.Polynomial.Cyclotomic.Homogeneous
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand

/-!
# Prime divisors of homogeneous cyclotomic values

Let `p` be a prime not dividing `b` and let `n ≠ 0`. Then `p` divides the homogeneous cyclotomic
value `Φ_n(a, b)` (`TauCeti.homogeneousCyclotomic`) exactly when the order of `a / b` modulo `p` is
the `p`-free part `ordCompl[p] n` of `n`: reducing modulo `p`, `a / b` is a root of the cyclotomic
polynomial `Φ_n` over `ZMod p`, and in characteristic `p` the roots of `Φ_{p ^ e m}` with
`p ∤ m` are the primitive `m`-th roots of unity.

Consequently every prime divisor `p` of `Φ_n(a, b)` with `p ∤ b` is at least every prime factor
of `n`. For coprime natural bases `b ≤ a` and `0 < n`, the primitive prime divisors of
`a ^ n - b ^ n` are exactly the prime divisors of `Φ_n(a, b)` that do not divide `n`. For coprime
natural bases `b < a` and `n ≠ 2`, a nonprimitive prime divisor `p` of `Φ_n(a, b)` therefore
divides `n`, is its largest prime factor, and divides `Φ_n(a, b)` exactly once. This is the
dichotomy behind the Bang–Zsigmondy theorem: for coprime natural bases `b < a` and `n ≠ 2`, if
`a ^ n - b ^ n` has no primitive prime divisor, then `Φ_n(a, b)` is `1` or the largest prime
factor of `n`.

## Main results

* `Nat.Prime.dvd_homogeneousCyclotomic_iff_orderOf_eq`: for `p ∤ b` and `n ≠ 0`,
  `p ∣ Φ_n(a, b)` iff the order of `a / b` in `ZMod p` is `ordCompl[p] n`.
* `Nat.Prime.ordCompl_dvd_sub_one_of_dvd_homogeneousCyclotomic`,
  `Nat.Prime.le_of_dvd_homogeneousCyclotomic_of_prime_of_dvd`: for `p ∤ b` dividing
  `Φ_n(a, b)`, `ordCompl[p] n ∣ p - 1` and every prime factor of `n` is at most `p`.
* `Nat.Coprime.not_dvd_mul_of_dvd_homogeneousCyclotomic`: for coprime natural bases, a prime
  divisor of `Φ_n(a, b)` divides neither base.
* `Nat.Prime.primitive_divisor_iff_dvd_homogeneousCyclotomic`: for coprime natural bases
  `b ≤ a` and `0 < n`, `p` is a primitive prime divisor of `a ^ n - b ^ n` iff `p ∣ Φ_n(a, b)`
  and `p ∤ n`.
* `Nat.Prime.multiplicity_homogeneousCyclotomic_eq_one`: for natural bases `b < a`, `p ∤ b`,
  `p ∣ n` and `n ≠ 2`, a prime divisor `p` of `Φ_n(a, b)` divides it exactly once.
* `Nat.Prime.multiplicity_homogeneousCyclotomic_of_not_primitive`: for coprime natural bases
  `b < a` and `n ≠ 2`, a prime divisor `p` of `Φ_n(a, b)` dividing some `a ^ k - b ^ k` with
  `0 < k < n` divides `n`, is its largest prime factor, and divides `Φ_n(a, b)` exactly once.
* `Nat.Coprime.homogeneousCyclotomic_eq_one_or_eq_prime_of_not_exists_prime_dvd_pow_sub_pow`: for
  coprime natural bases `b < a` and `n ≠ 2`, if `a ^ n - b ^ n` has no primitive prime divisor,
  then `Φ_n(a, b)` is `1` or the largest prime factor of `n`.

## References

* [G. D. Birkhoff and H. S. Vandiver, *On the integral divisors of `a ^ n - b ^ n`*,
  Ann. of Math. (2) 5 (1904), 173–180], Theorem IV, p. 177.
* [M. Roitman, *On Zsigmondy primes*, Proc. Amer. Math. Soc. 125 (1997), 1913–1919],
  Proposition 2, p. 1914.
* [Ö. Avcı, *Large Zsigmondy primes*, arXiv:2011.06136v2 (2023)], Lemmas 2.11 and 3.1.
-/

public section

open Polynomial TauCeti

namespace Nat.Prime

variable {p : ℕ}

/-- **Prime divisors of a homogeneous cyclotomic value.** For a prime `p ∤ b` and `n ≠ 0`, `p`
divides `Φ_n(a, b)` iff the order of `a / b` in `ZMod p` is the `p`-free part of `n`. The inverse
is `ZMod.inv`, so the statement needs no primality instance. -/
theorem dvd_homogeneousCyclotomic_iff_orderOf_eq (hp : p.Prime) {a b : ℤ}
    (hb : ¬(p : ℤ) ∣ b) {n : ℕ} (hn : n ≠ 0) :
    (p : ℤ) ∣ homogeneousCyclotomic n a b ↔
      orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = ordCompl[p] n := by
  have := Fact.mk hp
  have hb0 : (b : ZMod p) ≠ 0 := fun h => hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp h)
  have : NeZero ((ordCompl[p] n : ℕ) : ZMod p) :=
    ⟨fun h => Nat.not_dvd_ordCompl hp hn ((ZMod.natCast_eq_zero_iff _ p).mp h)⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_homogeneousCyclotomic,
    homogeneousCyclotomic_eq_eval_div_mul_pow _ _ hb0, _root_.mul_eq_zero,
    or_iff_left (pow_ne_zero _ hb0), ← IsPrimitiveRoot.iff_orderOf, ← div_eq_mul_inv,
    ← isRoot_cyclotomic_prime_pow_mul_iff_of_charP (k := n.factorization p),
    Nat.ordProj_mul_ordCompl_eq_self, IsRoot.def]

/-- For a prime `p ∤ b` dividing `Φ_n(a, b)`, the `p`-free part of `n` divides `p - 1`. -/
theorem ordCompl_dvd_sub_one_of_dvd_homogeneousCyclotomic (hp : p.Prime) {a b : ℤ}
    (hb : ¬(p : ℤ) ∣ b) {n : ℕ} (h : (p : ℤ) ∣ homogeneousCyclotomic n a b) :
    ordCompl[p] n ∣ p - 1 := by
  have := Fact.mk hp
  have hn := ne_zero_of_dvd_homogeneousCyclotomic (Nat.prime_iff_prime_int.1 hp).not_isUnit h
  -- The `p`-free part of `n` is the order of `a / b` in `(ZMod p)ˣ`.
  rw [hp.dvd_homogeneousCyclotomic_iff_orderOf_eq hb hn] at h
  rw [← h]
  refine ZMod.orderOf_dvd_card_sub_one fun h0 => (Nat.ordCompl_pos p hn).ne' ?_
  rw [← h, h0, orderOf_zero]

/-- Every prime factor `q` of `n` is at most any prime divisor `p ∤ b` of `Φ_n(a, b)`. -/
theorem le_of_dvd_homogeneousCyclotomic_of_prime_of_dvd (hp : p.Prime) {a b : ℤ}
    (hb : ¬(p : ℤ) ∣ b) {n q : ℕ} (h : (p : ℤ) ∣ homogeneousCyclotomic n a b) (hq : q.Prime)
    (hqn : q ∣ n) : q ≤ p := by
  rcases eq_or_ne q p with rfl | hqp
  · rfl
  -- For `q ≠ p`, `q` divides the `p`-free part of `n`, which divides `p - 1`.
  have hpq : ¬p ∣ q := fun hpq => hqp ((Nat.prime_dvd_prime_iff_eq hp hq).1 hpq).symm
  have := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt)
    ((Nat.dvd_ordCompl_of_dvd_not_dvd hqn hpq).trans
      (hp.ordCompl_dvd_sub_one_of_dvd_homogeneousCyclotomic hb h))
  omega

end Nat.Prime

/-- A prime divisor of `Φ_n(a, b)` for coprime natural bases divides neither base. -/
theorem Nat.Coprime.not_dvd_mul_of_dvd_homogeneousCyclotomic {a b n p : ℕ} (hab : a.Coprime b)
    (hp : p.Prime) (h : (p : ℤ) ∣ homogeneousCyclotomic n (a : ℤ) b) : ¬p ∣ a * b := by
  have hn := ne_zero_of_dvd_homogeneousCyclotomic (Nat.prime_iff_prime_int.1 hp).not_isUnit h
  -- `p` divides `a ^ n - b ^ n`, so dividing one base forces it to divide the other.
  have hdvd : (p : ℤ) ∣ ((a ^ n : ℕ) : ℤ) - ((b ^ n : ℕ) : ℤ) := by
    push_cast
    exact h.trans (homogeneousCyclotomic_dvd_pow_sub_pow dvd_rfl _ _)
  intro hmul
  refine hp.not_dvd_one (hab.gcd_eq_one ▸ ?_)
  rcases hp.dvd_mul.1 hmul with ha | hb
  · have hbn := (dvd_sub_right (Int.natCast_dvd_natCast.2 (dvd_pow ha hn))).1 hdvd
    exact Nat.dvd_gcd ha (hp.dvd_of_dvd_pow (Int.natCast_dvd_natCast.1 hbn))
  · have han := (dvd_sub_left (Int.natCast_dvd_natCast.2 (dvd_pow hb hn))).1 hdvd
    exact Nat.dvd_gcd (hp.dvd_of_dvd_pow (Int.natCast_dvd_natCast.1 han)) hb

namespace Nat.Prime

variable {p : ℕ}

/-- **Primitive prime divisors via cyclotomic values.** For coprime natural bases `b ≤ a` and
`0 < n`, a prime `p` is a primitive prime divisor of `a ^ n - b ^ n` iff `p ∣ Φ_n(a, b)` and
`p ∤ n`. -/
theorem primitive_divisor_iff_dvd_homogeneousCyclotomic (hp : p.Prime) {a b n : ℕ}
    (hab : a.Coprime b) (hba : b ≤ a) (hn : 0 < n) :
    (p ∣ a ^ n - b ^ n ∧ ∀ k, 0 < k → k < n → ¬p ∣ a ^ k - b ^ k) ↔
      (p : ℤ) ∣ homogeneousCyclotomic n (a : ℤ) b ∧ ¬p ∣ n := by
  rw [hp.primitive_divisor_iff_orderOf_eq hab hba hn]
  constructor
  · rintro ⟨hprod, hord⟩
    have hb : ¬(p : ℤ) ∣ (b : ℤ) := fun h =>
      hprod (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.1 h) a)
    have hpn : ¬p ∣ n := hord ▸ hp.not_dvd_orderOf_ratio hprod
    refine ⟨(hp.dvd_homogeneousCyclotomic_iff_orderOf_eq hb hn.ne').2 ?_, hpn⟩
    rw [(Nat.ordCompl_eq_self_iff_zero_or_not_dvd n hp).2 (Or.inr hpn)]
    simpa using hord
  · rintro ⟨h, hpn⟩
    have hprod := hab.not_dvd_mul_of_dvd_homogeneousCyclotomic hp h
    have hb : ¬(p : ℤ) ∣ (b : ℤ) := fun h =>
      hprod (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.1 h) a)
    refine ⟨hprod, ?_⟩
    have hord := (hp.dvd_homogeneousCyclotomic_iff_orderOf_eq hb hn.ne').1 h
    rw [(Nat.ordCompl_eq_self_iff_zero_or_not_dvd n hp).2 (Or.inr hpn)] at hord
    simpa using hord

/-- If a prime `p ∤ b` divides `Φ_{p k}(a, b)`, then `a ^ (p k) - b ^ (p k)` is
`Φ_{p k}(a, b) X (a ^ k - b ^ k)` for some `X` prime to `p`. -/
private theorem exists_pow_sub_pow_eq_homogeneousCyclotomic_mul (hp : p.Prime) {a b : ℤ}
    (hb : ¬(p : ℤ) ∣ b) {k : ℕ} (hk : k ≠ 0) (h : (p : ℤ) ∣ homogeneousCyclotomic (p * k) a b) :
    ∃ X : ℤ, ¬(p : ℤ) ∣ X ∧
      a ^ (p * k) - b ^ (p * k) = homogeneousCyclotomic (p * k) a b * X * (a ^ k - b ^ k) := by
  have hn : p * k ≠ 0 := mul_ne_zero hp.ne_zero hk
  have hcompl : ordCompl[p] (p * k) = ordCompl[p] k := by
    simpa using Nat.ordCompl_self_pow_mul k 1 hp
  have hord := (hp.dvd_homogeneousCyclotomic_iff_orderOf_eq hb hn).1 h
  set S := (p * k).divisors \ k.divisors with hS
  have hmem : p * k ∈ S := by
    refine Finset.mem_sdiff.2 ⟨Nat.mem_divisors_self _ hn, fun hk' => ?_⟩
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hk) (Nat.dvd_of_mem_divisors hk')
    have := Nat.mul_le_mul_right k hp.two_le
    omega
  -- `X` is the product of the `Φ_d(a, b)` over the divisors `d ≠ p k` of `p k` not dividing `k`;
  -- each such index has the wrong `p`-free part for `p` to divide `Φ_d(a, b)`.
  refine ⟨∏ d ∈ S.erase (p * k), homogeneousCyclotomic d a b, ?_, ?_⟩
  · rw [(Nat.prime_iff_prime_int.1 hp).dvd_finsetProd_iff]
    rintro ⟨d, hd, hpd⟩
    obtain ⟨hdne, hdS⟩ := Finset.mem_erase.1 hd
    obtain ⟨hdn, hdk⟩ := Finset.mem_sdiff.1 hdS
    have hdvd := Nat.dvd_of_mem_divisors hdn
    have hdord := (hp.dvd_homogeneousCyclotomic_iff_orderOf_eq hb
      (ne_zero_of_dvd_ne_zero hn hdvd)).1 hpd
    rw [hord, hcompl] at hdord
    exact hdne (hp.eq_mul_of_dvd_mul_of_not_dvd_of_ordCompl_eq hdvd
      (fun h => hdk (Nat.mem_divisors.2 ⟨h, hk⟩)) hdord.symm)
  · rw [Finset.mul_prod_erase S (fun d => homogeneousCyclotomic d a b) hmem, hS,
      ← prod_homogeneousCyclotomic_eq_pow_sub_pow (Nat.pos_of_ne_zero hk) a b,
      Finset.prod_sdiff (Nat.divisors_subset_of_dvd hn (dvd_mul_left k p)),
      prod_homogeneousCyclotomic_eq_pow_sub_pow (Nat.pos_of_ne_zero hn)]

/-- **Nonprimitive prime divisors divide a cyclotomic value once.** For natural bases `b < a`, a
prime `p ∤ b` dividing both `n` and `Φ_n(a, b)` divides `Φ_n(a, b)` exactly once, unless
`n = 2`, where `Φ_2(a, b) = a + b` may be a higher power of `2`. -/
theorem multiplicity_homogeneousCyclotomic_eq_one (hp : p.Prime) {a b n : ℕ} (hba : b < a)
    (hb : ¬p ∣ b) (hpn : p ∣ n) (hn2 : n ≠ 2) (h : (p : ℤ) ∣ homogeneousCyclotomic n (a : ℤ) b) :
    multiplicity (p : ℤ) (homogeneousCyclotomic n (a : ℤ) b) = 1 := by
  have := Fact.mk hp
  have hn := ne_zero_of_dvd_homogeneousCyclotomic (Nat.prime_iff_prime_int.1 hp).not_isUnit h
  have hb' : ¬(p : ℤ) ∣ (b : ℤ) := fun h => hb (Int.natCast_dvd_natCast.1 h)
  have hord := (hp.dvd_homogeneousCyclotomic_iff_orderOf_eq hb' hn).1 h
  simp only [Int.cast_natCast] at hord
  -- The ratio `a / b` has positive order, so `p ∤ a` as well.
  have hab : ¬p ∣ a * b := by
    refine fun hmul => (hp.dvd_mul.1 hmul).elim (fun ha => ?_) hb
    rw [(ZMod.natCast_eq_zero_iff a p).2 ha, zero_mul, orderOf_zero] at hord
    exact (Nat.ordCompl_pos p hn).ne' hord.symm
  obtain ⟨k, rfl⟩ := hpn
  have hk : k ≠ 0 := right_ne_zero_of_mul hn
  have hcompl : ordCompl[p] (p * k) = ordCompl[p] k := by
    simpa using Nat.ordCompl_self_pow_mul k 1 hp
  have hdk : orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) ∣ k :=
    hord ▸ hcompl ▸ Nat.ordCompl_dvd k p
  -- At `p = 2` the order is `1`, so `k` is a power of `2`, and it is even since `n ≠ 2`.
  have hexc : ¬(p = 2 ∧ Odd k) := by
    rintro ⟨rfl, hodd⟩
    have h1 := hp.orderOf_ratio_dvd_sub_one hab
    rw [hord, hcompl, (Nat.ordCompl_eq_self_iff_zero_or_not_dvd k hp).2
      (Or.inr hodd.not_two_dvd_nat), Nat.dvd_one] at h1
    exact hn2 (by rw [h1])
  have hval := hp.multiplicity_pow_sub_pow_div_pow_sub_pow_eq_ite hba hab hk hdk
  rw [ite_eq_right hexc] at hval
  -- The natural quotient of the two differences of powers is `Φ_{p k}(a, b) X` with `p ∤ X`.
  obtain ⟨X, hX, hsplit⟩ := hp.exists_pow_sub_pow_eq_homogeneousCyclotomic_mul hb' hk h
  have hsub : ((a ^ k - b ^ k : ℕ) : ℤ) ≠ 0 := by
    have := Nat.pow_lt_pow_left hba hk
    omega
  have hquot : (((a ^ (p * k) - b ^ (p * k)) / (a ^ k - b ^ k) : ℕ) : ℤ) =
      homogeneousCyclotomic (p * k) (a : ℤ) b * X := by
    refine mul_right_cancel₀ hsub ?_
    rw [← Nat.cast_mul, Nat.div_mul_cancel
      (Nat.pow_sub_pow_dvd_pow_sub_pow a b (dvd_mul_left k p))]
    push_cast [Nat.pow_le_pow_left hba.le]
    exact hsplit
  have hfin : FiniteMultiplicity (p : ℤ) (homogeneousCyclotomic (p * k) (a : ℤ) b * X) := by
    refine Int.finiteMultiplicity_iff.2 ⟨by simpa using hp.ne_one, fun h0 => ?_⟩
    have hpos : (b : ℤ) ^ (p * k) < (a : ℤ) ^ (p * k) :=
      pow_lt_pow_left₀ (by exact_mod_cast hba) (Int.natCast_nonneg b) hn
    rw [← sub_pos, hsplit, h0, zero_mul] at hpos
    exact hpos.false
  rwa [← Int.natCast_multiplicity, hquot,
    _root_.multiplicity_mul (Nat.prime_iff_prime_int.1 hp) hfin,
    multiplicity_eq_zero_of_not_dvd hX, add_zero] at hval

/-- **Nonprimitive prime divisors of a cyclotomic value.** For coprime natural bases `b < a` and
`n ≠ 2`, a prime `p` dividing `Φ_n(a, b)` and some `a ^ k - b ^ k` with `0 < k < n` divides `n`,
is at least every prime factor of `n`, and divides `Φ_n(a, b)` exactly once. -/
theorem multiplicity_homogeneousCyclotomic_of_not_primitive (hp : p.Prime) {a b n : ℕ}
    (hab : a.Coprime b) (hba : b < a) (hn2 : n ≠ 2)
    (h : (p : ℤ) ∣ homogeneousCyclotomic n (a : ℤ) b)
    (hk : ∃ k, 0 < k ∧ k < n ∧ p ∣ a ^ k - b ^ k) :
    p ∣ n ∧ (∀ q : ℕ, q.Prime → q ∣ n → q ≤ p) ∧
      multiplicity (p : ℤ) (homogeneousCyclotomic n (a : ℤ) b) = 1 := by
  have hprod := hab.not_dvd_mul_of_dvd_homogeneousCyclotomic hp h
  have hb : ¬p ∣ b := fun hb => hprod (dvd_mul_of_dvd_right hb a)
  have hb' : ¬(p : ℤ) ∣ (b : ℤ) := fun h => hb (Int.natCast_dvd_natCast.1 h)
  -- A prime divisor of `Φ_n(a, b)` not dividing `n` would be primitive.
  have hpn : p ∣ n := by
    by_contra hpn
    obtain ⟨k, hk0, hkn, hpk⟩ := hk
    exact ((hp.primitive_divisor_iff_dvd_homogeneousCyclotomic hab hba.le
      (hk0.trans hkn)).2 ⟨h, hpn⟩).2 k hk0 hkn hpk
  exact ⟨hpn, fun q hq hqn => hp.le_of_dvd_homogeneousCyclotomic_of_prime_of_dvd hb' h hq hqn,
    hp.multiplicity_homogeneousCyclotomic_eq_one hba hb hpn hn2 h⟩

end Nat.Prime

namespace Nat.Coprime

/-- **Cyclotomic values without primitive prime divisors.** For coprime natural bases `b < a` and
`n ≠ 2`, if `a ^ n - b ^ n` has no primitive prime divisor, then `Φ_n(a, b)` is `1` or a prime
`p` dividing `n` that is at least every prime factor of `n`. At `n = 2` this fails:
`Φ_2(3, 1) = 4`. -/
theorem homogeneousCyclotomic_eq_one_or_eq_prime_of_not_exists_prime_dvd_pow_sub_pow {a b n : ℕ}
    (hab : a.Coprime b) (hba : b < a) (hn2 : n ≠ 2)
    (h : ¬∃ p : ℕ, p.Prime ∧ p ∣ a ^ n - b ^ n ∧ ∀ k, 0 < k → k < n → ¬p ∣ a ^ k - b ^ k) :
    homogeneousCyclotomic n (a : ℤ) b = 1 ∨ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧
      (∀ q : ℕ, q.Prime → q ∣ n → q ≤ p) ∧ homogeneousCyclotomic n (a : ℤ) b = p := by
  have hpos : 0 < homogeneousCyclotomic n (a : ℤ) b :=
    homogeneousCyclotomic_pos (Int.natCast_nonneg b) (by exact_mod_cast hba) n
  set N := (homogeneousCyclotomic n (a : ℤ) b).natAbs
  have hN : (N : ℤ) = homogeneousCyclotomic n (a : ℤ) b := Int.natAbs_of_nonneg hpos.le
  rcases eq_or_ne N 1 with h1 | h1
  · exact Or.inl (by rw [← hN, h1, Nat.cast_one])
  -- Every prime divisor of `Φ_n(a, b)` is nonprimitive, hence divides `n`.
  have hdvd : ∀ q, q.Prime → q ∣ N →
      (q : ℤ) ∣ homogeneousCyclotomic n (a : ℤ) b ∧ ¬(q : ℤ) ∣ b ∧ q ∣ n := by
    intro q hq hqN
    have hqΦ : (q : ℤ) ∣ homogeneousCyclotomic n (a : ℤ) b := hN ▸ Int.natCast_dvd_natCast.2 hqN
    have hprod := hab.not_dvd_mul_of_dvd_homogeneousCyclotomic hq hqΦ
    refine ⟨hqΦ, fun hqb => hprod (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.1 hqb) a),
      by_contra fun hqn => h ⟨q, hq, ?_⟩⟩
    exact (hq.primitive_divisor_iff_dvd_homogeneousCyclotomic hab hba.le
      (Nat.pos_of_ne_zero (ne_zero_of_dvd_homogeneousCyclotomic
        (Nat.prime_iff_prime_int.1 hq).not_isUnit hqΦ))).2 ⟨hqΦ, hqn⟩
  obtain ⟨p, hp, hpN⟩ := Nat.exists_prime_and_dvd h1
  obtain ⟨hpΦ, hpb, hpn⟩ := hdvd p hp hpN
  -- Two prime divisors of `Φ_n(a, b)` each bound the other, so `p` is the only one.
  have huniq : ∀ {q}, q.Prime → q ∣ N → q = p := fun hq hqN =>
    have ⟨hqΦ, hqb, hqn⟩ := hdvd _ hq hqN
    le_antisymm (hp.le_of_dvd_homogeneousCyclotomic_of_prime_of_dvd hpb hpΦ hq hqn)
      (hq.le_of_dvd_homogeneousCyclotomic_of_prime_of_dvd hqb hqΦ hp hpn)
  have hpow : N = p ^ N.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd (Int.natAbs_ne_zero.2 hpos.ne') huniq
  have hmul := hp.multiplicity_homogeneousCyclotomic_eq_one hba
    (fun hpb' => hpb (Int.natCast_dvd_natCast.2 hpb')) hpn hn2 hpΦ
  rw [← hN, Int.natCast_multiplicity, hpow,
    multiplicity_pow_self_of_prime (Nat.prime_iff.1 hp)] at hmul
  refine Or.inr ⟨p, hp, hpn, fun q hq hqn => ?_, ?_⟩
  · exact hp.le_of_dvd_homogeneousCyclotomic_of_prime_of_dvd hpb hpΦ hq hqn
  · rw [← hN, hpow, hmul, pow_one]

end Nat.Coprime
