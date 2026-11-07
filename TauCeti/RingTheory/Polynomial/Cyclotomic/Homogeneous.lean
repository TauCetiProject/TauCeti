/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
public import TauCeti.RingTheory.Coprime.Lemmas

import TauCeti.Algebra.Polynomial.Homogenize

/-!
# Homogeneous cyclotomic values

For `n : ℕ` and `a b` in a commutative ring `R`, the homogeneous cyclotomic value
`Φ_n(a, b) = ∑ cᵢ aⁱ b ^ (φ(n) - i)` is the value at `(a, b)` of the homogenization of degree
`φ(n)` of the cyclotomic polynomial `Φ_n = ∑ cᵢ Xⁱ`. Thus `Φ_n(a, 1) = Φ_n(a)`, and in a field
`Φ_n(a, b) = b ^ φ(n) Φ_n(a / b)` for `b ≠ 0`. The first argument is the base:
`Φ_1(a, b) = a - b`.

These are the "algebraic primitive factors" of `a ^ n - b ^ n`: homogenizing
`∏_{d ∣ n} Φ_d = X ^ n - 1` gives `a ^ n - b ^ n = ∏_{d ∣ n} Φ_d(a, b)` for `n > 0`. This is the
starting point for the arithmetic of the numbers `a ^ n - b ^ n`, in particular for the study of
their primitive prime divisors (the Bang–Zsigmondy theorem): a prime dividing `a ^ n - b ^ n` but
no `a ^ k - b ^ k` with `0 < k < n` divides `Φ_n(a, b)`.

## Main definitions

* `TauCeti.homogeneousCyclotomic n a b`: the homogeneous cyclotomic value `Φ_n(a, b)`.

## Main results

* `TauCeti.homogeneousCyclotomic_eq_sum`: `Φ_n(a, b) = ∑_{i ≤ φ(n)} cᵢ aⁱ b ^ (φ(n) - i)`.
* `TauCeti.map_homogeneousCyclotomic`: ring homomorphisms commute with `Φ_n(·, ·)`.
* `TauCeti.homogeneousCyclotomic_one_right`, `TauCeti.homogeneousCyclotomic_eq_eval_div_mul_pow`:
  `Φ_n(a, 1) = Φ_n(a)`, and `Φ_n(a, b) = Φ_n(a / b) b ^ φ(n)` in a field when `b ≠ 0`.
* Closed forms at `n = 0, 1, 2, 3, 6`, at primes, `Φ_p(a, b) = ∑_{i < p} aⁱ b ^ (p - 1 - i)`, and
  at prime powers, `Φ_{p ^ (e + 1)}(a, b) = Φ_p(a ^ p ^ e, b ^ p ^ e)`.
* `TauCeti.homogeneousCyclotomic_zero_right`, `TauCeti.homogeneousCyclotomic_zero_left`: the values
  `Φ_n(a, 0) = a ^ φ(n)` and, for `n ≠ 1`, `Φ_n(0, b) = b ^ φ(n)`.
* `TauCeti.prod_homogeneousCyclotomic_eq_pow_sub_pow`: `∏_{d ∣ n} Φ_d(a, b) = a ^ n - b ^ n` for
  `0 < n`, with the divisibilities `Φ_d(a, b) ∣ a ^ n - b ^ n` and
  `(a ^ d - b ^ d) Φ_n(a, b) ∣ a ^ n - b ^ n` for proper divisors `d` of `n`.
* `TauCeti.homogeneousCyclotomic_pos`: in an ordered ring, `0 < Φ_n(a, b)` whenever `0 ≤ b < a`.
* `IsCoprime.mul_homogeneousCyclotomic`: for coprime `a` and `b` and `n ≠ 0`, `Φ_n(a, b)` is
  coprime to `a b`.

## References

* G. D. Birkhoff and H. S. Vandiver, *On the integral divisors of `a ^ n - b ^ n`*, Ann. of
  Math. (2) 5 (1904), 173–180, p. 176 (the primitive factor) and Theorem I, p. 174.
* Ö. Avcı, *Large Zsigmondy primes*, arXiv:2011.06136v2 (2023), Definition 2.4 and
  Corollary 2.6.
-/

public section

open Polynomial Finset

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- The homogeneous cyclotomic value `Φ_n(a, b) = ∑ cᵢ aⁱ b ^ (φ(n) - i)`, where `Φ_n = ∑ cᵢ Xⁱ` is
the `n`-th cyclotomic polynomial: the value at `(a, b)` of the homogenization of `Φ_n` of degree
`φ(n)`. The first argument is the base, so `Φ_1(a, b) = a - b`, and `Φ_0(a, b) = 1`. -/
noncomputable def homogeneousCyclotomic (n : ℕ) (a b : R) : R :=
  MvPolynomial.eval ![a, b] ((cyclotomic n R).homogenize n.totient)

/-- The homogeneous cyclotomic value as a sum of monomials:
`Φ_n(a, b) = ∑_{i ≤ φ(n)} cᵢ aⁱ b ^ (φ(n) - i)`, where `cᵢ` are the coefficients of `Φ_n`. -/
theorem homogeneousCyclotomic_eq_sum (n : ℕ) (a b : R) :
    homogeneousCyclotomic n a b =
      ∑ i ∈ range (n.totient + 1), (cyclotomic n R).coeff i * (a ^ i * b ^ (n.totient - i)) := by
  have h := aeval_homogenize_eq_sum (cyclotomic n R) n.totient a b
  rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa [homogeneousCyclotomic, MvPolynomial.coe_aeval_eq_eval] using h

/-- Ring homomorphisms commute with homogeneous cyclotomic values. -/
@[simp]
theorem map_homogeneousCyclotomic {S : Type*} [CommRing S] (f : R →+* S) (n : ℕ) (a b : R) :
    f (homogeneousCyclotomic n a b) = homogeneousCyclotomic n (f a) (f b) := by
  rw [homogeneousCyclotomic_eq_sum, homogeneousCyclotomic_eq_sum, ← map_cyclotomic n f]
  simp only [map_sum, map_mul, map_pow, coeff_map]

/-- At `b = 1` the homogeneous cyclotomic value is the value of the cyclotomic polynomial:
`Φ_n(a, 1) = Φ_n(a)`. -/
@[simp]
theorem homogeneousCyclotomic_one_right (n : ℕ) (a : R) :
    homogeneousCyclotomic n a 1 = (cyclotomic n R).eval a := by
  rw [homogeneousCyclotomic_eq_sum, eval_eq_sum_range' (Nat.lt_succ_of_le natDegree_cyclotomic_le)]
  simp

/-- In a field, for `b ≠ 0`, the homogeneous cyclotomic value is
`Φ_n(a, b) = Φ_n(a / b) b ^ φ(n)`. -/
theorem homogeneousCyclotomic_eq_eval_div_mul_pow {K : Type*} [Field K] (n : ℕ) (a : K) {b : K}
    (hb : b ≠ 0) :
    homogeneousCyclotomic n a b = (cyclotomic n K).eval (a / b) * b ^ n.totient :=
  eval_homogenize natDegree_cyclotomic_le ![a, b] hb

/-! ### Closed forms -/

/-- `Φ_0(a, b) = 1`, since `Φ_0 = 1` and `φ(0) = 0`. -/
@[simp]
theorem homogeneousCyclotomic_zero (a b : R) : homogeneousCyclotomic 0 a b = 1 := by
  simp [homogeneousCyclotomic]

/-- `Φ_1(a, b) = a - b`. -/
@[simp]
theorem homogeneousCyclotomic_one (a b : R) : homogeneousCyclotomic 1 a b = a - b := by
  simp [homogeneousCyclotomic]

/-- `Φ_2(a, b) = a + b`. -/
@[simp]
theorem homogeneousCyclotomic_two (a b : R) : homogeneousCyclotomic 2 a b = a + b := by
  simp [homogeneousCyclotomic, cyclotomic_two]

/-- `Φ_3(a, b) = a ^ 2 + a b + b ^ 2`. -/
theorem homogeneousCyclotomic_three (a b : R) :
    homogeneousCyclotomic 3 a b = a ^ 2 + a * b + b ^ 2 := by
  simp [homogeneousCyclotomic, cyclotomic_three, Nat.totient_prime Nat.prime_three]

/-- `Φ_6(a, b) = a ^ 2 - a b + b ^ 2`. -/
theorem homogeneousCyclotomic_six (a b : R) :
    homogeneousCyclotomic 6 a b = a ^ 2 - a * b + b ^ 2 := by
  have h6 : Nat.totient 6 = 2 := by decide
  simp [homogeneousCyclotomic, h6]

/-- At a prime power `p ^ (e + 1)` the homogeneous cyclotomic value is the geometric sum
`Φ_{p ^ (e + 1)}(a, b) = ∑_{i < p} (a ^ p ^ e) ^ i (b ^ p ^ e) ^ (p - 1 - i)`. -/
theorem homogeneousCyclotomic_prime_pow_eq_sum {p : ℕ} (hp : p.Prime) (e : ℕ) (a b : R) :
    homogeneousCyclotomic (p ^ (e + 1)) a b =
      ∑ i ∈ range p, (a ^ p ^ e) ^ i * (b ^ p ^ e) ^ (p - 1 - i) := by
  have hle : ∀ i ∈ range p, p ^ e * i ≤ p ^ e * (p - 1) := fun i hi =>
    Nat.mul_le_mul_left _ (Nat.le_sub_one_of_lt (mem_range.1 hi))
  rw [homogeneousCyclotomic, cyclotomic_prime_pow_eq_geom_sum hp, Nat.totient_prime_pow_succ hp,
    homogenize_finsetSum, map_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [← pow_mul, homogenize_X_pow (hle i hi), ← Nat.mul_sub, map_mul, map_pow, map_pow]
  simp [pow_mul]

/-- At a prime `p` the homogeneous cyclotomic value is the geometric sum
`Φ_p(a, b) = ∑_{i < p} aⁱ b ^ (p - 1 - i)`. -/
theorem homogeneousCyclotomic_prime_eq_sum {p : ℕ} (hp : p.Prime) (a b : R) :
    homogeneousCyclotomic p a b = ∑ i ∈ range p, a ^ i * b ^ (p - 1 - i) := by
  simpa using homogeneousCyclotomic_prime_pow_eq_sum hp 0 a b

/-- At a prime power, `Φ_{p ^ (e + 1)}(a, b) = Φ_p(a ^ p ^ e, b ^ p ^ e)`. -/
theorem homogeneousCyclotomic_prime_pow_succ {p : ℕ} (hp : p.Prime) (e : ℕ) (a b : R) :
    homogeneousCyclotomic (p ^ (e + 1)) a b = homogeneousCyclotomic p (a ^ p ^ e) (b ^ p ^ e) := by
  rw [homogeneousCyclotomic_prime_pow_eq_sum hp, homogeneousCyclotomic_prime_eq_sum hp]

/-! ### Values at zero -/

/-- Since `Φ_n` is monic of degree `φ(n)`, only its leading term survives at `b = 0`:
`Φ_n(a, 0) = a ^ φ(n)`. -/
@[simp]
theorem homogeneousCyclotomic_zero_right (n : ℕ) (a : R) :
    homogeneousCyclotomic n a 0 = a ^ n.totient := by
  nontriviality R
  rw [homogeneousCyclotomic_eq_sum, sum_eq_single n.totient]
  · rw [← natDegree_cyclotomic n R, (cyclotomic.monic n R).coeff_natDegree]
    simp
  · intro i hi hne
    have : 0 < n.totient - i := by
      have := mem_range.1 hi
      omega
    simp [zero_pow this.ne']
  · simp

/-- Since the constant coefficient of `Φ_n` is `1` for `n ≠ 1`, `Φ_n(0, b) = b ^ φ(n)`. At `n = 1`
instead `Φ_1(0, b) = -b`. -/
theorem homogeneousCyclotomic_zero_left {n : ℕ} (hn : n ≠ 1) (b : R) :
    homogeneousCyclotomic n 0 b = b ^ n.totient := by
  have hcoeff : (cyclotomic n R).coeff 0 = 1 := by
    rcases Nat.lt_or_ge n 1 with h | h
    · obtain rfl : n = 0 := by omega
      simp
    · exact cyclotomic_coeff_zero R (by omega)
  rw [homogeneousCyclotomic_eq_sum, sum_eq_single 0]
  · simp [hcoeff]
  · intro i _ hi
    simp [zero_pow hi]
  · simp

/-! ### The factorization of `a ^ n - b ^ n` -/

/-- **The factorization of `a ^ n - b ^ n`** into homogeneous cyclotomic values:
`∏_{d ∣ n} Φ_d(a, b) = a ^ n - b ^ n` for `0 < n`. This is the homogenization of
`Polynomial.prod_cyclotomic_eq_X_pow_sub_one`. -/
theorem prod_homogeneousCyclotomic_eq_pow_sub_pow {n : ℕ} (hn : 0 < n) (a b : R) :
    ∏ d ∈ n.divisors, homogeneousCyclotomic d a b = a ^ n - b ^ n := by
  have h := homogenize_finsetProd (s := n.divisors) (p := fun d => cyclotomic d R)
    (n := Nat.totient) fun d _ => natDegree_cyclotomic_le
  rw [Nat.sum_totient, prod_cyclotomic_eq_X_pow_sub_one hn, homogenize_sub,
    homogenize_X_pow le_rfl, homogenize_one] at h
  simp only [homogeneousCyclotomic, ← map_prod, ← h]
  simp

/-- For `d ∣ n` with `0 < n`, the homogeneous cyclotomic value `Φ_d(a, b)` divides
`a ^ n - b ^ n`. -/
theorem homogeneousCyclotomic_dvd_pow_sub_pow {d n : ℕ} (hn : 0 < n) (hd : d ∣ n) (a b : R) :
    homogeneousCyclotomic d a b ∣ a ^ n - b ^ n := by
  rw [← prod_homogeneousCyclotomic_eq_pow_sub_pow hn]
  exact dvd_prod_of_mem _ (Nat.mem_divisors.2 ⟨hd, hn.ne'⟩)

/-- For a proper divisor `d` of `n`, the factors `a ^ d - b ^ d` and `Φ_n(a, b)` of
`a ^ n - b ^ n` are complementary: `(a ^ d - b ^ d) Φ_n(a, b) ∣ a ^ n - b ^ n`. -/
theorem pow_sub_pow_mul_homogeneousCyclotomic_dvd_pow_sub_pow {d n : ℕ} (hd : d ∣ n)
    (hdn : d < n) (a b : R) :
    (a ^ d - b ^ d) * homogeneousCyclotomic n a b ∣ a ^ n - b ^ n := by
  have hn : 0 < n := (Nat.zero_le d).trans_lt hdn
  have hnd : n ∉ d.divisors := fun h => hdn.not_ge (Nat.divisor_le h)
  rw [← prod_homogeneousCyclotomic_eq_pow_sub_pow (Nat.pos_of_dvd_of_pos hd hn),
    ← prod_homogeneousCyclotomic_eq_pow_sub_pow hn, mul_comm,
    ← prod_insert (f := fun k => homogeneousCyclotomic k a b) hnd]
  exact prod_dvd_prod_of_subset _ _ _ (insert_subset_iff.2
    ⟨Nat.mem_divisors_self n hn.ne', Nat.divisors_subset_of_dvd hn.ne' hd⟩)

/-! ### Positivity -/

/-- In an ordered commutative ring, the homogeneous cyclotomic value is positive when
`0 ≤ b < a`. -/
theorem homogeneousCyclotomic_pos [LinearOrder R] [IsStrictOrderedRing R] {a b : R} (hb : 0 ≤ b)
    (hba : b < a) (n : ℕ) : 0 < homogeneousCyclotomic n a b := by
  -- Strong induction: `Φ_n(a, b)` times the positive `Φ_d(a, b)`, `d` a proper divisor of `n`,
  -- is the positive `a ^ n - b ^ n`.
  induction n using Nat.strong_induction_on with | _ n ih
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h := prod_homogeneousCyclotomic_eq_pow_sub_pow hn a b
  rw [← Nat.cons_self_properDivisors hn.ne', prod_cons] at h
  refine pos_of_mul_pos_left (h ▸ sub_pos.2 (pow_lt_pow_left₀ hba hb hn.ne')) ?_
  exact (prod_pos fun d hd => ih d (Nat.mem_properDivisors.1 hd).2).le

end TauCeti

/-- For coprime `a` and `b` and `n ≠ 0`, the homogeneous cyclotomic value `Φ_n(a, b)` is coprime to
`a b`, since it divides `a ^ n - b ^ n`. In particular no prime divisor of `Φ_n(a, b)` divides `a`
or `b`. -/
theorem IsCoprime.mul_homogeneousCyclotomic {R : Type*} [CommRing R] {a b : R} (h : IsCoprime a b)
    {n : ℕ} (hn : n ≠ 0) : IsCoprime (a * b) (TauCeti.homogeneousCyclotomic n a b) :=
  (h.mul_pow_sub_pow hn).of_isCoprime_of_dvd_right
    (TauCeti.homogeneousCyclotomic_dvd_pow_sub_pow (Nat.pos_of_ne_zero hn) dvd_rfl a b)
