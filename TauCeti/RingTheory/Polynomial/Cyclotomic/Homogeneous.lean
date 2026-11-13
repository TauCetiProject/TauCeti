/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import TauCeti.Algebra.Polynomial.Homogenize
import TauCeti.RingTheory.Polynomial.Cyclotomic.Reflect

/-!
# Homogeneous cyclotomic values

For a commutative ring `R`, `n : ℕ` and `a b : R`, the homogeneous cyclotomic value
`TauCeti.homogeneousCyclotomic n a b`, written `Φ_n(a, b)`, is the value at `(a, b)` of the
homogenization of `Polynomial.cyclotomic n R` at its degree `φ(n)`:
`Φ_n(a, b) = ∑_{k + l = φ(n)} c_k a ^ k b ^ l`, where `c_k` are the coefficients of `Φ_n`. The
first argument carries the coefficient index, so `Φ_1(a, b) = a - b`, and `Φ_n(a, b)` is
`b ^ φ(n) Φ_n(a / b)` whenever `b` is invertible in a field.

These values are the primitive factors of differences of powers:
`a ^ n - b ^ n = ∏_{d ∣ n} Φ_d(a, b)` for `n > 0`. Over the integers they are the algebraic
primitive parts of `a ^ n - b ^ n` studied by Birkhoff and Vandiver, whose prime divisors
control the primitive prime divisors of `a ^ n - b ^ n` (the Bang–Zsigmondy theorem).

## Main results

* `TauCeti.homogeneousCyclotomic_eq_sum`: `Φ_n(a, b)` as the sum `∑_{k + l = φ(n)} c_k a^k b^l`.
* `TauCeti.homogeneousCyclotomic_one_right`, `TauCeti.homogeneousCyclotomic_eq_eval_div_mul_pow`:
  `Φ_n(a, 1) = Φ_n(a)`, and `Φ_n(a, b) = Φ_n(a / b) b ^ φ(n)` for `b ≠ 0` in a field.
* `RingHom.map_homogeneousCyclotomic`, `Int.cast_homogeneousCyclotomic`: ring homomorphisms,
  and in particular integer casts, commute with `Φ_n(·, ·)`.
* `TauCeti.homogeneousCyclotomic_mul_mul`: `Φ_n(c a, c b) = c ^ φ(n) Φ_n(a, b)`.
* `TauCeti.homogeneousCyclotomic_zero`, `_one`, `_two`, `_three`, `_six`, `_prime`,
  `_prime_pow`: closed forms, including `Φ_p(a, b) = ∑_{i < p} a ^ i b ^ (p - 1 - i)` and
  `Φ_{p ^ (e + 1)}(a, b) = Φ_p(a ^ p ^ e, b ^ p ^ e)` for a prime `p`.
* `TauCeti.ne_zero_of_dvd_homogeneousCyclotomic`: a nonunit divides `Φ_n(a, b)` only if `n ≠ 0`.
* `TauCeti.homogeneousCyclotomic_mul_prime_of_dvd`,
  `TauCeti.homogeneousCyclotomic_mul_prime_mul_homogeneousCyclotomic`: for a prime `p`,
  `Φ_{n p}(a, b) = Φ_n(a ^ p, b ^ p)` if `p ∣ n`, and `Φ_{n p}(a, b) Φ_n(a, b) = Φ_n(a ^ p, b ^ p)`
  if `p ∤ n`.
* `TauCeti.homogeneousCyclotomic_prime_pow_mul`,
  `TauCeti.homogeneousCyclotomic_prime_pow_mul_mul_homogeneousCyclotomic`: the iterated forms
  `Φ_{p ^ (e + 1) m}(a, b) = Φ_{p m}(A, B)` and, for `p ∤ m`,
  `Φ_{p ^ (e + 1) m}(a, b) Φ_m(A, B) = Φ_m(A ^ p, B ^ p)`, with `A = a ^ p ^ e`, `B = b ^ p ^ e`.
* `TauCeti.homogeneousCyclotomic_comm`: `Φ_n(b, a) = Φ_n(a, b)` for `n ≠ 1`.
* `TauCeti.homogeneousCyclotomic_one_anticomm`: `Φ_1(b, a) = -Φ_1(a, b)`.
* `TauCeti.homogeneousCyclotomic_zero_right`, `TauCeti.homogeneousCyclotomic_zero_left`:
  `Φ_n(a, 0) = a ^ φ(n)`, and `Φ_n(0, b) = b ^ φ(n)` for `n ≠ 1`.
* `TauCeti.prod_homogeneousCyclotomic_eq_pow_sub_pow`: `∏_{d ∣ n} Φ_d(a, b) = a ^ n - b ^ n` for
  `0 < n`, and `TauCeti.homogeneousCyclotomic_dvd_pow_sub_pow`: `Φ_d(a, b) ∣ a ^ n - b ^ n` for
  `d ∣ n`.
* `TauCeti.homogeneousCyclotomic_mul_prod_properDivisors`:
  `Φ_n(a, b) ∏_{d ∣ n, d < n} Φ_d(a, b) = a ^ n - b ^ n` for `0 < n`.
* `TauCeti.homogeneousCyclotomic_pos`: in an ordered ring, `0 < Φ_n(a, b)` for `0 ≤ b < a`.

## References

* [G. D. Birkhoff and H. S. Vandiver, *On the integral divisors of `a ^ n - b ^ n`*,
  Ann. of Math. (2) 5 (1904), 173–180], p. 176, the primitive factor `F(n)`.
* [Ö. Avcı, *Large Zsigmondy primes*, arXiv:2011.06136v2 (2023)], Definition 2.4,
  Corollary 2.6, Lemma 2.9 and Corollary 2.10 (the expansion identities).
* [M. Roitman, *On Zsigmondy primes*, Proc. Amer. Math. Soc. 125 (1997), 1913–1919], p. 1913,
  positivity of cyclotomic values; p. 1914, proof of Lemma 1, the iterated expansion at `b = 1`.
-/

public section

open Polynomial

namespace TauCeti

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The **homogeneous cyclotomic value** `Φ_n(a, b) = ∑_{k + l = φ(n)} c_k a ^ k b ^ l`, where
`c_k` are the coefficients of the cyclotomic polynomial `Φ_n`: the value at `![a, b]` of the
homogenization of `Polynomial.cyclotomic n R` at its degree `φ(n)`. The first argument is the
base, so `Φ_1(a, b) = a - b`, and `Φ_0(a, b) = 1`. -/
noncomputable def homogeneousCyclotomic (n : ℕ) (a b : R) : R :=
  MvPolynomial.eval ![a, b] ((cyclotomic n R).homogenize n.totient)

/-- `Φ_n(a, b)` is the value at `![a, b]` of the homogenization of `Φ_n` at degree `φ(n)`. -/
theorem homogeneousCyclotomic_def (n : ℕ) (a b : R) :
    homogeneousCyclotomic n a b =
      MvPolynomial.eval ![a, b] ((cyclotomic n R).homogenize n.totient) :=
  (rfl)

/-- `Φ_n(a, b)` is the sum of the terms `c_k a ^ k b ^ l` over `k + l = φ(n)`, where `c_k` are
the coefficients of `Φ_n`. -/
theorem homogeneousCyclotomic_eq_sum (n : ℕ) (a b : R) :
    homogeneousCyclotomic n a b =
      ∑ kl ∈ Finset.antidiagonal n.totient,
        (cyclotomic n R).coeff kl.1 * (a ^ kl.1 * b ^ kl.2) := by
  rw [homogeneousCyclotomic_def, ← MvPolynomial.aeval_eq_eval, aeval_homogenize_eq_sum]
  simp

/-! ### Evaluation and transport -/

/-- `Φ_n(a, 1)` is the value of the cyclotomic polynomial `Φ_n` at `a`. -/
@[simp]
theorem homogeneousCyclotomic_one_right (n : ℕ) (a : R) :
    homogeneousCyclotomic n a 1 = (cyclotomic n R).eval a := by
  rw [homogeneousCyclotomic_def, ← MvPolynomial.aeval_eq_eval,
    aeval_homogenize_of_eq_one natDegree_cyclotomic_le _ rfl]
  simp

/-- For `b ≠ 0` in a field, `Φ_n(a, b) = Φ_n(a / b) b ^ φ(n)`. -/
theorem homogeneousCyclotomic_eq_eval_div_mul_pow {K : Type*} [Field K] (n : ℕ) (a : K) {b : K}
    (hb : b ≠ 0) :
    homogeneousCyclotomic n a b = (cyclotomic n K).eval (a / b) * b ^ n.totient := by
  rw [homogeneousCyclotomic_def, eval_homogenize natDegree_cyclotomic_le _ hb]
  simp

/-- Ring homomorphisms commute with homogeneous cyclotomic values. -/
@[simp]
theorem _root_.RingHom.map_homogeneousCyclotomic (f : R →+* S) (n : ℕ) (a b : R) :
    f (homogeneousCyclotomic n a b) = homogeneousCyclotomic n (f a) (f b) := by
  rw [homogeneousCyclotomic_def, homogeneousCyclotomic_def, MvPolynomial.map_eval,
    ← homogenize_map, map_cyclotomic]
  congr 2
  ext i
  fin_cases i <;> simp

/-- The cast of an integer homogeneous cyclotomic value is the homogeneous cyclotomic value of the
casts. -/
@[simp, norm_cast]
theorem _root_.Int.cast_homogeneousCyclotomic (n : ℕ) (a b : ℤ) :
    ((homogeneousCyclotomic n a b : ℤ) : R) = homogeneousCyclotomic n (a : R) (b : R) :=
  (Int.castRingHom R).map_homogeneousCyclotomic n a b

/-- `Φ_n` is homogeneous of degree `φ(n)`: `Φ_n(c a, c b) = c ^ φ(n) Φ_n(a, b)`. -/
theorem homogeneousCyclotomic_mul_mul (n : ℕ) (c a b : R) :
    homogeneousCyclotomic n (c * a) (c * b) = c ^ n.totient * homogeneousCyclotomic n a b := by
  rw [homogeneousCyclotomic_def, homogeneousCyclotomic_def,
    ← (isHomogeneous_homogenize _).eval_smul]
  simp [Matrix.smul_cons]

/-! ### Expansion identities -/

/-- For a prime `p` dividing `n`, `Φ_{n p}(a, b) = Φ_n(a ^ p, b ^ p)`. -/
theorem homogeneousCyclotomic_mul_prime_of_dvd {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (a b : R) :
    homogeneousCyclotomic (n * p) a b = homogeneousCyclotomic n (a ^ p) (b ^ p) := by
  rw [homogeneousCyclotomic_def, homogeneousCyclotomic_def,
    ← cyclotomic_expand_eq_cyclotomic hp hpn, mul_comm n, Nat.totient_mul_of_dvd hpn,
    homogenize_expand hp.ne_zero, MvPolynomial.eval_expand]
  congr 2
  ext i
  fin_cases i <;> simp

/-- For a prime `p` not dividing `n`, `Φ_{n p}(a, b) Φ_n(a, b) = Φ_n(a ^ p, b ^ p)`. -/
theorem homogeneousCyclotomic_mul_prime_mul_homogeneousCyclotomic {p n : ℕ} (hp : p.Prime)
    (hpn : ¬p ∣ n) (a b : R) :
    homogeneousCyclotomic (n * p) a b * homogeneousCyclotomic n a b =
      homogeneousCyclotomic n (a ^ p) (b ^ p) := by
  have hdeg : (n * p).totient + n.totient = p * n.totient := by
    rw [mul_comm n, Nat.totient_mul_of_prime_of_not_dvd hp hpn, ← Nat.succ_mul,
      Nat.succ_eq_add_one, Nat.sub_add_cancel hp.one_le]
  rw [homogeneousCyclotomic_def, homogeneousCyclotomic_def, homogeneousCyclotomic_def, ← map_mul,
    ← homogenize_mul _ _ natDegree_cyclotomic_le natDegree_cyclotomic_le, hdeg,
    ← cyclotomic_expand_eq_cyclotomic_mul hp hpn, homogenize_expand hp.ne_zero,
    MvPolynomial.eval_expand]
  congr 2
  ext i
  fin_cases i <;> simp

/-- For a prime `p`, `Φ_{p ^ (e + 1) m}(a, b) = Φ_{p m}(a ^ p ^ e, b ^ p ^ e)`: the factor `p ^ e`
of the index is traded for raising both arguments to the power `p ^ e`. No condition on `m` is
needed. -/
theorem homogeneousCyclotomic_prime_pow_mul {p : ℕ} (hp : p.Prime) (e m : ℕ) (a b : R) :
    homogeneousCyclotomic (p ^ (e + 1) * m) a b =
      homogeneousCyclotomic (p * m) (a ^ p ^ e) (b ^ p ^ e) := by
  induction e generalizing a b with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, mul_right_comm, homogeneousCyclotomic_mul_prime_of_dvd hp
      (dvd_mul_of_dvd_left (dvd_pow_self p e.succ_ne_zero) m), ih, ← pow_mul, ← pow_mul,
      ← pow_succ']

/-- For a prime `p` not dividing `m`,
`Φ_{p ^ (e + 1) m}(a, b) Φ_m(A, B) = Φ_m(A ^ p, B ^ p)` with `A = a ^ p ^ e` and
`B = b ^ p ^ e`. -/
theorem homogeneousCyclotomic_prime_pow_mul_mul_homogeneousCyclotomic {p m : ℕ} (hp : p.Prime)
    (hpm : ¬p ∣ m) (e : ℕ) (a b : R) :
    homogeneousCyclotomic (p ^ (e + 1) * m) a b *
        homogeneousCyclotomic m (a ^ p ^ e) (b ^ p ^ e) =
      homogeneousCyclotomic m (a ^ p ^ (e + 1)) (b ^ p ^ (e + 1)) := by
  rw [homogeneousCyclotomic_prime_pow_mul hp, mul_comm p,
    homogeneousCyclotomic_mul_prime_mul_homogeneousCyclotomic hp hpm, ← pow_mul, ← pow_mul,
    ← pow_succ]

/-- For a prime `p` not dividing `m`, in a field,
`Φ_{p ^ (e + 1) m}(a, b) = Φ_m(A ^ p, B ^ p) / Φ_m(A, B)` with `A = a ^ p ^ e` and
`B = b ^ p ^ e`, provided `Φ_m(A, B) ≠ 0`. -/
theorem homogeneousCyclotomic_prime_pow_mul_eq_div {K : Type*} [Field K] {p m : ℕ}
    (hp : p.Prime) (hpm : ¬p ∣ m) (e : ℕ) {a b : K}
    (h : homogeneousCyclotomic m (a ^ p ^ e) (b ^ p ^ e) ≠ 0) :
    homogeneousCyclotomic (p ^ (e + 1) * m) a b =
      homogeneousCyclotomic m (a ^ p ^ (e + 1)) (b ^ p ^ (e + 1)) /
        homogeneousCyclotomic m (a ^ p ^ e) (b ^ p ^ e) :=
  eq_div_of_mul_eq h (homogeneousCyclotomic_prime_pow_mul_mul_homogeneousCyclotomic hp hpm e a b)

/-! ### Closed forms -/

/-- `Φ_0(a, b) = 1`. -/
@[simp]
theorem homogeneousCyclotomic_zero (a b : R) : homogeneousCyclotomic 0 a b = 1 := by
  simp [homogeneousCyclotomic_def]

/-- A nonunit dividing `Φ_n(a, b)` forces `n ≠ 0`, since `Φ_0(a, b) = 1`. -/
theorem ne_zero_of_dvd_homogeneousCyclotomic {d a b : R} {n : ℕ} (hd : ¬IsUnit d)
    (h : d ∣ homogeneousCyclotomic n a b) : n ≠ 0 := by
  rintro rfl
  exact hd (isUnit_of_dvd_one (by simpa only [homogeneousCyclotomic_zero] using h))

/-- `Φ_1(a, b) = a - b`. -/
@[simp]
theorem homogeneousCyclotomic_one (a b : R) : homogeneousCyclotomic 1 a b = a - b := by
  simp [homogeneousCyclotomic_def]

/-- `Φ_2(a, b) = a + b`. -/
@[simp]
theorem homogeneousCyclotomic_two (a b : R) : homogeneousCyclotomic 2 a b = a + b := by
  simp [homogeneousCyclotomic_def]

/-- `Φ_3(a, b) = a ^ 2 + a b + b ^ 2`. -/
@[simp]
theorem homogeneousCyclotomic_three (a b : R) :
    homogeneousCyclotomic 3 a b = a ^ 2 + a * b + b ^ 2 := by
  simp [homogeneousCyclotomic_def, Nat.totient_prime Nat.prime_three]

/-- `Φ_6(a, b) = a ^ 2 - a b + b ^ 2`. -/
@[simp]
theorem homogeneousCyclotomic_six (a b : R) :
    homogeneousCyclotomic 6 a b = a ^ 2 - a * b + b ^ 2 := by
  have h6 : Nat.totient 6 = 2 := by decide
  simp [homogeneousCyclotomic_def, cyclotomic_six, h6]

/-- For a prime `p`, `Φ_p(a, b) = ∑_{i < p} a ^ i b ^ (p - 1 - i)`. -/
theorem homogeneousCyclotomic_prime {p : ℕ} (hp : p.Prime) (a b : R) :
    homogeneousCyclotomic p a b = ∑ i ∈ Finset.range p, a ^ i * b ^ (p - 1 - i) := by
  have := Fact.mk hp
  have h := eval_homogenize_geom_sum 1 p a b
  simp only [pow_one, one_mul] at h
  rw [homogeneousCyclotomic_def, cyclotomic_prime, Nat.totient_prime hp, h]

/-- For a prime `p`, `Φ_{p ^ (e + 1)}(a, b) = Φ_p(a ^ p ^ e, b ^ p ^ e)`. -/
theorem homogeneousCyclotomic_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) (a b : R) :
    homogeneousCyclotomic (p ^ (e + 1)) a b = homogeneousCyclotomic p (a ^ p ^ e) (b ^ p ^ e) := by
  simpa using homogeneousCyclotomic_prime_pow_mul hp e 1 a b

/-! ### Symmetry and values at zero -/

/-- For `n ≠ 1`, `Φ_n(a, b)` is symmetric in `a` and `b`, since the coefficients of `Φ_n` are
palindromic. -/
theorem homogeneousCyclotomic_comm {n : ℕ} (hn : n ≠ 1) (a b : R) :
    homogeneousCyclotomic n b a = homogeneousCyclotomic n a b := by
  calc homogeneousCyclotomic n b a
      = MvPolynomial.aeval ![b, a] ((cyclotomic n R).homogenize n.totient) := by
        rw [homogeneousCyclotomic_def, MvPolynomial.aeval_eq_eval]
    _ = MvPolynomial.aeval ![a, b] (((cyclotomic n R).reflect n.totient).homogenize n.totient) :=
        (aeval_homogenize_reflect _ _ a b).symm
    _ = homogeneousCyclotomic n a b := by
        rw [reflect_cyclotomic hn, homogeneousCyclotomic_def, MvPolynomial.aeval_eq_eval]

/-- `Φ_1(a, b) = a - b` is antisymmetric: `Φ_1(b, a) = -Φ_1(a, b)`. -/
theorem homogeneousCyclotomic_one_anticomm (a b : R) :
    homogeneousCyclotomic 1 b a = -homogeneousCyclotomic 1 a b := by
  rw [homogeneousCyclotomic_one, homogeneousCyclotomic_one, neg_sub]

/-- `Φ_n(a, 0) = a ^ φ(n)`: only the leading monomial survives. -/
@[simp]
theorem homogeneousCyclotomic_zero_right (n : ℕ) (a : R) :
    homogeneousCyclotomic n a 0 = a ^ n.totient := by
  nontriviality R
  rw [homogeneousCyclotomic_def, ← MvPolynomial.aeval_eq_eval,
    aeval_homogenize_of_eq_zero _ _ _ rfl, ← natDegree_cyclotomic n R,
    (cyclotomic.monic n R).coeff_natDegree]
  simp

/-- For `n ≠ 1`, `Φ_n(0, b) = b ^ φ(n)`: the constant coefficient of `Φ_n` is `1`. -/
@[simp]
theorem homogeneousCyclotomic_zero_left {n : ℕ} (hn : n ≠ 1) (b : R) :
    homogeneousCyclotomic n 0 b = b ^ n.totient := by
  rw [homogeneousCyclotomic_comm hn, homogeneousCyclotomic_zero_right]

/-! ### Factorization of `a ^ n - b ^ n` -/

/-- **Factorization of a difference of powers.** For `0 < n`,
`∏_{d ∣ n} Φ_d(a, b) = a ^ n - b ^ n`. The hypothesis is needed: for `n = 0` the product is
empty while `a ^ 0 - b ^ 0 = 0`. -/
theorem prod_homogeneousCyclotomic_eq_pow_sub_pow {n : ℕ} (hn : 0 < n) (a b : R) :
    ∏ d ∈ n.divisors, homogeneousCyclotomic d a b = a ^ n - b ^ n := by
  simp_rw [homogeneousCyclotomic_def]
  rw [← map_prod, ← homogenize_finsetProd (s := n.divisors)
      (p := fun d ↦ cyclotomic d R) (n := Nat.totient) (fun d _ ↦ natDegree_cyclotomic_le),
    Nat.sum_totient,
    prod_cyclotomic_eq_X_pow_sub_one hn, homogenize_sub, homogenize_X_pow le_rfl, homogenize_one]
  simp

/-- For `0 < n`, `Φ_n(a, b) ∏_{d ∣ n, d < n} Φ_d(a, b) = a ^ n - b ^ n`: the factor of index `n`
split off the factorization of `a ^ n - b ^ n`. -/
theorem homogeneousCyclotomic_mul_prod_properDivisors {n : ℕ} (hn : 0 < n) (a b : R) :
    homogeneousCyclotomic n a b * ∏ d ∈ n.properDivisors, homogeneousCyclotomic d a b =
      a ^ n - b ^ n := by
  rw [← Finset.prod_cons (f := fun d => homogeneousCyclotomic d a b)
    Nat.self_notMem_properDivisors, Nat.cons_self_properDivisors hn.ne',
    prod_homogeneousCyclotomic_eq_pow_sub_pow hn]

/-- For `d ∣ n`, `Φ_d(a, b)` divides `a ^ n - b ^ n`. -/
theorem homogeneousCyclotomic_dvd_pow_sub_pow {d n : ℕ} (h : d ∣ n) (a b : R) :
    homogeneousCyclotomic d a b ∣ a ^ n - b ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [← prod_homogeneousCyclotomic_eq_pow_sub_pow hn]
  exact Finset.dvd_prod_of_mem _ (Nat.mem_divisors.2 ⟨h, hn.ne'⟩)

/-! ### Positivity -/

/-- In an ordered commutative ring, `0 < Φ_n(a, b)` for every `n` whenever `0 ≤ b < a`. The value
`b` may vanish: `Φ_n(a, 0) = a ^ φ(n)`. -/
theorem homogeneousCyclotomic_pos [LinearOrder R] [IsStrictOrderedRing R] {a b : R} (hb : 0 ≤ b)
    (hba : b < a) (n : ℕ) : 0 < homogeneousCyclotomic n a b := by
  induction n using Nat.strong_induction_on with | _ n ih
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  -- `a ^ n - b ^ n = Φ_n(a, b) * ∏_{d ∣ n, d < n} Φ_d(a, b)` with every factor of the product
  -- positive by induction.
  have hQ : 0 < ∏ d ∈ n.properDivisors, homogeneousCyclotomic d a b :=
    Finset.prod_pos fun d hd => ih d (Nat.mem_properDivisors.1 hd).2
  have h :
      0 < homogeneousCyclotomic n a b * ∏ d ∈ n.properDivisors, homogeneousCyclotomic d a b := by
    rw [homogeneousCyclotomic_mul_prod_properDivisors hn, sub_pos]
    exact pow_lt_pow_left₀ hba hb hn.ne'
  exact (pos_iff_pos_of_mul_pos h).2 hQ

end TauCeti
