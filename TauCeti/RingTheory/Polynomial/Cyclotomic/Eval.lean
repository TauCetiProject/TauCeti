/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import TauCeti.RingTheory.Polynomial.Cyclotomic.Homogeneous

/-!
# Size estimates for homogeneous cyclotomic values

For real numbers `0 < b < a`, the homogeneous cyclotomic value `Φ_n(a, b)` lies between the
powers `(a - b) ^ φ(n)` and `(a + b) ^ φ(n)`:
`(a - b) ^ φ(n) < Φ_n(a, b)` for `n ≥ 2` and `Φ_n(a, b) < (a + b) ^ φ(n)` for `n ≥ 3`, while the
non-strict bounds hold for every `n` and also at `b = 0`, where `Φ_n(a, 0) = a ^ φ(n)`. These are
the two-variable forms of Mathlib's bounds `(q - 1) ^ φ(n) < Φ_n(q) < (q + 1) ^ φ(n)` for real
`q > 1`, obtained from `Φ_n(a, b) = Φ_n(a / b) b ^ φ(n)`; they are also stated for integer bases.
For a prime `p` and bases `a, b ≥ 1`, the geometric sum
`Φ_p(a, b) = ∑_{i < p} a ^ i b ^ (p - 1 - i)` is at least `p`, and exceeds `p` once `a > 1`; the
same holds for `Φ_{p ^ k}(a, b) = Φ_p(a ^ p ^ (k - 1), b ^ p ^ (k - 1))` when `k ≠ 0`.

The lower bounds show that `Φ_n(a, b)` is large compared with the prime divisors of `n`, which is
how the Bang–Zsigmondy theorem rules out cyclotomic values made only of nonprimitive prime
divisors. For real `0 < b` with `a - b ≥ 2`, every prime factor `p` of `n ≠ 0` satisfies
`p < Φ_n(a, b)`, because `p ≤ 2 ^ φ(n) ≤ (a - b) ^ φ(n)`.

## Main results

* `TauCeti.sub_pow_totient_lt_homogeneousCyclotomic`,
  `TauCeti.homogeneousCyclotomic_lt_add_pow_totient`: the strict bounds over `ℝ`.
* `TauCeti.sub_pow_totient_le_homogeneousCyclotomic`,
  `TauCeti.homogeneousCyclotomic_le_add_pow_totient`: the non-strict bounds over `ℝ`, for every
  `n` and `0 ≤ b < a`.
* `Int.sub_pow_totient_lt_homogeneousCyclotomic`, `Int.homogeneousCyclotomic_lt_add_pow_totient`,
  `Int.sub_pow_totient_le_homogeneousCyclotomic`, `Int.homogeneousCyclotomic_le_add_pow_totient`:
  the same bounds for integer bases.
* `TauCeti.natCast_le_homogeneousCyclotomic_prime`,
  `TauCeti.natCast_lt_homogeneousCyclotomic_prime`: `p ≤ Φ_p(a, b)` for `a, b ≥ 1`, strictly if
  `a > 1`, in an ordered commutative ring.
* `TauCeti.natCast_le_homogeneousCyclotomic_prime_pow`,
  `TauCeti.natCast_lt_homogeneousCyclotomic_prime_pow`: the same bounds for `Φ_{p ^ k}(a, b)`,
  `k ≠ 0`.
* `TauCeti.natCast_lt_homogeneousCyclotomic_of_prime_of_dvd`,
  `Int.natCast_lt_homogeneousCyclotomic_of_prime_of_dvd`: `p < Φ_n(a, b)` for every prime
  `p ∣ n ≠ 0` and real or integer bases `0 < b` with `a - b ≥ 2`.

## References

* [Ö. Avcı, *Large Zsigmondy primes*, arXiv:2011.06136v2 (2023)], Corollary 2.8.
* [G. D. Birkhoff and H. S. Vandiver, *On the integral divisors of `a ^ n - b ^ n`*,
  Ann. of Math. (2) 5 (1904), 173–180], proof of Theorem V, pp. 178–179.
* [M. Roitman, *On Zsigmondy primes*, Proc. Amer. Math. Soc. 125 (1997), 1913–1919], Lemma 1
  and the proof of Theorem 3.
-/

public section

open Polynomial

namespace TauCeti

/-! ### Real bases -/

/-- For `n ≥ 2` and real `0 < b < a`, `(a - b) ^ φ(n) < Φ_n(a, b)`. The bound fails for `n = 1`,
where `Φ_1(a, b) = a - b`. -/
theorem sub_pow_totient_lt_homogeneousCyclotomic {n : ℕ} (hn : 2 ≤ n) {a b : ℝ} (hb : 0 < b)
    (hba : b < a) : (a - b) ^ n.totient < homogeneousCyclotomic n a b := by
  rw [homogeneousCyclotomic_eq_eval_div_mul_pow n a hb.ne']
  calc (a - b) ^ n.totient = (a / b - 1) ^ n.totient * b ^ n.totient := by
        rw [← mul_pow, sub_one_mul, div_mul_cancel₀ a hb.ne']
    _ < _ := mul_lt_mul_of_pos_right
        (sub_one_pow_totient_lt_cyclotomic_eval hn ((one_lt_div hb).2 hba)) (pow_pos hb _)

/-- For `n ≥ 3` and real `0 < b < a`, `Φ_n(a, b) < (a + b) ^ φ(n)`. The bound fails for `n = 2`,
where `Φ_2(a, b) = a + b`. -/
theorem homogeneousCyclotomic_lt_add_pow_totient {n : ℕ} (hn : 3 ≤ n) {a b : ℝ} (hb : 0 < b)
    (hba : b < a) : homogeneousCyclotomic n a b < (a + b) ^ n.totient := by
  rw [homogeneousCyclotomic_eq_eval_div_mul_pow n a hb.ne']
  calc _ < (a / b + 1) ^ n.totient * b ^ n.totient := mul_lt_mul_of_pos_right
        (cyclotomic_eval_lt_add_one_pow_totient hn ((one_lt_div hb).2 hba)) (pow_pos hb _)
    _ = (a + b) ^ n.totient := by rw [← mul_pow, add_one_mul, div_mul_cancel₀ a hb.ne']

/-- For every `n` and real `0 ≤ b < a`, `(a - b) ^ φ(n) ≤ Φ_n(a, b)`, with equality at `b = 0`. -/
theorem sub_pow_totient_le_homogeneousCyclotomic (n : ℕ) {a b : ℝ} (hb : 0 ≤ b) (hba : b < a) :
    (a - b) ^ n.totient ≤ homogeneousCyclotomic n a b := by
  rcases hb.eq_or_lt with rfl | hb
  · simp
  rw [homogeneousCyclotomic_eq_eval_div_mul_pow n a hb.ne']
  calc (a - b) ^ n.totient = (a / b - 1) ^ n.totient * b ^ n.totient := by
        rw [← mul_pow, sub_one_mul, div_mul_cancel₀ a hb.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right
        (sub_one_pow_totient_le_cyclotomic_eval ((one_lt_div hb).2 hba) n) (pow_nonneg hb.le _)

/-- For every `n` and real `0 ≤ b < a`, `Φ_n(a, b) ≤ (a + b) ^ φ(n)`, with equality at `b = 0`
and at `n = 2`. -/
theorem homogeneousCyclotomic_le_add_pow_totient (n : ℕ) {a b : ℝ} (hb : 0 ≤ b) (hba : b < a) :
    homogeneousCyclotomic n a b ≤ (a + b) ^ n.totient := by
  rcases hb.eq_or_lt with rfl | hb
  · simp
  rw [homogeneousCyclotomic_eq_eval_div_mul_pow n a hb.ne']
  calc _ ≤ (a / b + 1) ^ n.totient * b ^ n.totient := mul_le_mul_of_nonneg_right
        (cyclotomic_eval_le_add_one_pow_totient ((one_lt_div hb).2 hba) n) (pow_nonneg hb.le _)
    _ = (a + b) ^ n.totient := by rw [← mul_pow, add_one_mul, div_mul_cancel₀ a hb.ne']

/-- For real `0 < b` with `2 ≤ a - b`, every prime factor `p` of `n ≠ 0` satisfies
`p < Φ_n(a, b)`. The hypothesis `2 ≤ a - b` is needed: `Φ_6(2, 1) = 3`. -/
theorem natCast_lt_homogeneousCyclotomic_of_prime_of_dvd {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime)
    (hpn : p ∣ n) {a b : ℝ} (hb : 0 < b) (hab : 2 ≤ a - b) :
    (p : ℝ) < homogeneousCyclotomic n a b := by
  have htot : p - 1 ≤ n.totient := by
    rw [← Nat.totient_prime hp]
    exact Nat.le_of_dvd (Nat.totient_pos.2 (Nat.pos_of_ne_zero hn)) (Nat.totient_dvd_of_dvd hpn)
  have hp2 : p ≤ 2 ^ n.totient := by
    have := (p - 1).lt_two_pow_self
    have := Nat.pow_le_pow_right two_pos htot
    have := hp.pos
    omega
  calc (p : ℝ) ≤ 2 ^ n.totient := by exact_mod_cast hp2
    _ ≤ (a - b) ^ n.totient := pow_le_pow_left₀ zero_le_two hab _
    _ < homogeneousCyclotomic n a b :=
        sub_pow_totient_lt_homogeneousCyclotomic
          (hp.two_le.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn)) hb (by linarith)

/-! ### Prime and prime-power indices -/

variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]

/-- For a prime `p` and `a, b ≥ 1` in an ordered commutative ring, `p ≤ Φ_p(a, b)`: each of the
`p` terms of `Φ_p(a, b) = ∑_{i < p} a ^ i b ^ (p - 1 - i)` is at least `1`. -/
theorem natCast_le_homogeneousCyclotomic_prime {p : ℕ} (hp : p.Prime) {a b : R} (ha : 1 ≤ a)
    (hb : 1 ≤ b) : (p : R) ≤ homogeneousCyclotomic p a b := by
  rw [homogeneousCyclotomic_prime hp]
  calc (p : R) = ∑ _i ∈ Finset.range p, (1 : R) := by simp
    _ ≤ _ := Finset.sum_le_sum fun i _ => one_le_mul_of_one_le_of_one_le (one_le_pow₀ ha)
        (one_le_pow₀ hb)

/-- For a prime `p`, `1 < a` and `1 ≤ b` in an ordered commutative ring, `p < Φ_p(a, b)`: the term
`a ^ (p - 1)` of `Φ_p(a, b) = ∑_{i < p} a ^ i b ^ (p - 1 - i)` exceeds `1`. Since `Φ_p` is
symmetric, the same holds for `1 ≤ a` and `1 < b`; at `a = b = 1`, `Φ_p(1, 1) = p`. -/
theorem natCast_lt_homogeneousCyclotomic_prime {p : ℕ} (hp : p.Prime) {a b : R} (ha : 1 < a)
    (hb : 1 ≤ b) : (p : R) < homogeneousCyclotomic p a b := by
  rw [homogeneousCyclotomic_prime hp]
  calc (p : R) = ∑ _i ∈ Finset.range p, (1 : R) := by simp
    _ < _ := Finset.sum_lt_sum
        (fun i _ => one_le_mul_of_one_le_of_one_le (one_le_pow₀ ha.le) (one_le_pow₀ hb))
        ⟨p - 1, Finset.mem_range.2 (Nat.sub_lt hp.pos one_pos), by
          simpa using one_lt_pow₀ ha (Nat.sub_ne_zero_of_lt hp.one_lt)⟩

/-- For a prime `p`, `k ≠ 0` and `a, b ≥ 1` in an ordered commutative ring,
`p ≤ Φ_{p ^ k}(a, b)`. -/
theorem natCast_le_homogeneousCyclotomic_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0)
    {a b : R} (ha : 1 ≤ a) (hb : 1 ≤ b) : (p : R) ≤ homogeneousCyclotomic (p ^ k) a b := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk
  rw [homogeneousCyclotomic_prime_pow hp]
  exact natCast_le_homogeneousCyclotomic_prime hp (one_le_pow₀ ha) (one_le_pow₀ hb)

/-- For a prime `p`, `k ≠ 0`, `1 < a` and `1 ≤ b` in an ordered commutative ring,
`p < Φ_{p ^ k}(a, b)`. -/
theorem natCast_lt_homogeneousCyclotomic_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0)
    {a b : R} (ha : 1 < a) (hb : 1 ≤ b) : (p : R) < homogeneousCyclotomic (p ^ k) a b := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk
  rw [homogeneousCyclotomic_prime_pow hp]
  exact natCast_lt_homogeneousCyclotomic_prime hp
    (one_lt_pow₀ ha (pow_ne_zero _ hp.ne_zero)) (one_le_pow₀ hb)

end TauCeti

/-! ### Integer bases -/

namespace Int

open TauCeti

/-- For `n ≥ 2` and integers `0 < b < a`, `(a - b) ^ φ(n) < Φ_n(a, b)`. -/
theorem sub_pow_totient_lt_homogeneousCyclotomic {n : ℕ} (hn : 2 ≤ n) {a b : ℤ} (hb : 0 < b)
    (hba : b < a) : (a - b) ^ n.totient < homogeneousCyclotomic n a b := by
  exact_mod_cast TauCeti.sub_pow_totient_lt_homogeneousCyclotomic hn (a := a) (b := b)
    (by exact_mod_cast hb) (by exact_mod_cast hba)

/-- For `n ≥ 3` and integers `0 < b < a`, `Φ_n(a, b) < (a + b) ^ φ(n)`. -/
theorem homogeneousCyclotomic_lt_add_pow_totient {n : ℕ} (hn : 3 ≤ n) {a b : ℤ} (hb : 0 < b)
    (hba : b < a) : homogeneousCyclotomic n a b < (a + b) ^ n.totient := by
  exact_mod_cast TauCeti.homogeneousCyclotomic_lt_add_pow_totient hn (a := a) (b := b)
    (by exact_mod_cast hb) (by exact_mod_cast hba)

/-- For every `n` and integers `0 ≤ b < a`, `(a - b) ^ φ(n) ≤ Φ_n(a, b)`. -/
theorem sub_pow_totient_le_homogeneousCyclotomic (n : ℕ) {a b : ℤ} (hb : 0 ≤ b) (hba : b < a) :
    (a - b) ^ n.totient ≤ homogeneousCyclotomic n a b := by
  exact_mod_cast TauCeti.sub_pow_totient_le_homogeneousCyclotomic n (a := a) (b := b)
    (by exact_mod_cast hb) (by exact_mod_cast hba)

/-- For every `n` and integers `0 ≤ b < a`, `Φ_n(a, b) ≤ (a + b) ^ φ(n)`. -/
theorem homogeneousCyclotomic_le_add_pow_totient (n : ℕ) {a b : ℤ} (hb : 0 ≤ b) (hba : b < a) :
    homogeneousCyclotomic n a b ≤ (a + b) ^ n.totient := by
  exact_mod_cast TauCeti.homogeneousCyclotomic_le_add_pow_totient n (a := a) (b := b)
    (by exact_mod_cast hb) (by exact_mod_cast hba)

/-- For integers `0 < b` with `2 ≤ a - b`, every prime factor `p` of `n ≠ 0` satisfies
`p < Φ_n(a, b)`. -/
theorem natCast_lt_homogeneousCyclotomic_of_prime_of_dvd {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime)
    (hpn : p ∣ n) {a b : ℤ} (hb : 0 < b) (hab : 2 ≤ a - b) :
    (p : ℤ) < homogeneousCyclotomic n a b := by
  exact_mod_cast TauCeti.natCast_lt_homogeneousCyclotomic_of_prime_of_dvd hn hp hpn (a := a)
    (b := b) (by exact_mod_cast hb) (by exact_mod_cast hab)

end Int
