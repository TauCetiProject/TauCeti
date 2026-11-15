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
Combining the lower bound at `(a ^ p, b ^ p)` with the upper bound at `(a, b)` across
`Φ_{p m}(a, b) Φ_m(a, b) = Φ_m(a ^ p, b ^ p)` gives `((a ^ p - b ^ p) / (a + b)) ^ φ(m) <
Φ_{p m}(a, b)` for a prime `p ∤ m` and real `0 < b < a`, with equality at `b = 0`.
For a prime `p` and bases `a, b ≥ 1`, the geometric sum
`Φ_p(a, b) = ∑_{i < p} a ^ i b ^ (p - 1 - i)` is at least `p`, and exceeds `p` once `a > 1`.

The lower bounds show that `Φ_n(a, b)` is large compared with the prime divisors of `n`, which is
how the Bang–Zsigmondy theorem rules out cyclotomic values made only of nonprimitive prime
divisors.

## Main results

* `TauCeti.sub_pow_totient_lt_homogeneousCyclotomic`,
  `TauCeti.homogeneousCyclotomic_lt_add_pow_totient`: the strict bounds over `ℝ`.
* `TauCeti.sub_pow_totient_le_homogeneousCyclotomic`,
  `TauCeti.homogeneousCyclotomic_le_add_pow_totient`: the non-strict bounds over `ℝ`, for every
  `n` and `0 ≤ b < a`.
* `TauCeti.pow_sub_pow_div_add_pow_totient_lt_homogeneousCyclotomic`,
  `TauCeti.pow_sub_pow_div_add_pow_totient_le_homogeneousCyclotomic`: the quotient-power lower
  bounds for `Φ_{p m}(a, b)` when `p` is prime and `p ∤ m`.
* `Int.sub_pow_totient_lt_homogeneousCyclotomic`, `Int.homogeneousCyclotomic_lt_add_pow_totient`,
  `Int.sub_pow_totient_le_homogeneousCyclotomic`, `Int.homogeneousCyclotomic_le_add_pow_totient`:
  the bounds `(a ∓ b) ^ φ(n)` for integer bases.
* `TauCeti.natCast_le_homogeneousCyclotomic_prime`,
  `TauCeti.natCast_lt_homogeneousCyclotomic_prime`: `p ≤ Φ_p(a, b)` for `a, b ≥ 1`, strictly if
  `a > 1`, in an ordered commutative ring.

## References

* [Ö. Avcı, *Large Zsigmondy primes*, arXiv:2011.06136v2 (2023)], Corollary 2.8.
* [G. D. Birkhoff and H. S. Vandiver, *On the integral divisors of `a ^ n - b ^ n`*,
  Ann. of Math. (2) 5 (1904), 173–180], pp. 178–179.
* [M. Roitman, *On Zsigmondy primes*, Proc. Amer. Math. Soc. 125 (1997), 1913–1919], Lemma 1.
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

/-- For a prime `p` not dividing `m` and real `0 < b < a`,
`((a ^ p - b ^ p) / (a + b)) ^ φ(m) < Φ_{p m}(a, b)`. Both `b > 0` and `p ∤ m` are needed:
at `b = 0` equality holds, and when `p ∣ m` the two sides have different homogeneity degrees. -/
theorem pow_sub_pow_div_add_pow_totient_lt_homogeneousCyclotomic {p m : ℕ} (hp : p.Prime)
    (hpm : ¬p ∣ m) {a b : ℝ} (hb : 0 < b) (hba : b < a) :
    ((a ^ p - b ^ p) / (a + b)) ^ m.totient < homogeneousCyclotomic (p * m) a b := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hpm (dvd_zero p)
  have hab_pos : 0 < a + b := by linarith
  have hpow_lt : b ^ p < a ^ p := pow_lt_pow_left₀ hba hb.le hp.ne_zero
  have hΦm_pos : 0 < homogeneousCyclotomic m a b := homogeneousCyclotomic_pos hb.le hba m
  -- Multiply by `Φ_m(a, b) > 0` and rewrite `Φ_{p m}(a, b) Φ_m(a, b)` as `Φ_m(a ^ p, b ^ p)`.
  refine lt_of_mul_lt_mul_right ?_ hΦm_pos.le
  rw [mul_comm p m, homogeneousCyclotomic_mul_prime_mul_homogeneousCyclotomic hp hpm a b]
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.2 hm0) with hm1 | hm2
  · rw [← hm1, Nat.totient_one, pow_one, homogeneousCyclotomic_one, homogeneousCyclotomic_one]
    calc (a ^ p - b ^ p) / (a + b) * (a - b)
        < (a ^ p - b ^ p) / (a + b) * (a + b) :=
          mul_lt_mul_of_pos_left (by linarith) (div_pos (sub_pos.2 hpow_lt) hab_pos)
      _ = a ^ p - b ^ p := div_mul_cancel₀ _ hab_pos.ne'
  · calc ((a ^ p - b ^ p) / (a + b)) ^ m.totient * homogeneousCyclotomic m a b
        ≤ ((a ^ p - b ^ p) / (a + b)) ^ m.totient * (a + b) ^ m.totient :=
          mul_le_mul_of_nonneg_left (homogeneousCyclotomic_le_add_pow_totient m hb.le hba)
            (pow_nonneg (div_nonneg (sub_nonneg.2 hpow_lt.le) hab_pos.le) _)
      _ = (a ^ p - b ^ p) ^ m.totient := by rw [← mul_pow, div_mul_cancel₀ _ hab_pos.ne']
      _ < homogeneousCyclotomic m (a ^ p) (b ^ p) :=
          sub_pow_totient_lt_homogeneousCyclotomic hm2 (pow_pos hb p) hpow_lt

/-- For a prime `p` not dividing `m` and real `0 ≤ b < a`,
`((a ^ p - b ^ p) / (a + b)) ^ φ(m) ≤ Φ_{p m}(a, b)`, with equality at `b = 0`. -/
theorem pow_sub_pow_div_add_pow_totient_le_homogeneousCyclotomic {p m : ℕ} (hp : p.Prime)
    (hpm : ¬p ∣ m) {a b : ℝ} (hb : 0 ≤ b) (hba : b < a) :
    ((a ^ p - b ^ p) / (a + b)) ^ m.totient ≤ homogeneousCyclotomic (p * m) a b := by
  rcases hb.eq_or_lt with rfl | hb
  · have hap : a ^ p / a = a ^ (p - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hp.one_le, pow_succ, mul_div_cancel_right₀ _ hba.ne']
    rw [zero_pow hp.ne_zero, sub_zero, add_zero, hap, ← pow_mul,
      homogeneousCyclotomic_zero_right, Nat.totient_mul_of_prime_of_not_dvd hp hpm, mul_comm]
  · exact (pow_sub_pow_div_add_pow_totient_lt_homogeneousCyclotomic hp hpm hb hba).le

/-! ### Prime indices -/

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

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

end Int
