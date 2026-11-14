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
For a prime `p` and `a, b ≥ 1`, the geometric sum
`Φ_p(a, b) = ∑_{i < p} a ^ i b ^ (p - 1 - i)` is at least `p`, and exceeds `p` once `a > 1`.
For a prime `p` not dividing `m` and real `0 < b < a`, `Φ_{p m}(a, b)` strictly exceeds
`((a ^ p - b ^ p) / (a + b)) ^ φ(m)`.

The lower bounds show that `Φ_n(a, b)` is large compared with the prime divisors of `n`, which is
how the Bang–Zsigmondy theorem rules out cyclotomic values made only of nonprimitive prime
divisors.

## Main results

* `TauCeti.sub_pow_totient_lt_homogeneousCyclotomic`,
  `TauCeti.homogeneousCyclotomic_lt_add_pow_totient`: the strict bounds over `ℝ`.
* `TauCeti.sub_pow_totient_le_homogeneousCyclotomic`,
  `TauCeti.homogeneousCyclotomic_le_add_pow_totient`: the non-strict bounds over `ℝ`, for every
  `n` and `0 ≤ b < a`.
* `TauCeti.pow_sub_pow_div_add_pow_totient_lt_homogeneousCyclotomic`: for a prime `p`, `p ∤ m`,
  and real `0 < b < a`, `((a ^ p - b ^ p) / (a + b)) ^ φ(m) < Φ_{p m}(a, b)`.
* `Int.sub_pow_totient_lt_homogeneousCyclotomic`, `Int.homogeneousCyclotomic_lt_add_pow_totient`,
  `Int.sub_pow_totient_le_homogeneousCyclotomic`, `Int.homogeneousCyclotomic_le_add_pow_totient`:
  the same bounds for integer bases.
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

/-- For a prime `p`, `p ∤ m`, and real `0 < b < a`,
`((a ^ p - b ^ p) / (a + b)) ^ φ(m) < Φ_{p m}(a, b)`. Neither condition on the index may be
dropped: `Φ_12(2, 1) = 13 < 25 = ((2 ^ 4 - 1) / 3) ^ φ(3)` and
`Φ_4(1 / 5, 1 / 10) = 1 / 20 < 1 / 10`. -/
theorem pow_sub_pow_div_add_pow_totient_lt_homogeneousCyclotomic {p m : ℕ} (hp : p.Prime)
    (hpm : ¬p ∣ m) {a b : ℝ} (hb : 0 < b) (hba : b < a) :
    ((a ^ p - b ^ p) / (a + b)) ^ m.totient < homogeneousCyclotomic (p * m) a b := by
  -- Write `Φ_{p m}(a, b) = Φ_m(a ^ p, b ^ p) / Φ_m(a, b)` and bound numerator and denominator.
  have hm0 : m ≠ 0 := fun h => hpm (h ▸ dvd_zero p)
  have hpos : 0 < homogeneousCyclotomic m a b := homogeneousCyclotomic_pos hb.le hba m
  have hexp : homogeneousCyclotomic (p * m) a b =
      homogeneousCyclotomic m (a ^ p) (b ^ p) / homogeneousCyclotomic m a b :=
    eq_div_of_mul_eq hpos.ne'
      (mul_comm p m ▸ homogeneousCyclotomic_mul_prime_mul_homogeneousCyclotomic hp hpm a b)
  have hbp : 0 < b ^ p := pow_pos hb p
  have hbap : b ^ p < a ^ p := pow_lt_pow_left₀ hba hb.le hp.ne_zero
  rcases eq_or_ne m 1 with rfl | hm1
  · rw [hexp, Nat.totient_one, pow_one, homogeneousCyclotomic_one, homogeneousCyclotomic_one]
    exact div_lt_div_of_pos_left (sub_pos.2 hbap) (sub_pos.2 hba) (by linarith)
  · have hm2 : 2 ≤ m := by omega
    rw [div_pow, hexp]
    exact (div_le_div_of_nonneg_left (pow_nonneg (sub_pos.2 hbap).le _) hpos
      (homogeneousCyclotomic_le_add_pow_totient m hb.le hba)).trans_lt
      (div_lt_div_of_pos_right (sub_pow_totient_lt_homogeneousCyclotomic hm2 hbp hbap) hpos)

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
