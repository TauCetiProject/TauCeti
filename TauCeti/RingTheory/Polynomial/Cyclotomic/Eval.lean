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
`Φ_p(a, b) = ∑_{i < p} a ^ i b ^ (p - 1 - i)` is at least `p`, and exceeds `p` once `a > 1`.
Combining the lower and upper bounds across the expansion identity
`Φ_{p m}(a, b) Φ_m(a, b) = Φ_m(a ^ p, b ^ p)` yields
`((a ^ p - b ^ p) / (a + b)) ^ φ(m) < Φ_{p m}(a, b)` whenever `m ≠ 0` and `p ∤ m`, while for
`b + 2 ≤ a` the lower bound `(a - b) ^ φ(n) ≥ 2 ^ (p - 1)` already exceeds every prime factor `p`
of `n ≠ 0`.

The lower bounds show that `Φ_n(a, b)` is large compared with the prime divisors of `n`, which is
how the Bang–Zsigmondy theorem rules out cyclotomic values made only of nonprimitive prime
divisors.

## Main results

* `TauCeti.sub_pow_totient_lt_homogeneousCyclotomic`,
  `TauCeti.homogeneousCyclotomic_lt_add_pow_totient`: the strict bounds over `ℝ`.
* `TauCeti.sub_pow_totient_le_homogeneousCyclotomic`,
  `TauCeti.homogeneousCyclotomic_le_add_pow_totient`: the non-strict bounds over `ℝ`, for every
  `n` and `0 ≤ b < a`.
* `TauCeti.pow_sub_pow_div_add_pow_totient_lt_homogeneousCyclotomic`: for a prime `p`, `m ≠ 0`
  with `p ∤ m`, and real `0 < b < a`, `((a ^ p - b ^ p) / (a + b)) ^ φ(m) < Φ_{p m}(a, b)`.
* `TauCeti.natCast_lt_homogeneousCyclotomic_of_dvd`,
  `Int.natCast_lt_homogeneousCyclotomic_of_dvd`: for a prime `p ∣ n`, `n ≠ 0`, `0 < b`, and
  `b + 2 ≤ a`, `p < Φ_n(a, b)`.
* `Int.natCast_lt_homogeneousCyclotomic_of_sq_dvd`: for a prime `p` with `p ^ 2 ∣ n`, `n ≠ 0`,
  and integers `0 < b < a`, `p < Φ_n(a, b)`.
* `Int.sub_pow_totient_lt_homogeneousCyclotomic`, `Int.homogeneousCyclotomic_lt_add_pow_totient`,
  `Int.sub_pow_totient_le_homogeneousCyclotomic`, `Int.homogeneousCyclotomic_le_add_pow_totient`:
  the power bounds for integer bases.
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

/-- For a prime `p`, `m ≠ 0` with `p ∤ m`, and real `0 < b < a`,
`((a ^ p - b ^ p) / (a + b)) ^ φ(m) < Φ_{p m}(a, b)` (Roitman 1997, Lemma 1, pp. 1913–1914, for
`b = 1`). -/
theorem pow_sub_pow_div_add_pow_totient_lt_homogeneousCyclotomic {p m : ℕ} (hp : p.Prime)
    (hm : m ≠ 0) (hpm : ¬p ∣ m) {a b : ℝ} (hb : 0 < b) (hba : b < a) :
    ((a ^ p - b ^ p) / (a + b)) ^ m.totient < homogeneousCyclotomic (p * m) a b := by
  have hΦpos : 0 < homogeneousCyclotomic m a b := homogeneousCyclotomic_pos hb.le hba m
  have hap : b ^ p < a ^ p := pow_lt_pow_left₀ hba hb.le hp.ne_zero
  have hab : 0 < a + b := by linarith
  have hexp :
      homogeneousCyclotomic (p * m) a b * homogeneousCyclotomic m a b =
        homogeneousCyclotomic m (a ^ p) (b ^ p) := by
    rw [mul_comm p m, homogeneousCyclotomic_mul_prime_mul_homogeneousCyclotomic hp hpm]
  refine lt_of_mul_lt_mul_right ?_ hΦpos.le
  rw [hexp]
  obtain rfl | hm2 : m = 1 ∨ 2 ≤ m := by omega
  · -- At `m = 1`, `Φ_1(a, b) = a - b < a + b` and `Φ_1(a ^ p, b ^ p) = a ^ p - b ^ p`.
    simp only [Nat.totient_one, pow_one, homogeneousCyclotomic_one]
    have hq : 0 < (a ^ p - b ^ p) / (a + b) := div_pos (sub_pos.2 hap) hab
    calc (a ^ p - b ^ p) / (a + b) * (a - b)
        < (a ^ p - b ^ p) / (a + b) * (a + b) := mul_lt_mul_of_pos_left (by linarith) hq
      _ = a ^ p - b ^ p := div_mul_cancel₀ _ hab.ne'
  · calc ((a ^ p - b ^ p) / (a + b)) ^ m.totient * homogeneousCyclotomic m a b
        ≤ ((a ^ p - b ^ p) / (a + b)) ^ m.totient * (a + b) ^ m.totient :=
          mul_le_mul_of_nonneg_left (homogeneousCyclotomic_le_add_pow_totient m hb.le hba)
            (pow_nonneg (div_nonneg (sub_nonneg.2 hap.le) hab.le) _)
      _ = (a ^ p - b ^ p) ^ m.totient := by
          rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hab.ne')]
      _ < homogeneousCyclotomic m (a ^ p) (b ^ p) :=
          sub_pow_totient_lt_homogeneousCyclotomic hm2 (pow_pos hb p) hap

/-- For a prime `p` dividing `n ≠ 0` and real `0 < b` with `b + 2 ≤ a`, `p < Φ_n(a, b)`. Both
`0 < b` and `b + 2 ≤ a` are sharp (`Φ_2(2, 0) = 2` and `Φ_6(2, 1) = 3`). -/
theorem natCast_lt_homogeneousCyclotomic_of_dvd {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (hn : n ≠ 0) {a b : ℝ} (hb : 0 < b) (hba : b + 2 ≤ a) :
    (p : ℝ) < homogeneousCyclotomic n a b := by
  have hn2 : 2 ≤ n := hp.two_le.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn)
  have htot : p - 1 ≤ n.totient := by
    rw [← Nat.totient_prime hp]
    exact Nat.le_of_dvd (Nat.totient_pos.2 (Nat.pos_of_ne_zero hn)) (Nat.totient_dvd_of_dvd hpn)
  have hp2 : p ≤ 2 ^ (p - 1) := by
    have := (p - 1).lt_two_pow_self
    omega
  calc (p : ℝ) ≤ (2 : ℝ) ^ (p - 1) := by exact_mod_cast hp2
    _ ≤ (2 : ℝ) ^ n.totient := pow_le_pow_right₀ one_le_two htot
    _ ≤ (a - b) ^ n.totient := pow_le_pow_left₀ zero_le_two (by linarith) _
    _ < homogeneousCyclotomic n a b :=
        sub_pow_totient_lt_homogeneousCyclotomic hn2 hb (by linarith)

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

/-- For a prime `p` dividing `n ≠ 0` and integers `0 < b` with `b + 2 ≤ a`, `p < Φ_n(a, b)`. -/
theorem natCast_lt_homogeneousCyclotomic_of_dvd {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (hn : n ≠ 0) {a b : ℤ} (hb : 0 < b) (hba : b + 2 ≤ a) :
    (p : ℤ) < homogeneousCyclotomic n a b := by
  exact_mod_cast TauCeti.natCast_lt_homogeneousCyclotomic_of_dvd hp hpn hn (a := a) (b := b)
    (by exact_mod_cast hb) (by exact_mod_cast hba)

/-- For a prime `p` with `p ^ 2 ∣ n`, `n ≠ 0`, and integers `0 < b < a`, `p < Φ_n(a, b)`.
Unlike the power bounds, this uses the integrality gap `b + 1 ≤ a`: over `ℝ`,
`Φ_18(a, 1) → 1 < 3` as `a → 1⁺`, while at `a = b = 1`, `Φ_4(1, 1) = 2`, and at `(2, 1, 6)`
(`3 ∣ 6`, `3 ^ 2 ∤ 6`), `Φ_6(2, 1) = 3`. -/
theorem natCast_lt_homogeneousCyclotomic_of_sq_dvd {p n : ℕ} (hp : p.Prime) (hpn : p ^ 2 ∣ n)
    (hn : n ≠ 0) {a b : ℤ} (hb : 0 < b) (hba : b < a) :
    (p : ℤ) < homogeneousCyclotomic n a b := by
  obtain ⟨k, rfl⟩ := hpn
  have hpk : p * k ≠ 0 := fun h0 => hn (by rw [sq, mul_assoc, h0, mul_zero])
  rw [sq, mul_right_comm, homogeneousCyclotomic_mul_prime_of_dvd hp (dvd_mul_right p k)]
  have hbern := pow_add_mul_le_add_pow hb.le (by omega : (0 : ℤ) ≤ 2 * b + 1) p
  have hbp : 1 ≤ b ^ (p - 1) := one_le_pow₀ hb
  have hp_le : (2 : ℤ) ≤ ↑p * b ^ (p - 1) * 1 := by
    calc (2 : ℤ) ≤ ↑p * 1 * 1 := by simpa using Int.ofNat_le.2 hp.two_le
      _ ≤ ↑p * b ^ (p - 1) * 1 := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbp (Nat.cast_nonneg p)) zero_le_one
  have hgap : b ^ p + 2 ≤ a ^ p :=
    calc b ^ p + 2 ≤ b ^ p + ↑p * b ^ (p - 1) * 1 := by linarith
      _ ≤ (b + 1) ^ p := hbern
      _ ≤ a ^ p := pow_le_pow_left₀ (by omega) (by omega) p
  exact Int.natCast_lt_homogeneousCyclotomic_of_dvd hp (dvd_mul_right p k) hpk
    (pow_pos hb p) hgap

end Int
