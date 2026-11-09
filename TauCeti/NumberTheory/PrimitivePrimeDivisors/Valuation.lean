/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiplicity
public import TauCeti.NumberTheory.PrimitivePrimeDivisors.Order

/-!
# Valuations along the multiplicative-order tower

Let `p` be a prime not dividing `a * b`, and let `d` be the order of `a / b` modulo `p`.
For odd `p`, the valuation of `a ^ k - b ^ k` vanishes unless `d ∣ k`; at a positive
multiple of `d` it is the valuation at exponent `d` plus the valuation of `k`.

The successive quotients in the tower of exponents `d * p ^ e` have valuation one,
with exactly one exception: for `p = 2` the first quotient has valuation `v₂(a + b)`.
This is the valuation increment used to isolate a nonprimitive prime divisor in a
homogeneous cyclotomic factor. The statements need neither coprimality of the bases
nor positivity of the smaller base, only `b < a` and nonvanishing modulo `p`.

Valuations on naturals use Mathlib's `multiplicity`, the replacement for `padicValNat`.
All subtractions and quotients in the statements are in `ℕ`.

## References

* G. D. Birkhoff and H. S. Vandiver, *On the integral divisors of aⁿ − bⁿ*,
  Annals of Mathematics (2) 5 (1904), 173–180, Theorems III–IV, pp. 175–177.
* Ö. Avcı, *Large Zsigmondy primes*, arXiv:2011.06136v2 (2023), Lemmas 2.2 and 3.1.
-/

public section

namespace Nat.Prime

/-- For an odd prime, the valuation of a positive-exponent difference of powers is
zero off the multiples of the order of the ratio; on those multiples it is the
valuation at the order plus the valuation of the exponent. -/
theorem multiplicity_pow_sub_pow_eq_ite_orderOf_dvd {p : ℕ} (hp : p.Prime)
    (hpodd : Odd p) {a b k : ℕ} (hba : b < a) (hab : ¬ p ∣ a * b) (hk : k ≠ 0) :
    multiplicity p (a ^ k - b ^ k) =
      if orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) ∣ k then
        multiplicity p (a ^ orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) -
          b ^ orderOf ((a : ZMod p) * (b : ZMod p)⁻¹)) + multiplicity p k
      else 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have ha : ¬ p ∣ a := fun h => hab (dvd_mul_of_dvd_left h b)
  have hb : ¬ p ∣ b := fun h => hab (dvd_mul_of_dvd_right h a)
  split_ifs with hd
  · have hpd : ¬ p ∣ orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) := by
      intro h
      have := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt)
        (h.trans (hp.orderOf_ratio_dvd_sub_one hab))
      have := hp.one_lt
      omega
    exact Nat.multiplicity_pow_sub_pow_of_dvd_pow_sub_pow hpodd hba
      ((hp.dvd_pow_sub_pow_iff_orderOf_dvd hba.le hb _).mpr (dvd_refl _)) ha hpd hd hk
  · exact multiplicity_eq_zero_of_not_dvd
      (fun h => hd ((hp.dvd_pow_sub_pow_iff_orderOf_dvd hba.le hb k).mp h))

/-- Successive quotients at exponents `d * p ^ e`, where `d` is the order of the ratio
modulo `p`, have valuation one. The first dyadic quotient instead has valuation
`v₂(a + b)`; no other quotient is exceptional. -/
theorem multiplicity_order_prime_power_quotient {p : ℕ} (hp : p.Prime)
    {a b : ℕ} (hba : b < a) (hab : ¬ p ∣ a * b) (e : ℕ) :
    let d := orderOf ((a : ZMod p) * (b : ZMod p)⁻¹)
    multiplicity p ((a ^ (d * p ^ (e + 1)) - b ^ (d * p ^ (e + 1))) /
      (a ^ (d * p ^ e) - b ^ (d * p ^ e))) =
        if p = 2 ∧ e = 0 then multiplicity 2 (a + b) else 1 := by
  let : Fact p.Prime := ⟨hp⟩
  dsimp only
  let d := orderOf ((a : ZMod p) * (b : ZMod p)⁻¹)
  have hd : 0 < d := hp.orderOf_ratio_pos hab
  have hdiv : d * p ^ e ∣ d * p ^ (e + 1) :=
    Nat.mul_dvd_mul_left d (pow_dvd_pow p (by omega))
  -- The quotient is exact, so its valuation is the difference of adjacent valuations.
  rw [Nat.multiplicity_div_of_dvd (Nat.pow_sub_pow_dvd_pow_sub_pow a b hdiv)]
  by_cases hp2 : p = 2
  · subst p
    have hd1 : d = 1 := by
      exact Nat.dvd_one.mp (hp.orderOf_ratio_dvd_sub_one hab)
    have ha : Odd a := Nat.not_even_iff_odd.mp (fun h =>
      hab (dvd_mul_of_dvd_left h.two_dvd b))
    have hb : Odd b := Nat.not_even_iff_odd.mp (fun h =>
      hab (dvd_mul_of_dvd_right h.two_dvd a))
    simp only [hd1, one_mul, true_and]
    -- At two the order is one. Separate the first step from the even-exponent steps.
    rcases e with _ | e
    · simp only [Nat.zero_add, pow_zero, pow_one, ite_true]
      have hval := Nat.multiplicity_pow_two_sub_pow hba
        (Nat.Odd.sub_odd ha hb).two_dvd ha.not_two_dvd_nat (by decide : 2 ≠ 0)
        (by decide : Even 2)
      have htwo : multiplicity 2 2 = 1 := by simp
      rw [htwo] at hval
      omega
    · simp only [Nat.succ_ne_zero, ite_false]
      have hn0 : 2 ^ (e + 1) ≠ 0 := pow_ne_zero _ (by decide)
      have hn1 : 2 ^ (e + 1 + 1) ≠ 0 := pow_ne_zero _ (by decide)
      have he0 : Even (2 ^ (e + 1)) := even_two.pow_of_ne_zero (by omega)
      have he1 : Even (2 ^ (e + 1 + 1)) := even_two.pow_of_ne_zero (by omega)
      have hv0 := Nat.multiplicity_pow_two_sub_pow_of_even hba ha hb he0 hn0
      have hv1 := Nat.multiplicity_pow_two_sub_pow_of_even hba ha hb he1 hn1
      simp only [Nat.multiplicity_prime_pow] at hv0 hv1
      omega
  · -- For odd primes, the valuation grows by one at every step of the tower.
    have hpodd : Odd p := hp.odd_of_ne_two hp2
    have hn0 : d * p ^ e ≠ 0 := mul_ne_zero hd.ne' (pow_ne_zero _ hp.ne_zero)
    have hn1 : d * p ^ (e + 1) ≠ 0 := mul_ne_zero hd.ne' (pow_ne_zero _ hp.ne_zero)
    have hv0 := hp.multiplicity_pow_sub_pow_eq_ite_orderOf_dvd hpodd hba hab hn0
    have hv1 := hp.multiplicity_pow_sub_pow_eq_ite_orderOf_dvd hpodd hba hab hn1
    have hpd : multiplicity p d = 0 := multiplicity_eq_zero_of_not_dvd (by
      intro h
      have := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt)
        (h.trans (hp.orderOf_ratio_dvd_sub_one hab))
      have := hp.one_lt
      omega)
    dsimp only [d] at *
    simp only [dvd_mul_right, ite_true, Nat.multiplicity_mul hd.ne'
      (pow_ne_zero _ hp.ne_zero), Nat.multiplicity_prime_pow, hpd, zero_add] at hv0 hv1
    simp only [hp2, false_and, ite_false]
    omega

end Nat.Prime
