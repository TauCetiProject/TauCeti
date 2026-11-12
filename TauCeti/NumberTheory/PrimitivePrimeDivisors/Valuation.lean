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

For any positive multiple `k` of `d`, the quotient from exponent `k` to `p * k`
has valuation one, except when `p = 2` and `k` is odd, when it has valuation `v₂(a + b)`.
In the tower `d * p ^ e`, only the first dyadic quotient is exceptional.
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
  · exact Nat.multiplicity_pow_sub_pow_of_dvd_pow_sub_pow hpodd hba
      ((hp.dvd_pow_sub_pow_iff_orderOf_dvd hba.le hb _).mpr (dvd_refl _)) ha
      (hp.not_dvd_orderOf_ratio hab) hd hk
  · exact multiplicity_eq_zero_of_not_dvd
      (fun h => hd ((hp.dvd_pow_sub_pow_iff_orderOf_dvd hba.le hb k).mp h))

/-- For a nonzero multiple `k` of the order of the ratio modulo `p`, the quotient from
exponent `k` to `p * k` has valuation one. At `p = 2` and odd `k`, its valuation is
instead `v₂(a + b)`. In particular, along the tower `d * p ^ e` only the first dyadic
quotient is exceptional. -/
theorem multiplicity_pow_sub_pow_div_pow_sub_pow_eq_ite {p : ℕ} (hp : p.Prime)
    {a b k : ℕ} (hba : b < a) (hab : ¬ p ∣ a * b) (hk : k ≠ 0)
    (hdk : orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) ∣ k) :
    multiplicity p ((a ^ (p * k) - b ^ (p * k)) / (a ^ k - b ^ k)) =
      if p = 2 ∧ Odd k then multiplicity 2 (a + b) else 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hpk : p * k ≠ 0 := mul_ne_zero hp.ne_zero hk
  have hmul : multiplicity p (p * k) = 1 + multiplicity p k := by
    rw [Nat.multiplicity_mul hp.ne_zero hk]
    simp
  -- The quotient is exact, so its valuation is the difference of adjacent valuations.
  rw [Nat.multiplicity_div_of_dvd
    (Nat.pow_sub_pow_dvd_pow_sub_pow a b (dvd_mul_left k p))]
  by_cases hp2 : p = 2
  · subst p
    have ha : Odd a := Nat.not_even_iff_odd.mp (fun h =>
      hab (dvd_mul_of_dvd_left h.two_dvd b))
    have hb : Odd b := Nat.not_even_iff_odd.mp (fun h =>
      hab (dvd_mul_of_dvd_right h.two_dvd a))
    have hv1 := Nat.multiplicity_pow_two_sub_pow_of_even hba ha hb
      (even_two.mul_right k) hpk
    rw [hmul] at hv1
    simp only [true_and]
    -- Odd exponents retain the base valuation; even exponents use dyadic lifting twice.
    by_cases hodd : Odd k
    · rw [ite_eq_left hodd, Nat.multiplicity_pow_two_sub_pow_of_odd ha hb hodd]
      have hval := Nat.multiplicity_pow_two_sub_pow hba
        (Nat.Odd.sub_odd ha hb).two_dvd ha.not_two_dvd_nat (by decide : 2 ≠ 0)
        (by decide : Even 2)
      have hkval := multiplicity_eq_zero_of_not_dvd hodd.not_two_dvd_nat
      have htwo : multiplicity 2 2 = 1 := by simp
      rw [htwo] at hval
      omega
    · rw [ite_eq_right hodd]
      have hv0 := Nat.multiplicity_pow_two_sub_pow_of_even hba ha hb
        (Nat.not_odd_iff_even.mp hodd) hk
      omega
  · -- For odd primes, the order-based formulas differ only in the exponent valuation.
    have hpodd : Odd p := hp.odd_of_ne_two hp2
    have hv0 := hp.multiplicity_pow_sub_pow_eq_ite_orderOf_dvd hpodd hba hab hk
    have hv1 := hp.multiplicity_pow_sub_pow_eq_ite_orderOf_dvd hpodd hba hab hpk
    rw [ite_eq_left hdk] at hv0
    rw [ite_eq_left (dvd_mul_of_dvd_right hdk p), hmul] at hv1
    simp only [hp2, false_and, ite_false]
    omega

end Nat.Prime
