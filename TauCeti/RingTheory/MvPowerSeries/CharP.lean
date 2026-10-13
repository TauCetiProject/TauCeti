/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Power series in two variables whose `q`-th power lies in `(X ^ q, Y ^ q)`

Let `f ∈ R⟦X, Y⟧` have zero constant coefficient and linear part `X + Y`, over a commutative ring
`R`. Since `f = X + Y + (terms of total degree at least two)`, the part of total degree `q` of
`f ^ q` is `(X + Y) ^ q`. No monomial `Xⁱ Y^(q - i)` with `0 < i < q` occurs in an element of
`(X ^ q, Y ^ q)`, so if `f ^ q` lies in this ideal then every binomial coefficient `q.choose i`
with `0 < i < q` vanishes in `R`. For `q = p ^ n` with `p` prime and `n ≠ 0`, taking `i = 1` gives
`p ^ n = 0`, and taking `i = p ^ (n - 1)`, whose binomial coefficient is `p` times an integer prime
to `p`, then gives `p = 0`.

This is the coefficient argument behind Katz–Mazur, Lemma 5.3.4, applied to formal group laws in
`TauCeti.RingTheory.FormalGroup.CharP`.

## Main results

* `MvPowerSeries.two_le_order_sub_X_add_X`: such an `f` differs from `X + Y` by a series of order
  at least two.
* `MvPowerSeries.coeff_single_add_single_pow_eq_choose`: the coefficient of `Xⁱ Y^(q - i)` in
  `f ^ q` is `q.choose i`.
* `MvPowerSeries.natCast_choose_eq_zero_of_pow_mem_span`: if moreover `f ^ q ∈ (X ^ q, Y ^ q)`,
  then `q.choose i = 0` in `R` for `0 < i < q`.
* `MvPowerSeries.natCast_eq_zero_of_pow_mem_span`: if moreover `q = p ^ n` with `p` prime and
  `n ≠ 0`, then `p = 0` in `R`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Lemma 5.3.4.
-/

public section

open Finsupp

namespace MvPowerSeries

variable {R : Type*} [CommRing R] {f : MvPowerSeries (Fin 2) R}

/-- A power series in two variables with zero constant coefficient and linear part `X + Y` differs
from `X + Y` by a series of order at least two. -/
theorem two_le_order_sub_X_add_X (h₀ : f.constantCoeff = 0)
    (hX : coeff (single 0 1) f = 1) (hY : coeff (single 1 1) f = 1) :
    2 ≤ (f - (X 0 + X 1)).order := by
  refine nat_le_order fun d hd => ?_
  rw [degree_eq_sum, Fin.sum_univ_two] at hd
  have hd' : d = single 0 (d 0) + single 1 (d 1) := by
    ext i
    fin_cases i <;> simp
  rw [hd']
  obtain h | h | h : (d 0 = 0 ∧ d 1 = 0) ∨ (d 0 = 1 ∧ d 1 = 0) ∨ (d 0 = 0 ∧ d 1 = 1) := by
    lia
  all_goals simp [h.1, h.2, coeff_X, h₀, hX, hY, single_eq_single_iff]

/-- If `f ∈ R⟦X, Y⟧` has zero constant coefficient and linear part `X + Y`, then the part of total
degree `q` of `f ^ q` is `(X + Y) ^ q`: the coefficient of `Xⁱ Y^(q - i)` in `f ^ q` is
`q.choose i`. -/
theorem coeff_single_add_single_pow_eq_choose (h₀ : f.constantCoeff = 0)
    (hX : coeff (single 0 1) f = 1) (hY : coeff (single 1 1) f = 1) {q i : ℕ} (hi : i ≤ q) :
    coeff (single 0 i + single 1 (q - i)) (f ^ q) = q.choose i := by
  set g := f - (X 0 + X 1)
  have hg : 2 ≤ g.order := two_le_order_sub_X_add_X h₀ hX hY
  -- Write `f` as `(X + Y) + g` so that `add_pow` expands `f ^ q`; only the term `(X + Y) ^ q`
  -- contributes in total degree `q`, since every other term has order greater than `q`.
  rw [show f = X 0 + X 1 + g by simp [g], add_pow, map_sum, Finset.sum_eq_single q]
  · rw [tsub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one,
      ← MvPolynomial.coe_X, ← MvPolynomial.coe_X, ← MvPolynomial.coe_add, ← MvPolynomial.coe_pow,
      MvPolynomial.coeff_coe, MvPolynomial.coeff_add_pow]
    simp [hi]
  · intro k hk hkq
    replace hkq : k < q := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hkq
    apply coeff_of_lt_order
    have hL : (k : ℕ∞) ≤ ((X 0 + X 1 : MvPowerSeries (Fin 2) R) ^ k).order :=
      le_order_pow_of_constantCoeff_eq_zero k (by simp)
    have hG : (q - k) • (2 : ℕ∞) ≤ (g ^ (q - k)).order :=
      (nsmul_le_nsmul_right hg (q - k)).trans (le_order_pow (q - k))
    calc ((single (0 : Fin 2) i + single 1 (q - i)).degree : ℕ∞)
        = (q : ℕ∞) := by
          rw [map_add, degree_single, degree_single]
          exact_mod_cast Nat.add_sub_cancel' hi
      _ < (k : ℕ∞) + (q - k) • (2 : ℕ∞) := by
          rw [nsmul_eq_mul]
          exact_mod_cast (by lia : q < k + (q - k) * 2)
      _ ≤ _ + _ := add_le_add hL hG
      _ ≤ _ := le_order_mul
      _ ≤ _ + _ := le_self_add
      _ ≤ _ := le_order_mul
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self q)) h

/-- If `f ∈ R⟦X, Y⟧` has zero constant coefficient and linear part `X + Y`, and `f ^ q` lies in
the ideal `(X ^ q, Y ^ q)`, then the binomial coefficient `q.choose i` vanishes in `R` for every
`0 < i < q`. -/
theorem natCast_choose_eq_zero_of_pow_mem_span (h₀ : f.constantCoeff = 0)
    (hX : coeff (single 0 1) f = 1) (hY : coeff (single 1 1) f = 1) {q i : ℕ}
    (h : f ^ q ∈ Ideal.span {X 0 ^ q, X 1 ^ q}) (hi₀ : 0 < i) (hiq : i < q) :
    (q.choose i : R) = 0 := by
  rw [← coeff_single_add_single_pow_eq_choose h₀ hX hY hiq.le]
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp h
  rw [← hab, map_add, X_pow_dvd_iff.mp (dvd_mul_left _ a) _ (by simpa),
    X_pow_dvd_iff.mp (dvd_mul_left _ b) _ (by simp; lia), add_zero]

/-- **Katz–Mazur, Lemma 5.3.4.** If `f ∈ R⟦X, Y⟧` has zero constant coefficient and linear part
`X + Y`, and `f ^ (p ^ n)` lies in the ideal `(X ^ (p ^ n), Y ^ (p ^ n))` for a prime `p` and some
`n ≠ 0`, then `p = 0` in `R`. -/
theorem natCast_eq_zero_of_pow_mem_span (h₀ : f.constantCoeff = 0)
    (hX : coeff (single 0 1) f = 1) (hY : coeff (single 1 1) f = 1) {p n : ℕ} (hp : p.Prime)
    (hn : n ≠ 0) (h : f ^ p ^ n ∈ Ideal.span {X 0 ^ p ^ n, X 1 ^ p ^ n}) :
    (p : R) = 0 := by
  have hlt : p ^ (n - 1) < p ^ n := Nat.pow_lt_pow_right hp.one_lt (by lia)
  -- The binomial coefficients `C(pⁿ, 1) = pⁿ` and `C(pⁿ, pⁿ⁻¹)` vanish in `R`.
  have hpow : ((p ^ n : ℕ) : R) = 0 := by
    simpa using natCast_choose_eq_zero_of_pow_mem_span h₀ hX hY h one_pos
      (Nat.one_lt_pow hn hp.one_lt)
  have hchoose := natCast_choose_eq_zero_of_pow_mem_span h₀ hX hY h (pow_pos hp.pos _) hlt
  -- `C(pⁿ, pⁿ⁻¹)` is exactly divisible by `p`: it is `p * m` with `m` prime to `p`.
  set c := (p ^ n).choose (p ^ (n - 1))
  have hc : c.factorization p = 1 := by
    rw [Nat.factorization_choose_prime_pow hp hlt.le (pow_pos hp.pos _).ne', hp.factorization_pow,
      single_eq_same]
    lia
  have hcm : p * (c / p) = c := by
    simpa [hc] using Nat.ordProj_mul_ordCompl_eq_self c p
  have hpm : ¬p ∣ c / p := by
    have := Nat.not_dvd_ordCompl (n := c) hp (Nat.choose_pos hlt.le).ne'
    rwa [hc, pow_one] at this
  obtain ⟨u, v, huv⟩ : IsCoprime ((c / p : ℕ) : R) ((p ^ n : ℕ) : R) :=
    (((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm).symm.pow_right n).cast
  rw [← hcm, Nat.cast_mul] at hchoose
  calc (p : R) = p * (u * ((c / p : ℕ) : R) + v * ((p ^ n : ℕ) : R)) := by rw [huv, mul_one]
    _ = u * ((p : R) * ((c / p : ℕ) : R)) + v * p * ((p ^ n : ℕ) : R) := by ring
    _ = 0 := by rw [hchoose, hpow]; ring

end MvPowerSeries
