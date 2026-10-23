/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Ideal.Span
public import TauCeti.RingTheory.MvPowerSeries.Order
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Data.Nat.Choose.Factorization

/-!
# Power series in two variables whose `q`-th power lies in `(X ^ q, Y ^ q)`

Let `f ∈ R⟦X, Y⟧` have zero constant coefficient and linear part `X + Y`, over a semiring `R`.
Since all other terms have total degree at least two, the part of total degree `q` of
`f ^ q` is `(X + Y) ^ q`. No monomial `Xⁱ Y^(q - i)` with `0 < i < q` occurs in an element of
`(X ^ q, Y ^ q)`, so if `f ^ q` lies in this ideal then every binomial coefficient `q.choose i`
with `0 < i < q` vanishes in `R`. For `q = p ^ n` with `p` prime and `n ≠ 0`, taking `i = 1` gives
`p ^ n = 0`, and taking `i = p ^ (n - 1)`, whose binomial coefficient is `p` times an integer prime
to `p`, then gives `p = 0`: the characteristic of `R` divides both coefficients and hence `p`.

This is the coefficient argument behind Katz–Mazur, Lemma 5.3.4, applied to formal group laws in
`TauCeti.RingTheory.FormalGroup.CharP`.

## Main results

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

variable {R : Type*} {f : MvPowerSeries (Fin 2) R}

variable [Semiring R]

/-- If `f ∈ R⟦X, Y⟧` has zero constant coefficient and linear part `X + Y`, then the part of total
degree `q` of `f ^ q` is `(X + Y) ^ q`: the coefficient of `Xⁱ Y^(q - i)` in `f ^ q` is
`q.choose i`. -/
theorem coeff_single_add_single_pow_eq_choose (h₀ : f.constantCoeff = 0)
    (hX : coeff (single 0 1) f = 1) (hY : coeff (single 1 1) f = 1) {q i : ℕ} (hi : i ≤ q) :
    coeff (single 0 i + single 1 (q - i)) (f ^ q) = q.choose i := by
  have hpow : homogeneousComponent q (f ^ q) = (X 0 + X 1) ^ q := by
    simpa only [mul_one, homogeneousComponent_one_eq_X_add_X hX hY] using
      homogeneousComponent_pow_of_le_order (one_le_order_iff_constCoeff_eq_zero.mpr h₀) q
  have hd : (single (0 : Fin 2) i + single 1 (q - i)).degree = q := by
    rw [map_add, degree_single, degree_single]
    exact Nat.add_sub_cancel' hi
  have heq := congrArg (coeff (single (0 : Fin 2) i + single 1 (q - i))) hpow
  rw [coeff_homogeneousComponent, ite_eq_left hd] at heq
  have hnat : coeff (single (0 : Fin 2) i + single 1 (q - i))
      ((X 0 + X 1 : MvPowerSeries (Fin 2) ℕ) ^ q) = q.choose i := by
    rw [← MvPolynomial.coe_X, ← MvPolynomial.coe_X, ← MvPolynomial.coe_add,
      ← MvPolynomial.coe_pow, MvPolynomial.coeff_coe, MvPolynomial.coeff_add_pow]
    simp [hi]
  -- The linear polynomial has natural coefficients, so its formula maps to any semiring.
  rw [heq]
  simpa only [← coeff_map, map_pow, map_add, map_X, Nat.coe_castRingHom] using
    congrArg (Nat.castRingHom R) hnat

/-- If `f ∈ R⟦X, Y⟧` has zero constant coefficient and linear part `X + Y`, and `f ^ q` lies in
the ideal `(X ^ q, Y ^ q)`, then the binomial coefficient `q.choose i` vanishes in `R` for every
`0 < i < q`. -/
theorem natCast_choose_eq_zero_of_pow_mem_span (h₀ : f.constantCoeff = 0)
    (hX : coeff (single 0 1) f = 1) (hY : coeff (single 1 1) f = 1) {q i : ℕ}
    (h : f ^ q ∈ Ideal.span {X 0 ^ q, X 1 ^ q}) (hi₀ : 0 < i) (hiq : i < q) :
    (q.choose i : R) = 0 := by
  rw [← coeff_single_add_single_pow_eq_choose h₀ hX hY hiq.le]
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp h
  rw [← hab, map_add, ← X_pow_mul, ← X_pow_mul,
    X_pow_dvd_iff.mp (dvd_mul_right _ a) _ (by simpa),
    X_pow_dvd_iff.mp (dvd_mul_right _ b) _ (by simp; lia), add_zero]

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
  have hcop : (p ^ n).Coprime (c / p) :=
    (hp.coprime_iff_not_dvd.mpr hpm).pow_left n
  rw [ringChar.spec R]
  apply (hcop.of_dvd_left (ringChar.dvd hpow)).dvd_of_dvd_mul_right
  rw [hcm]
  exact ringChar.dvd hchoose

end MvPowerSeries
