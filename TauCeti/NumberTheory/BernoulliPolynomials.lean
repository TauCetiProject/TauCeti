/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.BernoulliPolynomials
public import TauCeti.RingTheory.PowerSeries.CharacteristicSeries

/-!
# Exponential generating series and midpoint values of Bernoulli polynomials

Over a `ℚ`-algebra `A`, Mathlib's `Polynomial.bernoulli_generating_function` states that
`(∑ Bₙ(t) Xⁿ / n!) · (e^X - 1) = X e^{tX}`, while `bernoulliPowerSeries_mul_exp_sub_one` states
`B(X) · (e^X - 1) = X` for the Bernoulli series `B(X) = ∑ Bₙ Xⁿ / n!`. Eliminating `e^X - 1` by
cross-multiplying the two identities and cancelling `X` avoids dividing by `X` and gives the direct
factorization

`∑ Bₙ(t) Xⁿ / n! = B(X) · e^{tX}`.

Specializing `t` to `1 / 2 + u` replaces `B(X) · e^{X/2}` by the even characteristic series
`Â(X) = (X / 2) / sinh (X / 2)` (`TauCeti.aHatSeries`):

`∑ Bₙ(1/2 + u) Xⁿ / n! = Â(X) · e^{uX}`.

At `u = 0` this identifies the exponential generating series of the midpoint values `Bₙ(1/2)` with
`Â(X)`, yielding the closed rational formula `Bₙ(1/2) = (2 / 2ⁿ - 1) Bₙ`, vanishing at `1/2` in
odd degree, and the binomial sum `∑_{j ≤ n} C(n, j) 2ʲ Bⱼ = 2ⁿ Bₙ(1/2)`. Both the midpoint
identities and the shifted `1/2 + u` factorization feed the parity cancellations of single-valued
polylogarithms.

## Main results

* `TauCeti.mk_aeval_bernoulli_eq_bernoulliPowerSeries_mul_rescale_exp`:
  `∑ Bₙ(t) Xⁿ / n! = B(X) · e^{tX}`.
* `TauCeti.mk_aeval_inv_two_add_bernoulli_eq_aHatSeries_mul_rescale_exp`:
  `∑ Bₙ(1/2 + u) Xⁿ / n! = Â(X) · e^{uX}`.
* `TauCeti.mk_aeval_inv_two_bernoulli_eq_aHatSeries`: `∑ Bₙ(1/2) Xⁿ / n! = Â(X)`.
* `TauCeti.bernoulli_eval_inv_two`, `TauCeti.two_pow_mul_bernoulli_eval_inv_two`:
  `Bₙ(1/2) = (2 / 2ⁿ - 1) Bₙ` and `2ⁿ Bₙ(1/2) = (2 - 2ⁿ) Bₙ` in `ℚ`.
* `TauCeti.bernoulli_eval_inv_two_eq_zero_of_odd`: `Bₙ(1/2) = 0` for odd `n`.
* `TauCeti.sum_choose_mul_two_pow_mul_bernoulli`:
  `∑_{j ≤ n} C(n, j) 2ʲ Bⱼ = 2ⁿ Bₙ(1/2)`.

## References

* F. Hirzebruch, *Topological Methods in Algebraic Geometry*, Springer (1966), §1.
* D. Zagier, *Polylogarithms, Dedekind zeta functions and the algebraic K-theory of fields*,
  in *Arithmetic Algebraic Geometry* (Texel, 1989), Progress in Mathematics 89,
  Birkhäuser (1991), pp. 391–430, §7, pp. 413–414.
-/

public section

open Nat Finset PowerSeries

namespace TauCeti

section GeneratingSeries

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- **Exponential generating series of Bernoulli polynomials**: over any `ℚ`-algebra `A`,
`∑ Bₙ(t) Xⁿ / n! = B(X) · e^{tX}`. -/
theorem mk_aeval_bernoulli_eq_bernoulliPowerSeries_mul_rescale_exp (t : A) :
    (PowerSeries.mk fun n => Polynomial.aeval t ((1 / n ! : ℚ) • Polynomial.bernoulli n)) =
      bernoulliPowerSeries A * PowerSeries.rescale t (PowerSeries.exp A) := by
  refine PowerSeries.mul_X_cancel ?_
  linear_combination
    bernoulliPowerSeries A * Polynomial.bernoulli_generating_function t -
      (PowerSeries.mk fun n => Polynomial.aeval t ((1 / n ! : ℚ) • Polynomial.bernoulli n)) *
        bernoulliPowerSeries_mul_exp_sub_one A

/-- **Shifted midpoint generating series of Bernoulli polynomials**: shifting around `1 / 2`
factors out the even series `Â(X) = (X / 2) / sinh (X / 2)`, giving
`∑ Bₙ(1/2 + u) Xⁿ / n! = Â(X) · e^{uX}`. -/
theorem mk_aeval_inv_two_add_bernoulli_eq_aHatSeries_mul_rescale_exp (u : A) :
    (PowerSeries.mk fun n =>
      Polynomial.aeval (algebraMap ℚ A 2⁻¹ + u) ((1 / n ! : ℚ) • Polynomial.bernoulli n)) =
      aHatSeries A * PowerSeries.rescale u (PowerSeries.exp A) := by
  rw [mk_aeval_bernoulli_eq_bernoulliPowerSeries_mul_rescale_exp,
    ← PowerSeries.exp_mul_exp_eq_exp_add, ← mul_assoc,
    bernoulliPowerSeries_mul_rescale_exp_eq_aHatSeries]

end GeneratingSeries

/-- **Midpoint generating series of Bernoulli polynomials**: the exponential generating series of
`Bₙ(1/2)` is the Â series `Â(X)`. -/
theorem mk_aeval_inv_two_bernoulli_eq_aHatSeries (A : Type*) [CommRing A] [Algebra ℚ A] :
    (PowerSeries.mk fun n =>
      Polynomial.aeval (algebraMap ℚ A 2⁻¹) ((1 / n ! : ℚ) • Polynomial.bernoulli n)) =
      aHatSeries A := by
  simpa using mk_aeval_inv_two_add_bernoulli_eq_aHatSeries_mul_rescale_exp (A := A) 0

section Midpoint

/-- **Midpoint evaluation of Bernoulli polynomials**: `Bₙ(1/2) = (2 / 2ⁿ - 1) Bₙ` in `ℚ`. -/
theorem bernoulli_eval_inv_two (n : ℕ) :
    (Polynomial.bernoulli n).eval 2⁻¹ = (2 / 2 ^ n - 1) * bernoulli n := by
  have h := congrArg (PowerSeries.coeff n) (mk_aeval_inv_two_bernoulli_eq_aHatSeries ℚ)
  simp only [PowerSeries.coeff_mk, coeff_aHatSeries, Algebra.algebraMap_self, RingHom.id_apply,
    Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_id,
    Polynomial.eval_smul, smul_eq_mul, one_div] at h
  have hne : (n ! : ℚ) ≠ 0 := mod_cast Nat.factorial_ne_zero n
  exact mul_left_cancel₀ (inv_ne_zero hne) (by linear_combination h)

/-- Odd-degree Bernoulli polynomials vanish at `1 / 2`. -/
@[simp]
theorem bernoulli_eval_inv_two_eq_zero_of_odd {n : ℕ} (hn : Odd n) :
    (Polynomial.bernoulli n).eval 2⁻¹ = 0 := by
  have h := Polynomial.bernoulli_eval_one_sub n 2⁻¹
  rw [hn.neg_one_pow] at h
  norm_num at h
  linarith

/-- Scaled midpoint evaluation of Bernoulli polynomials: `2ⁿ Bₙ(1/2) = (2 - 2ⁿ) Bₙ`. -/
theorem two_pow_mul_bernoulli_eval_inv_two (n : ℕ) :
    2 ^ n * (Polynomial.bernoulli n).eval 2⁻¹ = (2 - 2 ^ n) * bernoulli n := by
  rw [bernoulli_eval_inv_two]
  field_simp

/-- Binomial transform of `2ʲ Bⱼ`: `∑_{j ≤ n} C(n, j) 2ʲ Bⱼ = 2ⁿ Bₙ(1/2)`. -/
theorem sum_choose_mul_two_pow_mul_bernoulli (n : ℕ) :
    ∑ j ∈ range (n + 1), (n.choose j : ℚ) * 2 ^ j * bernoulli j =
      2 ^ n * (Polynomial.bernoulli n).eval 2⁻¹ := by
  rw [Polynomial.bernoulli, Polynomial.eval_finsetSum, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hle : j ≤ n := mem_range_succ_iff.mp hj
  rw [Polynomial.eval_monomial]
  have hpow : (2 : ℚ) ^ n * (2⁻¹ : ℚ) ^ (n - j) = 2 ^ j := by
    have hsplit : (2 : ℚ) ^ n = 2 ^ j * 2 ^ (n - j) := by
      rw [← pow_add, Nat.add_sub_of_le hle]
    rw [hsplit, mul_assoc, ← mul_pow]
    norm_num
  linear_combination bernoulli j * (n.choose j : ℚ) * hpow.symm

end Midpoint

end TauCeti
