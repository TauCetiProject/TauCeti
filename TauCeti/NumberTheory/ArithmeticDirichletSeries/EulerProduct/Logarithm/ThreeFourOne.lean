/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Basic
public import TauCeti.NumberTheory.LSeries.ThreeFourOne

/-!
# The `3-4-1` inequality for the `L`-series of a unitary ideal weight

For a unitary ideal weight `χ` of a number field `K`, a real `σ > 1` and a real `t`, the three
`L`-series of the family `1`, `χ`, `χ ^ 2` read at `σ`, `σ + it` and `σ + 2it` satisfy

```text
‖ζ_K(σ) ^ 3 * L(χ, σ + it) ^ 4 * L(χ ^ 2, σ + 2it)‖ ≥ 1.
```

The inequality is an Euler-product identity read termwise. At a height-one prime `P` of absolute
norm `x ≥ 2` the three local ratios are `x ^ (-σ)` times the phases `1`, `z` and `z ^ 2`, where
`z = χ(P) x ^ (-it)` has modulus at most one, so the weights `3`, `4`, `1` meet the elementary
positivity `3 + 4 cos θ + cos 2θ ≥ 0` in the form
`TauCeti.LSeries.threeFourOne_re_neg_log_one_sub_div_cpow_nonneg`. Summing over the primes and
exponentiating gives the displayed bound.

Everything happens strictly to the right of the line `Re s = 1`, where all three series converge
absolutely; no analytic continuation is used and none is asserted. This is the positivity half of
the classical argument for the nonvanishing of `L(χ, s)` on `Re s = 1`. Completing that argument
would additionally require the behaviour of the three factors as `σ → 1⁺`, and hence continuations
of `L(χ, ·)` and `L(χ ^ 2, ·)` across that line; no such continuation is constructed or assumed
here.

## Main results

* `TauCeti.UnitaryIdealWeight.norm_threeFourOne_product_ge_one`: the displayed inequality.

## Provenance

The argument follows Mathlib's `DirichletCharacter.norm_LSeries_product_ge_one` in
`Mathlib/NumberTheory/LSeries/Nonvanishing.lean`, by Michael Stoll and David Loeffler, replacing
the Euler product over the rational primes by the ideal Euler product over the height-one primes
of `𝓞 K`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 4.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII §8.
-/

public section

namespace TauCeti

open Complex IsDedekindDomain

open scoped NumberField

namespace UnitaryIdealWeight

variable {K : Type*} [Field K] [NumberField K]

/-- The `3-4-1` combination of the local Euler logarithms at a single prime is nonnegative. -/
private theorem threeFourOne_local_nonneg (χ : UnitaryIdealWeight K) {σ : ℝ} (hσ : 0 < σ)
    (t : ℝ) (P : HeightOneSpectrum (𝓞 K)) :
    0 ≤ 3 * (-log (1 - (1 : UnitaryIdealWeight K).1 P.asIdeal /
            (Ideal.absNorm P.asIdeal : ℂ) ^ (σ : ℂ))).re +
          4 * (-log (1 - χ.1 P.asIdeal /
            (Ideal.absNorm P.asIdeal : ℂ) ^ ((σ : ℂ) + I * t))).re +
          (-log (1 - (χ * χ).1 P.asIdeal /
            (Ideal.absNorm P.asIdeal : ℂ) ^ ((σ : ℂ) + 2 * I * t))).re := by
  have hx : (1 : ℝ) < (Ideal.absNorm P.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm P
  have hone : (1 : UnitaryIdealWeight K).1 P.asIdeal = 1 := by simp [P.ne_bot]
  have hsq : (χ * χ).1 P.asIdeal = χ.1 P.asIdeal ^ 2 := by
    rw [val_mul, MultiplicativeIdealWeight.mul_apply, sq]
  rw [hone, hsq]
  exact LSeries.threeFourOne_re_neg_log_one_sub_div_cpow_nonneg hx hσ t (χ.norm_le_one _)

/-- **The `3-4-1` inequality for the `L`-series of a unitary ideal weight.** For `σ > 1` and real
`t`, the Dedekind zeta function of `K` at `σ`, the `L`-series of `χ` at `σ + it` and the
`L`-series of `χ ^ 2` at `σ + 2it` satisfy
`‖ζ_K(σ) ^ 3 * L(χ, σ + it) ^ 4 * L(χ ^ 2, σ + 2it)‖ ≥ 1`.

The bound holds on the whole open half-plane of absolute convergence and uses no continuation;
it is the positivity input to the nonvanishing of `L(χ, ·)` on the line `Re s = 1`. -/
theorem norm_threeFourOne_product_ge_one (χ : UnitaryIdealWeight K) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    1 ≤ ‖NumberField.dedekindZeta K (σ : ℂ) ^ 3 *
        LSeries (normCoeff K χ.toIdealArithmeticFunction) ((σ : ℂ) + I * t) ^ 4 *
        LSeries (normCoeff K (χ ^ 2).toIdealArithmeticFunction) ((σ : ℂ) + 2 * I * t)‖ := by
  rw [pow_two χ]
  -- A unitary weight converges absolutely on `Re s > 1`, at each of the three points.
  have hs0 : Summable
      (idealTerm K (1 : UnitaryIdealWeight K).1.toIdealArithmeticFunction (σ : ℂ)) := by
    rw [← toIdealArithmeticFunction_eq_val]
    exact summable_idealTerm_of_unitary_of_one_lt_re 1 (by simpa using hσ)
  have hs1 : Summable (idealTerm K χ.1.toIdealArithmeticFunction ((σ : ℂ) + I * t)) := by
    rw [← toIdealArithmeticFunction_eq_val]
    exact summable_idealTerm_of_unitary_of_one_lt_re χ (by simpa using hσ)
  have hs2 : Summable (idealTerm K (χ * χ).1.toIdealArithmeticFunction ((σ : ℂ) + 2 * I * t)) := by
    rw [← toIdealArithmeticFunction_eq_val]
    exact summable_idealTerm_of_unitary_of_one_lt_re (χ * χ) (by simpa using hσ)
  have hzeta : NumberField.dedekindZeta K (σ : ℂ) =
      LSeries (normCoeff K (1 : UnitaryIdealWeight K).1.toIdealArithmeticFunction) (σ : ℂ) := by
    rw [val_one, MultiplicativeIdealWeight.toIdealArithmeticFunction_one,
      dedekindZeta_eq_LSeries_normCoeff_one]
  rw [norm_mul, norm_mul, norm_pow, norm_pow, hzeta, toIdealArithmeticFunction_eq_val,
    toIdealArithmeticFunction_eq_val,
    (1 : UnitaryIdealWeight K).1.norm_LSeries_eq_exp_tsum_re_neg_log_one_sub hs0,
    χ.1.norm_LSeries_eq_exp_tsum_re_neg_log_one_sub hs1,
    (χ * χ).1.norm_LSeries_eq_exp_tsum_re_neg_log_one_sub hs2,
    ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add,
    Real.one_le_exp_iff]
  have hsum0 := ((1 : UnitaryIdealWeight K).1.summable_re_neg_log_one_sub hs0).mul_left 3
  have hsum1 := (χ.1.summable_re_neg_log_one_sub hs1).mul_left 4
  have hsum2 := (χ * χ).1.summable_re_neg_log_one_sub hs2
  push_cast
  rw [← tsum_mul_left, ← tsum_mul_left, ← hsum0.tsum_add hsum1,
    ← (hsum0.add hsum1).tsum_add hsum2]
  exact tsum_nonneg fun P ↦ threeFourOne_local_nonneg χ (zero_lt_one.trans hσ) t P

end UnitaryIdealWeight

end TauCeti
