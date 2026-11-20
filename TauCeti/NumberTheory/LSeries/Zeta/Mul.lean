/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The `L`-series of `ζ * χ`

For a Dirichlet character `χ`, Mathlib's `DirichletCharacter.zetaMul χ` is the Dirichlet
convolution `ζ * χ` of the constant function `1` with `χ`. On the half-plane `Re s > 1` its
`L`-series is `ζ(s) L(s, χ)`. For the character of a quadratic field this is the factorization of
its Dedekind zeta function (`TauCeti.NumberField.dedekindZeta_eq_riemannZeta_mul_LFunction`).

## Main results

* `DirichletCharacter.LSeries_zetaMul`: for every character `χ`, the `L`-series of `ζ * χ` is
  `ζ(s) L(s, χ)` on `Re s > 1`.
* `DirichletCharacter.zetaMul_prime_pow_of_eq_neg_one`: when `χ(p) = -1`, the prime-power
  coefficients of `ζ * χ` are `1` at even exponents and `0` at odd exponents.

## References

* The proof of `DirichletCharacter.LSeries_zetaMul` follows the private lemma
  `DirichletCharacter.BadChar.F_eq_LSeries` of Mathlib's
  `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`.
* The prime-power evaluation follows the calculation in Mathlib's
  `DirichletCharacter.zetaMul_prime_pow_nonneg` in the same file.
-/

public section

namespace DirichletCharacter

variable {N : ℕ}

/-- If `χ(p) = -1`, the coefficients of `ζ * χ` at powers of `p` are `1` at even exponents
and `0` at odd exponents. -/
theorem zetaMul_prime_pow_of_eq_neg_one {χ : DirichletCharacter ℂ N} {p : ℕ}
    (hp : p.Prime) (hχ : χ p = -1) (k : ℕ) :
    χ.zetaMul (p ^ k) = if _root_.Even k then 1 else 0 := by
  simp only [zetaMul, ArithmeticFunction.coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
  simp_rw [← χ.apply_eq_toArithmeticFunction_apply (pow_ne_zero _ hp.ne_zero),
    Nat.cast_pow, map_pow, hχ, neg_one_geom_sum]
  simp only [Nat.even_add_one, ite_not]

variable [NeZero N]

/-- **The `L`-series of `ζ * χ`.** On `Re s > 1`, the `L`-series of Mathlib's convolution
`DirichletCharacter.zetaMul χ` of the constant function `1` with `χ` is `ζ(s) L(s, χ)`. -/
theorem LSeries_zetaMul (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries χ.zetaMul s = riemannZeta s * χ.LFunction s := by
  rw [zetaMul, ← ArithmeticFunction.coe_mul, LSeries_convolution', χ.LFunction_eq_LSeries hs]
  · congr 1
    · simp_rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs,
        ← ArithmeticFunction.natCoe_apply]
    · exact (LSeries_congr χ.apply_eq_toArithmeticFunction_apply s).symm
  · exact ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  · exact (LSeriesSummable_congr _ fun h ↦ (χ.apply_eq_toArithmeticFunction_apply h).symm).mpr <|
      ZMod.LSeriesSummable_of_one_lt_re χ hs

/-- On `Re s > 1`, the convolution `ζ * χ` has an absolutely convergent Dirichlet series
with sum `ζ(s) L(s, χ)`. -/
theorem LSeriesHasSum_zetaMul (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum χ.zetaMul s (riemannZeta s * χ.LFunction s) := by
  rw [← LSeries_zetaMul χ hs]
  exact (χ.LSeriesSummable_zetaMul hs).LSeriesHasSum

end DirichletCharacter
