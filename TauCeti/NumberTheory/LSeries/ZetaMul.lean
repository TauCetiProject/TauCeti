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

## References

* The proof of `DirichletCharacter.LSeries_zetaMul` follows the private lemma
  `DirichletCharacter.BadChar.F_eq_LSeries` of Mathlib's
  `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`.
-/

public section

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

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

end DirichletCharacter
