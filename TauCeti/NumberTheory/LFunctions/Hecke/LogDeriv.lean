/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.ThreeFourOne
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Weight

/-!
# The `3-4-1` inequality for logarithmic derivatives of presented Hecke L-series

The negative logarithmic derivatives of the Hecke L-series of the principal character, of `χ`
and of `χ ^ 2`, all presented at the same modulus, satisfy the `3-4-1` inequality on
`Re s > 1`. Each character is extended by zero at ideals meeting the finite part of the modulus.
This is the case of
`TauCeti.UnitaryIdealWeight.threeFourOne_re_neg_logDeriv_LSeries_nonneg` in which `χ₀` is the
weight of the principal character, the indicator of the ideals prime to the modulus.

## References

* H. Davenport, *Multiplicative Number Theory*, §14, for the logarithmic derivative argument.
-/

public section

open Complex

namespace TauCeti.GlobalNumberFields.RayClassCharacter

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- **The logarithmic derivative `3-4-1` inequality.** For `σ > 1`, the real parts of the
negative logarithmic derivatives of `L(1, σ)`, `L(χ, σ + it)` and `L(χ², σ + 2it)` have
nonnegative weighted sum with weights `3`, `4` and `1`. All three series use the same modulus. -/
theorem threeFourOne_re_neg_logDeriv_LSeries_nonneg (χ : RayClassCharacter 𝔪) {σ : ℝ}
    (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (-logDeriv (LSeries (normCoeff K
        (1 : RayClassCharacter 𝔪).toUnitaryIdealWeight.toIdealArithmeticFunction)) σ).re +
      4 * (-logDeriv (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction))
        ((σ : ℂ) + I * t)).re +
      (-logDeriv (LSeries (normCoeff K (χ ^ 2).toUnitaryIdealWeight.toIdealArithmeticFunction))
        ((σ : ℂ) + 2 * I * t)).re := by
  rw [pow_two, toUnitaryIdealWeight_mul, ← pow_two,
    UnitaryIdealWeight.toIdealArithmeticFunction_eq_val
      (1 : RayClassCharacter 𝔪).toUnitaryIdealWeight]
  exact χ.toUnitaryIdealWeight.threeFourOne_re_neg_logDeriv_LSeries_nonneg
    (χ₀ := (1 : RayClassCharacter 𝔪).toUnitaryIdealWeight.val)
    (by
      rw [val_toUnitaryIdealWeight, toMultiplicativeIdealWeight_one]
      exact MultiplicativeIdealWeight.isTrivialOnGood_ofBadPrimes _)
    (by simp) hσ t

end TauCeti.GlobalNumberFields.RayClassCharacter
