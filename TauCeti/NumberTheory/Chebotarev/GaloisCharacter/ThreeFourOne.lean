/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Weight
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.ThreeFourOne

/-!
# The 3-4-1 bound for Galois character series

The Euler products of a Galois character, its square, and the trivial character satisfy the
classical 3-4-1 positivity inequality on `Re s > 1`. All three products omit exactly the primes
ramified in the extension. This lower bound is the positivity input for proving nonvanishing of
the continued character series on the line `Re s = 1`.

It is the specialization of `TauCeti.UnitaryIdealWeight.norm_LSeries_threeFourOne_ge_one` to the
unitary weight of a Galois character, measured against the weight of the trivial character: that
weight is trivial on its good ideals, and its bad primes, the ramified ones, are those of every
character weight.
-/

public section

namespace NumberField.Chebotarev

open Complex TauCeti

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- **The 3-4-1 bound for Galois character Euler products.** For `σ > 1`, the product of the
trivial-character series to the third power, the `χ`-series at `σ + it` to the fourth power, and
the `χ²`-series at `σ + 2it` has norm at least one. The Euler factors at ramified primes are
omitted in all three series. -/
theorem norm_galoisCharacterLSeries_threeFourOne_ge_one
    (χ : (L ≃ₐ[K] L) →* ℂˣ) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    1 ≤ ‖LSeries (normCoeff K
        (1 : (L ≃ₐ[K] L) →* ℂˣ).galoisCharacterWeight.toIdealArithmeticFunction) σ ^ 3 *
      LSeries (normCoeff K χ.galoisCharacterWeight.toIdealArithmeticFunction)
        ((σ : ℂ) + I * t) ^ 4 *
      LSeries (normCoeff K (χ ^ 2).galoisCharacterWeight.toIdealArithmeticFunction)
        ((σ : ℂ) + 2 * I * t)‖ := by
  have h₀ : (MonoidHom.galoisCharacterWeight (K := K) (L := L) 1).IsTrivialOnGood := by
    simpa using MultiplicativeIdealWeight.isTrivialOnGood_ofBadPrimes _
  have h := UnitaryIdealWeight.norm_LSeries_threeFourOne_ge_one
    (MonoidHom.galoisCharacterUnitaryWeight (L := L) χ) h₀ (by simp) hσ t
  simpa [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val, pow_two] using h

end NumberField.Chebotarev
