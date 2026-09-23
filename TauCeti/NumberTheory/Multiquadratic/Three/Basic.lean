/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.NumberTheory.NumberField.Basic
import TauCeti.NumberTheory.NumberField.IntegralSqrt
import TauCeti.NumberTheory.NumberField.Quadratic.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Data.Rat.Lemmas

/-!
# The `AdjoinRoot (X² - 3)` model of `ℚ(√3)`

The concrete number field `AdjoinRoot (X² - 3)` serving as the canonical model of the real
quadratic field `ℚ(√3)`, together with its integral generator. This presentation datum is shared
by the class-number and `2`-rank computations for this field, so it lives here rather than in
either of them.

Unlike the imaginary quadratic models, where `X² - d` with `d < 0` has no rational root for sign
reasons, irreducibility here is the irrationality of `√3`: a rational square root of `3` would
make `3` a square in `ℤ` (`Rat.isSquare_intCast_iff`), contradicting its primality.

## Main results

* `TauCeti.NumberField.not_isSquare_three_rat`: `3` is not a square in `ℚ`.
* `TauCeti.NumberField.exists_minpoly_eq_X_sq_sub_three_and_adjoin_eq_top`: the model has an
  integral generator with minimal polynomial `X² - 3` generating the field over `ℚ`.
-/

public section

open NumberField Polynomial
open scoped NumberField

namespace TauCeti.NumberField

/-- **`3` is not a square in `ℚ`**, the arithmetic input that makes `ℚ(√3)` a quadratic field:
a rational square root of `3` would make `3` a square in `ℤ` (`Rat.isSquare_intCast_iff`),
contradicting its primality. -/
theorem not_isSquare_three_rat : ¬ IsSquare ((3 : ℤ) : ℚ) := by
  rw [Rat.isSquare_intCast_iff]
  exact Int.prime_three.not_isSquare

/-- `X² - 3` is irreducible over `ℚ`, so `AdjoinRoot (X² - 3)` is a field. -/
instance irreducible_X_sq_sub_three : Fact (Irreducible (X ^ 2 - C (3 : ℚ))) := ⟨by
  refine (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr fun q hq => ?_
  exact not_isSquare_three_rat ⟨q, by push_cast; rw [← hq]; ring⟩⟩

/-- The concrete model `AdjoinRoot (X² - 3)` of `ℚ(√3)` carries an integral generator with minimal
polynomial `X² - 3` generating the field over `ℚ`: the presentation data shared by the
class-number and `2`-rank computations for this field. -/
theorem exists_minpoly_eq_X_sq_sub_three_and_adjoin_eq_top :
    ∃ θ : 𝓞 (AdjoinRoot (X ^ 2 - C (3 : ℚ))),
      minpoly ℤ θ = X ^ 2 - C (3 : ℤ) ∧
        Algebra.adjoin ℚ {(θ : AdjoinRoot (X ^ 2 - C (3 : ℚ)))} = ⊤ := by
  let K := AdjoinRoot (X ^ 2 - C (3 : ℚ))
  let x : K := AdjoinRoot.root (X ^ 2 - C (3 : ℚ))
  have hx : x ^ 2 = algebraMap ℤ K (3 : ℤ) := by
    rw [TauCeti.AdjoinRoot.root_sq, IsScalarTower.algebraMap_apply ℤ ℚ]
    norm_num
  refine ⟨integralSqrt hx, minpoly_integralSqrt hx not_isSquare_three_rat, ?_⟩
  have hθx : ((integralSqrt hx : 𝓞 K) : K) = x := algebraMap_integralSqrt hx
  rw [hθx]
  exact AdjoinRoot.adjoinRoot_eq_top

end TauCeti.NumberField
