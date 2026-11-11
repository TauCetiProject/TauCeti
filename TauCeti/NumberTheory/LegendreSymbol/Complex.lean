/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Complex
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import TauCeti.Algebra.AddCircle
public import TauCeti.Analysis.SpecialFunctions.Complex.Circle.Basic

/-!
# Complex values of characters of finite fields

Mathlib's `AddChar.FiniteField.primitiveChar_to_Complex` is the canonical primitive additive
character of a finite field `F` with values in `ℂ`, and
`AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive` records its primitivity. Its values are
roots of unity, hence algebraic integers, so `F` also has a primitive additive character with
values in the ring `integralClosure ℤ ℂ` of algebraic integers of `ℂ`; Gauss sums of characters of
residue fields of a number field can then be read in a domain containing its ring of integers.

A Legendre symbol `(θ/p) = ±1` is also an eighth root of unity, `e^{2πi · 2(1 - (θ/p))/8}`; this is
the form in which it enters the Gauss-sum invariants of finite quadratic modules, which take values
in `ℤ/8`.

## Main results

* `TauCeti.exists_primitive_addChar_integralClosure`: `F` has a primitive additive character with
  values in the algebraic integers of `ℂ`.
* `TauCeti.legendreSym_eq_expCircle`: `(θ/p) = e^{2πi · 2(1 - (θ/p))/8}` for `θ` prime to `p`.
-/

public section

namespace TauCeti

variable (F : Type*) [Field F] [Finite F]

/-- A finite field has a primitive additive character with values in the ring of algebraic
integers of `ℂ`: the values of `AddChar.FiniteField.primitiveChar_to_Complex` are roots of unity. -/
theorem exists_primitive_addChar_integralClosure :
    ∃ ψ : AddChar F (integralClosure ℤ ℂ), ψ.IsPrimitive := by
  let ψ₀ := AddChar.FiniteField.primitiveChar_to_Complex F
  refine ⟨{ toFun t := ⟨ψ₀ t, IsIntegral.of_pow Nat.card_pos <| by
              rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero', AddChar.map_zero_eq_one]
              exact isIntegral_one⟩
            map_zero_eq_one' := Subtype.ext ψ₀.map_zero_eq_one
            map_add_eq_mul' a b := Subtype.ext (ψ₀.map_add_eq_mul a b) }, fun a ha h => ?_⟩
  exact AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F ha <|
    DFunLike.ext _ _ fun t => congrArg Subtype.val (DFunLike.congr_fun h t)

/-- A Legendre symbol `(θ/p) = ±1` is `e^{2πi · 2(1 - (θ/p))/8}`. -/
theorem legendreSym_eq_expCircle {p : ℕ} [Fact p.Prime] {θ : ℤ} (hθ : (θ : ZMod p) ≠ 0) :
    (legendreSym p θ : ℂ) =
      expCircle (ZMod.toRatAddCircle 8 ((2 * (1 - legendreSym p θ) : ℤ) : ZMod 8)) := by
  rcases legendreSym.eq_one_or_neg_one p hθ with h | h <;> rw [h]
  · simp
  · rw [ZMod.toRatAddCircle_intCast, show ((2 * (1 - -1) : ℤ) / (8 : ℕ) : ℚ) = 1 / 2 by norm_num,
      expCircle_one_div_two]
    simp

end TauCeti
