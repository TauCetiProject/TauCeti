/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Complex
public import TauCeti.Algebra.AddCircle
public import TauCeti.Analysis.SpecialFunctions.Complex.Circle

/-!
# Complex values of characters of finite fields

Mathlib's `AddChar.FiniteField.primitiveChar_to_Complex` is the canonical primitive additive
character of a finite field `F` with values in `ℂ`, and
`AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive` records its primitivity. Consumers
that just need *some* nontrivial additive character of `F` — character sums over `F`, the
cuspidal characters of `GL₂(F)` — want the weaker statement that it differs from the trivial
character, which is primitivity read at the shift by `1`.

A Legendre symbol `(θ/p) = ±1` is also an eighth root of unity, `e^{2πi · 2(1 - (θ/p))/8}`; this is
the form in which it enters the Gauss-sum invariants of finite quadratic modules, which take values
in `ℤ/8`.

## Main results

* `TauCeti.primitiveChar_to_Complex_ne_one`:
  `AddChar.FiniteField.primitiveChar_to_Complex F ≠ 1`.
* `TauCeti.legendreSym_eq_expCircle`: `(θ/p) = e^{2πi · 2(1 - (θ/p))/8}` for `θ` prime to `p`.
-/

public section

namespace TauCeti

variable (F : Type*) [Field F] [Finite F]

/-- Mathlib's canonical primitive complex additive character of a finite field is nontrivial. -/
theorem primitiveChar_to_Complex_ne_one :
    AddChar.FiniteField.primitiveChar_to_Complex F ≠ 1 := by
  simpa only [AddChar.mulShift_one] using
    AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F (one_ne_zero : (1 : F) ≠ 0)

/-- A Legendre symbol `(θ/p) = ±1` is `e^{2πi · 2(1 - (θ/p))/8}`. -/
theorem legendreSym_eq_expCircle {p : ℕ} [Fact p.Prime] {θ : ℤ} (hθ : (θ : ZMod p) ≠ 0) :
    (legendreSym p θ : ℂ) =
      expCircle (ZMod.toRatAddCircle 8 ((2 * (1 - legendreSym p θ) : ℤ) : ZMod 8)) := by
  rcases legendreSym.eq_one_or_neg_one p hθ with h | h <;> rw [h]
  · simp
  · rw [show ((2 * (1 - -1) : ℤ) : ZMod 8) = ((4 : ℕ) : ZMod 8) by decide,
      ZMod.toRatAddCircle_natCast, show ((4 : ℕ) : ℚ) / (8 : ℕ) = 1 / 2 by norm_num,
      expCircle_one_div_two, Int.cast_neg, Int.cast_one]

end TauCeti
