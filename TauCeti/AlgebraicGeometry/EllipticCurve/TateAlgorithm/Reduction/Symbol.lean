/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

/-!
# Reduction symbols in Tate's algorithm

This file defines the output symbols of Tate's algorithm and the component count attached to
each symbol. The count is the input to the algorithmic Ogg exponent.

The family `I n` includes `I 0` (good reduction) and `I n` for positive `n`; `IStar n`
includes `I₀*` at `n = 0` and `Iₙ*` for positive `n`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

namespace TauCeti

/-- The reduction symbols output by Tate's algorithm. The parameterized families encode `Iₙ`
and `Iₙ*`; their zero cases are `I₀` and `I₀*`. -/
inductive ReductionSymbol where
  /-- The `Iₙ` family, with `I₀` denoting good reduction. -/
  | I (n : ℕ)
  /-- The additive reduction symbol `II`. -/
  | II
  /-- The additive reduction symbol `III`. -/
  | III
  /-- The additive reduction symbol `IV`. -/
  | IV
  /-- The additive family `Iₙ*`, with `I₀*` at `n = 0`. -/
  | IStar (n : ℕ)
  /-- The additive reduction symbol `IV*`. -/
  | IVStar
  /-- The additive reduction symbol `III*`. -/
  | IIIStar
  /-- The additive reduction symbol `II*`. -/
  | IIStar
  deriving DecidableEq, Repr

namespace ReductionSymbol

/-- The number of geometric irreducible components specified by a reduction symbol. -/
def componentCount : ReductionSymbol → ℕ
  | .I n => max 1 n
  | .II => 1
  | .III => 2
  | .IV => 3
  | .IStar n => n + 5
  | .IVStar => 7
  | .IIIStar => 8
  | .IIStar => 9

@[simp]
theorem componentCount_I (n : ℕ) : (I n).componentCount = max 1 n := (rfl)

@[simp]
theorem componentCount_II : II.componentCount = 1 := (rfl)

@[simp]
theorem componentCount_III : III.componentCount = 2 := (rfl)

@[simp]
theorem componentCount_IV : IV.componentCount = 3 := (rfl)

@[simp]
theorem componentCount_IStar (n : ℕ) : (IStar n).componentCount = n + 5 := (rfl)

@[simp]
theorem componentCount_IVStar : IVStar.componentCount = 7 := (rfl)

@[simp]
theorem componentCount_IIIStar : IIIStar.componentCount = 8 := (rfl)

@[simp]
theorem componentCount_IIStar : IIStar.componentCount = 9 := (rfl)

/-- Every reduction symbol has at least one component. -/
theorem componentCount_pos (symbol : ReductionSymbol) : 0 < symbol.componentCount := by
  cases symbol <;> simp

/-- The algorithmic Ogg exponent attached to a symbol and a minimal discriminant
valuation `vΔ`: `vΔ - m + 1`, where `m` is the component count. It is integer-valued so that the
formula remains exact for arbitrary inputs; when the symbol and equation come from Tate's
algorithm, its branch conditions ensure this exponent is nonnegative. -/
def algorithmicOggExponent (symbol : ReductionSymbol) (vΔ : ℕ) : ℤ :=
  (vΔ : ℤ) - (symbol.componentCount : ℤ) + 1

/-- The exponent is the discriminant valuation minus the component count plus one. -/
theorem algorithmicOggExponent_def (symbol : ReductionSymbol) (vΔ : ℕ) :
    symbol.algorithmicOggExponent vΔ =
      (vΔ : ℤ) - (symbol.componentCount : ℤ) + 1 := (rfl)

/-- The good reduction symbol `I₀` has Ogg exponent `vΔ`; in particular it is zero at
valuation zero. -/
@[simp]
theorem algorithmicOggExponent_I_zero (vΔ : ℕ) :
    (I 0).algorithmicOggExponent vΔ = vΔ := by
  simp [algorithmicOggExponent]

/-- A multiplicative symbol `Iₙ`, `n ≠ 0`, has Ogg exponent `vΔ - n + 1`; in particular it is
one when the minimal discriminant valuation is `n`. -/
@[simp]
theorem algorithmicOggExponent_I {n : ℕ} (hn : n ≠ 0) (vΔ : ℕ) :
    (I n).algorithmicOggExponent vΔ = (vΔ : ℤ) - n + 1 := by
  simp [algorithmicOggExponent, Nat.one_le_iff_ne_zero.2 hn]

/-- The additive symbol `II` has Ogg exponent `vΔ`. -/
@[simp]
theorem algorithmicOggExponent_II (vΔ : ℕ) :
    II.algorithmicOggExponent vΔ = vΔ := by
  simp [algorithmicOggExponent]

/-- The additive symbol `III` has Ogg exponent `vΔ - 1`. -/
@[simp]
theorem algorithmicOggExponent_III (vΔ : ℕ) :
    III.algorithmicOggExponent vΔ = (vΔ : ℤ) - 1 := by
  simp [algorithmicOggExponent, sub_add]

/-- The additive symbol `IV` has Ogg exponent `vΔ - 2`. -/
@[simp]
theorem algorithmicOggExponent_IV (vΔ : ℕ) :
    IV.algorithmicOggExponent vΔ = (vΔ : ℤ) - 2 := by
  simp [algorithmicOggExponent, sub_add]

/-- The additive symbol `Iₙ*` has Ogg exponent `vΔ - n - 4`. -/
@[simp]
theorem algorithmicOggExponent_IStar (n vΔ : ℕ) :
    (IStar n).algorithmicOggExponent vΔ = (vΔ : ℤ) - n - 4 := by
  simp [algorithmicOggExponent]
  ring

/-- The additive symbol `IV*` has Ogg exponent `vΔ - 6`. -/
@[simp]
theorem algorithmicOggExponent_IVStar (vΔ : ℕ) :
    IVStar.algorithmicOggExponent vΔ = (vΔ : ℤ) - 6 := by
  simp [algorithmicOggExponent, sub_add]

/-- The additive symbol `III*` has Ogg exponent `vΔ - 7`. -/
@[simp]
theorem algorithmicOggExponent_IIIStar (vΔ : ℕ) :
    IIIStar.algorithmicOggExponent vΔ = (vΔ : ℤ) - 7 := by
  simp [algorithmicOggExponent, sub_add]

/-- The additive symbol `II*` has Ogg exponent `vΔ - 8`. -/
@[simp]
theorem algorithmicOggExponent_IIStar (vΔ : ℕ) :
    IIStar.algorithmicOggExponent vΔ = (vΔ : ℤ) - 8 := by
  simp [algorithmicOggExponent, sub_add]

end ReductionSymbol
end TauCeti

end
