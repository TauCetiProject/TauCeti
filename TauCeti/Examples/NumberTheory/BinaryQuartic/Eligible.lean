/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuartic.Eligible
import Mathlib.Data.ZMod.Basic

/-!
# Checks for binary quartic invariants and eligible pairs

These examples evaluate the invariants `I`, `J` and the discriminant `Δ` on explicit forms and
exercise the classification of eligible invariant pairs.

* `x³ y - x y³` has `(I, J, Δ) = (3, 0, 4)`, and `x⁴ - y⁴` has `(-12, 0, -256)`; the latter
  fixes the sign of `Δ`. The all-ones form has `(10, 25, 125)`, and `x⁴` has `(0, 0, 0)`.
* Over `𝔽₃` the form `x³ y - x y³` has `I = J = 0` but `Δ = 1`, so `27 Δ = 4 I³ - J²` does not
  determine `Δ` in characteristic three.
* Scaling by `2` multiplies `I` by `2² = 4`.
* `x³ y - x² y²` realizes `(1, 2)` and `x² y²` realizes `(1, -2)`, so the sign of `J` matters;
  `x³ y - y⁴` realizes `(0, 27)` and `x³ y + x² y² - x y³ - y⁴` realizes `(4, 16)`.
* `(1, 0)` is not eligible, no pair `(2, J)` is eligible, and translating by `(9, 27)`
  preserves eligibility and ineligibility, as for `(2, 0)` and `(11, 27)`.
-/

public section

open TauCeti TauCeti.BinaryQuartic

namespace TauCeti.Examples.NumberTheory.BinaryQuartic

/-! ### Invariants of explicit forms -/

/-- The form `x³ y - x y³`, with roots `0`, `±1` and `∞`. -/
abbrev xCubedYSubXYCubed (R : Type*) [CommRing R] : TauCeti.BinaryQuartic R := ![0, 1, 0, -1, 0]

example : invI (xCubedYSubXYCubed ℤ) = 3 := by simp [invI_def]
example : invJ (xCubedYSubXYCubed ℤ) = 0 := by simp [invJ_def]
example : disc (xCubedYSubXYCubed ℤ) = 4 := by simp [disc_def]

/-- Over `𝔽₃` the invariants of `x³ y - x y³` vanish but its discriminant does not. -/
example : invI (xCubedYSubXYCubed (ZMod 3)) = 0 ∧ invJ (xCubedYSubXYCubed (ZMod 3)) = 0 ∧
    disc (xCubedYSubXYCubed (ZMod 3)) = 1 := by
  simp only [invI_def, invJ_def, disc_def]
  decide

/-- `x⁴ - y⁴` has `I = -12`, `J = 0` and `Δ = -256`, the discriminant of `X⁴ - 1`. -/
example : invI (![1, 0, 0, 0, -1] : TauCeti.BinaryQuartic ℤ) = -12 ∧
    invJ (![1, 0, 0, 0, -1] : TauCeti.BinaryQuartic ℤ) = 0 ∧
    disc (![1, 0, 0, 0, -1] : TauCeti.BinaryQuartic ℤ) = -256 := by
  simp [invI_def, invJ_def, disc_def]

/-- The all-ones form `x⁴ + x³ y + x² y² + x y³ + y⁴`. -/
example : invI (![1, 1, 1, 1, 1] : TauCeti.BinaryQuartic ℤ) = 10 ∧
    invJ (![1, 1, 1, 1, 1] : TauCeti.BinaryQuartic ℤ) = 25 ∧
    disc (![1, 1, 1, 1, 1] : TauCeti.BinaryQuartic ℤ) = 125 := by
  simp [invI_def, invJ_def, disc_def]

/-- `x⁴` lies in the null cone. -/
example : invI (![1, 0, 0, 0, 0] : TauCeti.BinaryQuartic ℤ) = 0 ∧
    invJ (![1, 0, 0, 0, 0] : TauCeti.BinaryQuartic ℤ) = 0 ∧
    disc (![1, 0, 0, 0, 0] : TauCeti.BinaryQuartic ℤ) = 0 := by
  simp [invI_def, invJ_def, disc_def]

/-- Scaling `x³ y - x y³` by `2` multiplies `I` by `4`, not by `2`. -/
example : invI ((2 : ℤ) • xCubedYSubXYCubed ℤ) = 12 := by
  simp [invI_def]

/-! ### Eligible pairs -/

example : invI (![0, 1, -1, 0, 0] : TauCeti.BinaryQuartic ℤ) = 1 ∧
    invJ (![0, 1, -1, 0, 0] : TauCeti.BinaryQuartic ℤ) = 2 := by
  simp [invI_def, invJ_def]

/-- `x² y²` has `(I, J) = (1, -2)`. -/
example : invI (![0, 0, 1, 0, 0] : TauCeti.BinaryQuartic ℤ) = 1 ∧
    invJ (![0, 0, 1, 0, 0] : TauCeti.BinaryQuartic ℤ) = -2 := by
  simp [invI_def, invJ_def]

/-- `x³ y - y⁴` has `(I, J) = (0, 27)`. -/
example : invI (![0, 1, 0, 0, -1] : TauCeti.BinaryQuartic ℤ) = 0 ∧
    invJ (![0, 1, 0, 0, -1] : TauCeti.BinaryQuartic ℤ) = 27 := by
  simp [invI_def, invJ_def]

/-- `x³ y + x² y² - x y³ - y⁴` has `(I, J) = (4, 16)`. -/
example : invI (![0, 1, 1, -1, -1] : TauCeti.BinaryQuartic ℤ) = 4 ∧
    invJ (![0, 1, 1, -1, -1] : TauCeti.BinaryQuartic ℤ) = 16 := by
  simp [invI_def, invJ_def]

example : IsEligible 1 2 := by decide
example : IsEligible 0 0 := by decide
example : IsEligible 4 16 := by decide
example : ¬ IsEligible 1 0 := by decide
example : ¬ IsEligible 11 27 := by decide

/-- No pair with `I = 2` is eligible. -/
example (J : ℤ) : ¬ IsEligible 2 J := by
  rw [isEligible_iff_mem_eligibleResidues]
  generalize (J : ZMod 27) = j
  revert j
  decide

/-- Translating by `(9, 27)` preserves eligibility. -/
example (I J : ℤ) : IsEligible (I + 9) (J + 27) ↔ IsEligible I J := by
  have h9 : ((9 : ℤ) : ZMod 9) = 0 := rfl
  have h27 : ((27 : ℤ) : ZMod 27) = 0 := rfl
  simp only [isEligible_iff_mem_eligibleResidues, Int.cast_add, h9, h27, add_zero]

/-- Eligibility is preserved by the scaling `(I, J) ↦ (2⁴ I, 2⁶ J)`. -/
example {I J : ℤ} (h : IsEligible I J) : IsEligible (2 ^ 4 * I) (2 ^ 6 * J) := by
  simpa using h.sq_mul_pow_three_mul 4

end TauCeti.Examples.NumberTheory.BinaryQuartic
