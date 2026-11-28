/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.LocalField.Unramified.Character
public import Mathlib.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Examples of smooth characters of `p`-adic groups

For `t ∈ Aˣ`, the character `x ↦ t ^ v_p(x)` of `ℚ_p^×`, which is the unramified character
`TauCeti.unramifiedCharacter ℚ_[p] t`, is smooth, because the valuation is locally constant. An
injective character of the additive group `ℤ_p` is not smooth, whatever its coefficients: its
kernel is trivial, and `{0}` is not open in `ℤ_p`, since `p ^ n → 0`. In particular
`x ↦ (1 + p) ^ x`, and every injective character `ℤ_p → ℤ_p^×`, is not smooth.
-/

public section

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {A : Type*} [Monoid A]

/-- The unramified character `TauCeti.unramifiedCharacter ℚ_[p] t` is `x ↦ t ^ v_p(x)`. -/
example [TopologicalSpace Aˣ] (t : Aˣ) (x : ℚ_[p]ˣ) :
    unramifiedCharacter ℚ_[p] t x = t ^ (x : ℚ_[p]).valuation := by
  rw [unramifiedCharacter_apply, Padic.toAdd_normalizedValuation_eq_valuation]

/-- `x ↦ t ^ v_p(x)` is a smooth character of `ℚ_p^×`. -/
example [TopologicalSpace Aˣ] (t : Aˣ) :
    IsSmoothCharacter (unramifiedCharacter ℚ_[p] t : ℚ_[p]ˣ →* Aˣ) :=
  isSmoothCharacter_unramifiedCharacter ℚ_[p] t

/-- An injective character of `ℤ_p` is not smooth, whatever its coefficients. -/
example (χ : Multiplicative ℤ_[p] →* Aˣ) (hχ : Function.Injective χ) : ¬IsSmoothCharacter χ :=
  fun h ↦ PadicInt.not_isOpen_singleton_one_multiplicative (h.isOpen_singleton_one_of_injective hχ)

end TauCeti
