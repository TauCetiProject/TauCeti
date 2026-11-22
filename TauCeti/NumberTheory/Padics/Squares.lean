/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.RingTheory.Henselian.SquareClasses

/-!
# Squares of `p`-adic units

At an odd prime `p` the ring `ℤ_p` is Henselian with residue field `ℤ/p` and `2` is a unit, so a
unit of `ℤ_p` is a square exactly when its reduction modulo `p` is a square
(`PadicInt.isSquare_iff_isSquare_toZMod`). Hence the square classes of `ℤ_pˣ` are read off the
Legendre symbol of an integer congruent to the unit modulo `p`.

At every prime, a unit `a` of `ℤ_p` whose product `a pⁿ` with a power of `p` is a square is itself
a square (`PadicInt.isSquare_of_isUnit_of_mul_pow_eq_sq`): a square has even valuation, so
`n = 2k` and the square root is `p^k` times a unit. This is how the unit part of a determinant,
known only up to a power of `p`, is compared with a square.

## Main results

* `PadicInt.isSquare_iff_isSquare_toZMod`: at an odd prime, a unit of `ℤ_p` is a square exactly when
  its reduction modulo `p` is.
* `PadicInt.isSquare_of_isUnit_of_mul_pow_eq_sq`: a unit whose product with a power of `p` is a
  square is a square.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter II, §3.3.
-/

public section

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- **Squares of units at an odd prime.** A unit of `ℤ_p`, for an odd prime `p`, is a square
exactly when its reduction modulo `p` is a square. -/
theorem isSquare_iff_isSquare_toZMod (hp : p ≠ 2) {x : ℤ_[p]} (hx : IsUnit x) :
    IsSquare x ↔ IsSquare (toZMod x) := by
  rw [TauCeti.HenselianLocalRing.isSquare_iff_residue_isSquare (isUnit_two hp) hx,
    toZMod_eq_residueField_comp_residue, RingHom.comp_apply]
  refine ⟨fun h ↦ h.map residueField.toRingHom, fun h ↦ ?_⟩
  simpa using h.map residueField.symm.toRingHom

/-- A unit of `ℤ_p` whose product with a power of `p` is a square is itself a square. -/
theorem isSquare_of_isUnit_of_mul_pow_eq_sq {a s : ℤ_[p]} (ha : IsUnit a) {n : ℕ}
    (h : a * (p : ℤ_[p]) ^ n = s ^ 2) : IsSquare a := by
  have hp0 : (p : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hs : s ≠ 0 := by
    rintro rfl
    simp [ha.ne_zero, hp0] at h
  have hval : a.valuation = 0 := by
    obtain ⟨a, rfl⟩ := ha
    have h1 := congrArg valuation a.mul_inv
    rw [valuation_mul a.ne_zero a⁻¹.ne_zero, valuation_one] at h1
    omega
  -- Comparing valuations gives `n = 2 v(s)`, and then `s = t pᵛ⁽ˢ⁾` with `t` a unit.
  have hn : n = 2 * s.valuation := by
    have h1 := congrArg valuation h
    rw [valuation_mul ha.ne_zero (pow_ne_zero n hp0), hval, valuation_pow, valuation_pow,
      valuation_p] at h1
    omega
  refine ⟨unitCoeff hs, mul_right_cancel₀ (pow_ne_zero n hp0) ?_⟩
  rw [h]
  conv_lhs => rw [unitCoeff_spec hs]
  rw [hn, pow_mul]
  ring

end PadicInt
