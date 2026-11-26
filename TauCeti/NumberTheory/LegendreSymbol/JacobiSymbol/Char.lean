/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# The Jacobi symbol as a Dirichlet character of its denominator

For a fixed denominator `b ≠ 0`, the Jacobi symbol `a ↦ J(a | b)` is periodic modulo `b`
(`jacobiSym.mod_left'`), multiplicative in `a` (`jacobiSym.mul_left`) and vanishes exactly when
`gcd (a, b) ≠ 1` (`jacobiSym.eq_zero_iff_not_coprime`), so it is a Dirichlet character of
modulus `b`. For odd `b` this is the quadratic character `(· / b)`. The definition does not
require `b` to be odd.

This is the character with the denominator fixed; Tau Ceti's `kroneckerChar` fixes the
numerator instead.

## Main definitions and results

* `TauCeti.jacobiChar R b`: the Dirichlet character `a ↦ J(a | b)` of modulus `b`, with values in
  a commutative ring `R`.
* `TauCeti.jacobiChar_intCast`, `TauCeti.jacobiChar_natCast`: its value at the class of an integer
  or a natural number `a` is `J(a | b)`.
* `TauCeti.jacobiChar_eq_ringHomComp_quadraticChar`: at a prime modulus it is the quadratic
  character of `ZMod p`.
* `TauCeti.jacobiChar_mul`: it is multiplicative in the modulus.
* `TauCeti.changeLevel_jacobiChar_apply_units`: the same evaluation after lifting to a multiple
  `m` of `b`, at a unit of `ZMod m`.
* `TauCeti.jacobiChar_isQuadratic`: it takes only the values `0`, `1` and `-1`.
-/

public section

namespace TauCeti

variable (R : Type*) [CommRing R]

/-- The **Jacobi character** of modulus `b ≠ 0`: the Dirichlet character `a ↦ J(a | b)` with values
in a commutative ring `R`. It is well defined because `J(· | b)` is periodic modulo `b`
(`jacobiSym.mod_left'`) and multiplicative (`jacobiSym.mul_left`), and it vanishes off the units
because `J(a | b) = 0` when `gcd (a, b) ≠ 1` (`jacobiSym.eq_zero_iff_not_coprime`). -/
def jacobiChar (b : ℕ) [NeZero b] : DirichletCharacter R b where
  toFun x := (jacobiSym x.val b : R)
  map_one' := by
    rw [jacobiSym_val_eq_of_intCast_eq (a := 1) Int.cast_one, jacobiSym.one_left, Int.cast_one]
  map_mul' x y := by
    rw [jacobiSym_val_eq_of_intCast_eq (a := x.val * y.val) (by push_cast; simp),
      jacobiSym.mul_left, Int.cast_mul]
  map_nonunit' x hx := by
    rw [jacobiSym.eq_zero_iff_not_coprime.mpr, Int.cast_zero]
    intro h
    refine hx ?_
    rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime]
    rwa [Int.gcd_natCast_natCast] at h

variable {R} {b : ℕ} [NeZero b]

/-- The Jacobi character at `x : ZMod b` is the Jacobi symbol `J(x.val | b)`, by definition. -/
theorem jacobiChar_apply (x : ZMod b) : jacobiChar R b x = jacobiSym x.val b := by
  rfl

/-- The Jacobi character at the class of an integer `a` is the Jacobi symbol `J(a | b)`. -/
@[simp]
theorem jacobiChar_intCast (a : ℤ) : jacobiChar R b a = jacobiSym a b := by
  rw [jacobiChar_apply, jacobiSym_val_eq_of_intCast_eq rfl]

/-- The Jacobi character at the class of a natural number `n` is the Jacobi symbol `J(n | b)`. -/
@[simp]
theorem jacobiChar_natCast (n : ℕ) : jacobiChar R b n = jacobiSym n b := by
  rw [← jacobiChar_intCast, Int.cast_natCast]

/-- The Jacobi character lifted to a modulus `m ≠ 0` that `b` divides, at a unit `u` of
`ZMod m`, is the Jacobi symbol `J(u.val | b)` of the representative of `u` modulo `m`. -/
@[simp]
theorem changeLevel_jacobiChar_apply_units {m : ℕ} [NeZero m] (h : b ∣ m) (u : (ZMod m)ˣ) :
    (jacobiChar R b).changeLevel h u = jacobiSym (u : ZMod m).val b := by
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, ZMod.cast_eq_val, jacobiChar_natCast]

/-- At a prime modulus `p`, the Jacobi character is Mathlib's quadratic character of `ZMod p`
(the Legendre symbol), with values cast to `R`. -/
theorem jacobiChar_eq_ringHomComp_quadraticChar (p : ℕ) [Fact p.Prime] :
    jacobiChar R p = (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R) := by
  refine MulChar.ext' fun x ↦ ?_
  rw [jacobiChar_apply, ← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast,
    ZMod.natCast_zmod_val, MulChar.ringHomComp_apply, eq_intCast]

/-- The Jacobi character is multiplicative in its modulus: `J(· | a b) = J(· | a) J(· | b)`, with
the two factors lifted to modulus `a * b`. -/
theorem jacobiChar_mul (a b : ℕ) [NeZero a] [NeZero b] :
    jacobiChar R (a * b) = (jacobiChar R a).changeLevel (dvd_mul_right a b) *
      (jacobiChar R b).changeLevel (dvd_mul_left b a) := by
  refine MulChar.ext fun u ↦ ?_
  rw [MulChar.mul_apply, changeLevel_jacobiChar_apply_units, changeLevel_jacobiChar_apply_units,
    jacobiChar_apply, jacobiSym.mul_right, Int.cast_mul]

/-- The Jacobi character is quadratic: it takes only the values `0`, `1` and `-1`. -/
theorem jacobiChar_isQuadratic : (jacobiChar R b).IsQuadratic := by
  intro x
  rw [jacobiChar_apply]
  rcases jacobiSym.trichotomy x.val b with h | h | h <;> rw [h] <;> simp

end TauCeti
