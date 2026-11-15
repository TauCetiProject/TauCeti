/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Character
public import TauCeti.NumberTheory.DirichletCharacter.Conductor

/-!
# Scalar realizations of fundamental-discriminant characters

The integer-valued character of a fundamental discriminant has compatible realizations over
commutative rings. Whenever `2 ≠ 0` in the coefficient ring (in particular in characteristic zero),
these realizations retain conductor `|D|`, are primitive and quadratic, and are nonprincipal
exactly when `D ≠ 1`. In particular the real and complex realizations have the same coefficients
under the canonical scalar embedding.

These comparisons let analytic Dirichlet-character APIs use precisely the character constructed
from prime discriminants, without choosing a second quadratic character.
-/

public section

namespace TauCeti.Multiquadratic

open DirichletCharacter

variable {D : ℤ}

/-- The character of a fundamental discriminant, with its integer values cast to `R`. -/
noncomputable def fundamentalDiscriminantCharCast (R : Type*) [CommRing R]
    (D : ℤ) (hD : Int.IsFundamentalDiscr D) : DirichletCharacter R D.natAbs :=
  (fundamentalDiscriminantChar D hD).ringHomComp (Int.castRingHom R)

/-- Scalar realization casts every coefficient of the integer-valued character. -/
@[simp] theorem fundamentalDiscriminantCharCast_apply {R : Type*} [CommRing R]
    (hD : Int.IsFundamentalDiscr D) (a : ZMod D.natAbs) :
    fundamentalDiscriminantCharCast R D hD a = (fundamentalDiscriminantChar D hD a : R) :=
  (rfl)

/-- Two equal fundamental discriminants give equal scalar-realized character values at every
integer. -/
theorem fundamentalDiscriminantCharCast_congr {R : Type*} [CommRing R] {D₁ D₂ : ℤ}
    (hD₁ : Int.IsFundamentalDiscr D₁) (hD₂ : Int.IsFundamentalDiscr D₂) (h : D₁ = D₂)
    (n : ℤ) :
    fundamentalDiscriminantCharCast R D₁ hD₁ n =
      fundamentalDiscriminantCharCast R D₂ hD₂ n := by
  subst h
  rfl

/-- Over `ℤ`, `fundamentalDiscriminantCharCast` is `fundamentalDiscriminantChar` itself. -/
@[simp] theorem fundamentalDiscriminantCharCast_int (hD : Int.IsFundamentalDiscr D) :
    fundamentalDiscriminantCharCast ℤ D hD = fundamentalDiscriminantChar D hD := by
  ext a
  simp

/-- Realizations commute with scalar maps, including the embedding of real into complex values. -/
@[simp] theorem fundamentalDiscriminantCharCast_ringHomComp {R S : Type*}
    [CommRing R] [CommRing S] (hD : Int.IsFundamentalDiscr D) (f : R →+* S) :
    (fundamentalDiscriminantCharCast R D hD).ringHomComp f =
      fundamentalDiscriminantCharCast S D hD := by
  ext a
  simp

/-- Every scalar realization remains quadratic. -/
theorem fundamentalDiscriminantCharCast_isQuadratic {R : Type*} [CommRing R]
    (hD : Int.IsFundamentalDiscr D) :
    (fundamentalDiscriminantCharCast R D hD).IsQuadratic :=
  (fundamentalDiscriminantChar_isQuadratic hD).comp (Int.castRingHom R)

/-- The scalar realization at `-1` is the cast of the sign of `D`. -/
theorem fundamentalDiscriminantCharCast_neg_one {R : Type*} [CommRing R]
    (hD : Int.IsFundamentalDiscr D) :
    fundamentalDiscriminantCharCast R D hD (-1) = D.sign := by
  rw [fundamentalDiscriminantCharCast_apply, fundamentalDiscriminantChar_neg_one]

/-- The scalar realization of the trivial fundamental discriminant `1` is principal over every
commutative ring. -/
@[simp] theorem fundamentalDiscriminantCharCast_one {R : Type*} [CommRing R]
    (hD : Int.IsFundamentalDiscr 1) :
    fundamentalDiscriminantCharCast R 1 hD = 1 := by
  exact @Subsingleton.elim (DirichletCharacter R 1) _ _ _

variable {R : Type*} [CommRing R] [NeZero (2 : R)]

/-- When `2 ≠ 0` in `R`, `fundamentalDiscriminantCharCast R D hD` factors through a divisor `d`
if and only if the integer-valued character does. -/
theorem factorsThrough_fundamentalDiscriminantCharCast_iff (hD : Int.IsFundamentalDiscr D)
    {d : ℕ} :
    (fundamentalDiscriminantCharCast R D hD).FactorsThrough d ↔
      (fundamentalDiscriminantChar D hD).FactorsThrough d := by
  have := hD.neZero_natAbs
  exact (fundamentalDiscriminantChar_isQuadratic hD).factorsThrough_ringHomComp_iff _

/-- When `2 ≠ 0` in `R`, the realized character has conductor `|D|`. -/
@[simp] theorem conductor_fundamentalDiscriminantCharCast (hD : Int.IsFundamentalDiscr D) :
    (fundamentalDiscriminantCharCast R D hD).conductor = D.natAbs :=
  ((fundamentalDiscriminantChar_isQuadratic hD).conductor_ringHomComp _).trans
    ((isPrimitive_def _).mp (isPrimitive_fundamentalDiscriminantChar hD))

/-- When `2 ≠ 0` in `R`, the scalar realization is primitive at its actual level `|D|`. -/
theorem isPrimitive_fundamentalDiscriminantCharCast (hD : Int.IsFundamentalDiscr D) :
    (fundamentalDiscriminantCharCast R D hD).IsPrimitive :=
  ((fundamentalDiscriminantChar_isQuadratic hD).isPrimitive_ringHomComp_iff _).mpr
    (isPrimitive_fundamentalDiscriminantChar hD)

/-- When `2 ≠ 0` in `R`, the scalar realization is principal if and only if `D = 1`. -/
@[simp] theorem fundamentalDiscriminantCharCast_eq_one_iff (hD : Int.IsFundamentalDiscr D) :
    fundamentalDiscriminantCharCast R D hD = 1 ↔ D = 1 := by
  have := hD.neZero_natAbs
  rw [fundamentalDiscriminantCharCast,
    (fundamentalDiscriminantChar_isQuadratic hD).ringHomComp_eq_one_iff,
    eq_one_iff_conductor_eq_one,
    (isPrimitive_def _).mp (isPrimitive_fundamentalDiscriminantChar hD), hD.natAbs_eq_one_iff]

end TauCeti.Multiquadratic
