/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Character
public import TauCeti.NumberTheory.DirichletCharacter.Conductor
import TauCeti.Algebra.CharP.Lemmas

/-!
# Scalar realizations of fundamental-discriminant characters

The integer-valued character of a fundamental discriminant has compatible quadratic realizations
over commutative rings. Whenever `2 ≠ 0` in the coefficient ring, these realizations retain
conductor `|D|`, are primitive, and are nonprincipal exactly when `D ≠ 1`. In particular the real
and complex realizations have the same coefficients under the canonical scalar embedding.

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

variable {R : Type*} [CommRing R] [NeZero (2 : R)]

/-- Whenever `2 ≠ 0` in the coefficient ring, the scalar realization is primitive at its actual
level `|D|`. -/
theorem isPrimitive_fundamentalDiscriminantCharCast (hD : Int.IsFundamentalDiscr D) :
    (fundamentalDiscriminantCharCast R D hD).IsPrimitive := by
  have : Nontrivial R := NeZero.nontrivial (2 : R)
  simpa only [fundamentalDiscriminantCharCast, isPrimitive_def,
    conductor_ringHomComp_intCast _ (TauCeti.ringChar_ne_two_of_neZero_two R)] using
    isPrimitive_fundamentalDiscriminantChar hD

/-- Whenever `2 ≠ 0` in the coefficient ring, the realized character has conductor
exactly `|D|`. -/
@[simp] theorem conductor_fundamentalDiscriminantCharCast (hD : Int.IsFundamentalDiscr D) :
    (fundamentalDiscriminantCharCast R D hD).conductor = D.natAbs :=
  (isPrimitive_def _).mp (isPrimitive_fundamentalDiscriminantCharCast hD)

/-- Whenever `2 ≠ 0` in the coefficient ring, the realized character is principal exactly for the
discriminant `1`. -/
@[simp] theorem fundamentalDiscriminantCharCast_eq_one_iff (hD : Int.IsFundamentalDiscr D) :
    fundamentalDiscriminantCharCast R D hD = 1 ↔ D = 1 := by
  have := hD.neZero_natAbs
  rw [(isPrimitive_fundamentalDiscriminantCharCast hD).eq_one_iff, hD.natAbs_eq_one_iff]

end TauCeti.Multiquadratic
