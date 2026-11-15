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
  by_cases hd : d ∣ D.natAbs
  · rw [factorsThrough_iff_ker_unitsMap hd, factorsThrough_iff_ker_unitsMap hd]
    suffices (fundamentalDiscriminantCharCast R D hD).toUnitHom.ker =
        (fundamentalDiscriminantChar D hD).toUnitHom.ker by rw [this]
    ext u
    simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one,
      fundamentalDiscriminantCharCast_apply]
    rcases (fundamentalDiscriminantChar_isQuadratic hD).apply_eq_one_or_eq_neg_one u.isUnit with
      hu | hu
    · simp [hu]
    · rw [hu, Int.cast_neg, Int.cast_one]
      refine iff_of_false (fun h ↦ NeZero.ne (2 : R) ?_) (by norm_num)
      rwa [neg_eq_iff_add_eq_zero, one_add_one_eq_two] at h
  · exact iff_of_false (mt FactorsThrough.dvd hd) (mt FactorsThrough.dvd hd)

/-- When `2 ≠ 0` in `R`, the realized character has conductor `|D|`. -/
@[simp] theorem conductor_fundamentalDiscriminantCharCast (hD : Int.IsFundamentalDiscr D) :
    (fundamentalDiscriminantCharCast R D hD).conductor = D.natAbs := by
  have hcond : (fundamentalDiscriminantCharCast R D hD).conductor =
      (fundamentalDiscriminantChar D hD).conductor :=
    congrArg sInf (Set.ext fun _ ↦ factorsThrough_fundamentalDiscriminantCharCast_iff hD)
  exact hcond.trans ((isPrimitive_def _).mp (isPrimitive_fundamentalDiscriminantChar hD))

/-- When `2 ≠ 0` in `R`, the scalar realization is primitive at its actual level `|D|`. -/
theorem isPrimitive_fundamentalDiscriminantCharCast (hD : Int.IsFundamentalDiscr D) :
    (fundamentalDiscriminantCharCast R D hD).IsPrimitive :=
  (isPrimitive_def _).mpr (conductor_fundamentalDiscriminantCharCast hD)

/-- When `2 ≠ 0` in `R`, the scalar realization is principal if and only if `D = 1`. -/
@[simp] theorem fundamentalDiscriminantCharCast_eq_one_iff (hD : Int.IsFundamentalDiscr D) :
    fundamentalDiscriminantCharCast R D hD = 1 ↔ D = 1 := by
  have := hD.neZero_natAbs
  rw [eq_one_iff_conductor_eq_one, conductor_fundamentalDiscriminantCharCast, hD.natAbs_eq_one_iff]

end TauCeti.Multiquadratic
