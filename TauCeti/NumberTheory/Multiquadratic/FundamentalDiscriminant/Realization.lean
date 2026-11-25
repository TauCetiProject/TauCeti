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

The integer-valued character of a fundamental discriminant has compatible quadratic realizations
over commutative rings, with the `ℤ`-realization recovering the character itself. At every odd
prime `p`, each realization takes the cast of `legendreSym p D`. Whenever `2 ≠ 0` in the
coefficient ring, its value at `p` is `-1` exactly when `D` is not a square modulo `p`, and these
realizations retain conductor `|D|`, are primitive, and are nonprincipal exactly when `D ≠ 1`. In
particular the real and complex realizations have the same coefficients under the canonical scalar
embedding, and each realization is the Kronecker character `(D / ·)` with values in its ring.

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

/-- The scalar realization of a fundamental-discriminant character is the Kronecker character
`(D / ·)` with values in `R`. -/
theorem fundamentalDiscriminantCharCast_eq_kroneckerChar {R : Type*} [CommRing R]
    (hD : Int.IsFundamentalDiscr D) (hD' : D ≡ 0 [ZMOD 4] ∨ D ≡ 1 [ZMOD 4]) :
    fundamentalDiscriminantCharCast R D hD = kroneckerChar R D hD' hD.ne_zero := by
  have := hD.neZero_natAbs
  refine MulChar.ext' fun a ↦ ?_
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective a
  simp [fundamentalDiscriminantCharCast_apply]

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

/-- The integer realization of a fundamental-discriminant character is the character itself. -/
@[simp] theorem fundamentalDiscriminantCharCast_int (hD : Int.IsFundamentalDiscr D) :
    fundamentalDiscriminantCharCast ℤ D hD = fundamentalDiscriminantChar D hD := by
  ext a
  simp

/-- At an odd prime `p`, every scalar realization of a fundamental-discriminant character takes
the cast of the Legendre symbol `legendreSym p D` (including `0` when `p ∣ D`). -/
theorem fundamentalDiscriminantCharCast_natCast_eq_legendreSym {R : Type*} [CommRing R]
    (hD : Int.IsFundamentalDiscr D) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    fundamentalDiscriminantCharCast R D hD p = (legendreSym p D : R) := by
  simpa [fundamentalDiscriminantCharCast_apply] using
    congrArg (Int.cast (R := R)) (fundamentalDiscriminantChar_natCast_eq_legendreSym hD hp)

variable {R : Type*} [CommRing R] [NeZero (2 : R)]

/-- When `2 ≠ 0` in `R`, at an odd prime `p`, the `R`-realization of a fundamental-discriminant
character takes the value `-1` if and only if `D` is not a square modulo `p`. -/
theorem fundamentalDiscriminantCharCast_natCast_eq_neg_one_iff (hD : Int.IsFundamentalDiscr D)
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    fundamentalDiscriminantCharCast R D hD p = -1 ↔ ¬ IsSquare (D : ZMod p) := by
  rw [fundamentalDiscriminantCharCast_natCast_eq_legendreSym hD hp,
    ← legendreSym.eq_neg_one_iff p]
  have h0 : (0 : R) ≠ -1 := fun h ↦
    two_ne_zero (α := R) (by rw [← one_add_one_eq_two, neg_eq_zero.mp h.symm, add_zero])
  have h1 : (1 : R) ≠ -1 := fun h ↦
    two_ne_zero (α := R) (by rw [← one_add_one_eq_two]; exact neg_eq_iff_add_eq_zero.mp h.symm)
  by_cases hD0 : (D : ZMod p) = 0
  · rw [(legendreSym.eq_zero_iff p D).mpr hD0]
    simp [h0]
  · rcases legendreSym.eq_one_or_neg_one p hD0 with h | h <;> simp [h, h1]

/-- Whenever `2 ≠ 0` in the coefficient ring, the scalar realization is primitive at its actual
level `|D|`. -/
theorem isPrimitive_fundamentalDiscriminantCharCast (hD : Int.IsFundamentalDiscr D) :
    (fundamentalDiscriminantCharCast R D hD).IsPrimitive := by
  have := hD.neZero_natAbs
  have : Nontrivial R := nontrivial_of_ne 2 0 two_ne_zero
  have hR : ringChar R ≠ 2 := fun h ↦
    two_ne_zero (Nat.cast_two (R := R) ▸ (ringChar.spec R 2).mpr h.dvd)
  refine Nat.dvd_antisymm (conductor_dvd_level _) ?_
  have hdvd : (fundamentalDiscriminantChar D hD).conductor ∣
      (fundamentalDiscriminantCharCast R D hD).conductor := by
    refine conductor_dvd_of_mem_conductorSet _ ?_
    have hfac := factorsThrough_conductor (fundamentalDiscriminantCharCast R D hD)
    rw [mem_conductorSet_iff, factorsThrough_iff_ker_unitsMap (conductor_dvd_level _)]
    rw [factorsThrough_iff_ker_unitsMap (conductor_dvd_level _)] at hfac
    intro u hu
    have h1 : (fundamentalDiscriminantChar D hD u : R) = ((1 : ℤ) : R) := by
      have hu' := congrArg Units.val (MonoidHom.mem_ker.mp (hfac hu))
      rw [MulChar.coe_toUnitHom, fundamentalDiscriminantCharCast_apply, Units.val_one,
        ← Int.cast_one] at hu'
      exact hu'
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
    exact Int.cast_injOn_of_ringChar_ne_two hR
      (fundamentalDiscriminantChar_isQuadratic hD u) (Or.inr (Or.inl rfl)) h1
  rwa [(isPrimitive_def _).mp (isPrimitive_fundamentalDiscriminantChar hD)] at hdvd

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
