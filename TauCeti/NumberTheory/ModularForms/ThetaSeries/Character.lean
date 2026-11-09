/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ThetaSeries.GaussSum
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Character

/-!
# The character of a lattice theta series

For an even full lattice `L` of even rank, `ZLattice.IsEven.thetaCharacter` is the quadratic
Dirichlet character at `level L` induced from the primitive character of the signed discriminant
`D_L`. The conductor-divisibility theorem licenses this induction; it does not require the
level to divide `|D_L|`.

On integers prime to the level its value is the Kronecker symbol `(D_L / a)`. Its parity is
`χ_L(-1) = (-1)^k` in rank `2k`, and it is trivial when `D_L` is a square, in particular for
an even unimodular lattice. The unit-homomorphism used for modular forms with character is
`MulChar.equivToUnitHom (hL.thetaCharacter hE)`.

The evaluated Gauss-sum transformation law is expressed in terms of this character at the
lower-right matrix entry, for matrices in `Γ₀(level L)` with positive lower-left and positive odd
upper-left entries. This identifies the arithmetic scalar needed for the general theta
transformation law.

## References

* W. Ebeling, *Lattices and Codes*, third edition, Chapter 3.
* B. Schoeneberg, *Elliptic Modular Functions*, Chapter IX.
-/

public section

open Module
open scoped MatrixGroups ModularForm UpperHalfPlane

namespace ZLattice.IsEven

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]

/-- The quadratic nebentypus of the theta series of an even lattice of even rank, at the
lattice's level. It is induced from the primitive Kronecker character of `signedDiscr L`. -/
noncomputable def thetaCharacter (hL : IsEven L) (hE : Even (finrank ℝ E)) :
    DirichletCharacter ℂ (level L) :=
  DirichletCharacter.changeLevel (hL.conductor_kroneckerChar_signedDiscr_dvd_level ℂ hE)
    (TauCeti.kroneckerChar ℂ (signedDiscr L) (hL.signedDiscr_modEq_zero_or_one hE)
      hL.isIntegral.signedDiscr_ne_zero).primitiveCharacter

/-- The theta character is the induction of the primitive discriminant character to the level. -/
theorem thetaCharacter_def (hL : IsEven L) (hE : Even (finrank ℝ E)) :
    hL.thetaCharacter hE =
      DirichletCharacter.changeLevel (hL.conductor_kroneckerChar_signedDiscr_dvd_level ℂ hE)
        (TauCeti.kroneckerChar ℂ (signedDiscr L) (hL.signedDiscr_modEq_zero_or_one hE)
          hL.isIntegral.signedDiscr_ne_zero).primitiveCharacter := (rfl)

/-- On integers coprime to the level, the theta character is the Kronecker symbol of the
signed discriminant. -/
@[simp]
theorem thetaCharacter_intCast (hL : IsEven L) (hE : Even (finrank ℝ E)) {a : ℤ}
    (ha : IsCoprime a (level L)) :
    hL.thetaCharacter hE a = (TauCeti.kroneckerSym (signedDiscr L) a : ℂ) := by
  rw [thetaCharacter_def, DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ ha,
    DirichletCharacter.primitiveCharacter_apply_of_isCoprime,
    TauCeti.kroneckerChar_intCast]
  rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]
  exact coprime_natAbs_signedDiscr_of_coprime_level
    (by simpa [Int.isCoprime_iff_nat_coprime] using ha)

/-- The theta character is quadratic, including its zero values on nonunits. -/
theorem thetaCharacter_isQuadratic (hL : IsEven L) (hE : Even (finrank ℝ E)) :
    (hL.thetaCharacter hE).IsQuadratic := by
  have : NeZero (level L) := ⟨hL.isIntegral.level_pos.ne'⟩
  intro a
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective a
  by_cases hb : IsCoprime b (level L)
  · rw [hL.thetaCharacter_intCast hE hb]
    simpa only [TauCeti.kroneckerChar_intCast] using
      TauCeti.kroneckerChar_isQuadratic (R := ℂ) (hL.signedDiscr_modEq_zero_or_one hE)
        hL.isIntegral.signedDiscr_ne_zero (b : ZMod (signedDiscr L).natAbs)
  · exact Or.inl ((DirichletCharacter.apply_eq_zero_iff _ b).mpr hb)

/-- The parity of the theta character agrees with the weight `k = rank L / 2`. -/
theorem thetaCharacter_neg_one (hL : IsEven L) (hE : Even (finrank ℝ E)) {k : ℕ}
    (hk : finrank ℝ E = 2 * k) : hL.thetaCharacter hE (-1) = (-1) ^ k := by
  have h := hL.thetaCharacter_intCast hE (a := -1) isCoprime_one_left.neg_left
  have hp := hL.kroneckerChar_signedDiscr_neg_one ℂ hk
  rw [← Int.cast_one (R := ZMod (signedDiscr L).natAbs), ← Int.cast_neg,
    TauCeti.kroneckerChar_intCast] at hp
  simpa only [Int.cast_neg, Int.cast_one] using h.trans hp

/-- A square signed discriminant gives the trivial theta character. -/
@[simp]
theorem thetaCharacter_eq_one_of_isSquare (hL : IsEven L) (hE : Even (finrank ℝ E))
    (hD : IsSquare (signedDiscr L)) : hL.thetaCharacter hE = 1 := by
  rw [thetaCharacter_def, TauCeti.primitiveCharacter_kroneckerChar_of_isSquare _ _ hD,
    DirichletCharacter.changeLevel_one]

/-- In particular the theta character of an even unimodular lattice is trivial. -/
@[simp]
theorem thetaCharacter_eq_one_of_isUnimodular (hL : IsEven L) (hE : Even (finrank ℝ E))
    (hU : IsUnimodular L) : hL.thetaCharacter hE = 1 := by
  apply hL.thetaCharacter_eq_one_of_isSquare hE
  rw [hL.signedDiscr_eq_one_of_isUnimodular hU]
  exact IsSquare.one

/-- For a matrix in `Γ₀(level L)` with positive lower-left and positive odd upper-left entries,
the theta transformation scalar is the theta character evaluated at the lower-right entry.
The subgroup condition means that the level divides the lower-left entry. -/
theorem thetaSeries_slash_eq_thetaCharacter_smul_of_pos_odd
    [MeasurableSpace E] [BorelSpace E] (hL : IsEven L) (hE : Even (finrank ℝ E)) {k : ℕ}
    (hk : finrank ℝ E = 2 * k) (A : SL(2, ℤ)) {a c : ℕ} [NeZero c]
    (ha : A 0 0 = a) (hc : A 1 0 = c) (haodd : Odd a) (hN : level L ∣ c) :
    thetaSeries L ∣[(k : ℤ)] A =
      hL.thetaCharacter hE (A 1 1 : ℤ) • thetaSeries L := by
  have hA : A ∈ CongruenceSubgroup.Gamma0 (level L) :=
    CongruenceSubgroup.mem_Gamma0_iff_dvd.mpr (hc ▸ Int.natCast_dvd_natCast.mpr hN)
  have hunit := CongruenceSubgroup.isUnit_intCast_apply_zero_zero_of_mem_Gamma0 hA
  have haN : IsCoprime (a : ℤ) (level L) := by
    rw [← ha]
    exact isCoprime_comm.mp ((ZMod.isUnit_intCast_iff_isCoprime _ _).mp hunit)
  have hchar : hL.thetaCharacter hE (a : ℤ) = hL.thetaCharacter hE (A 1 1 : ℤ) := by
    rw [← ha]
    exact
      ((hL.thetaCharacter_isQuadratic hE).apply_one_one_eq_apply_zero_zero_of_mem_Gamma0 hA).symm
  rw [hL.thetaSeries_slash_eq_jacobiSym_smul hk A ha hc haodd hN,
    ← signedDiscr_of_finrank_eq L hk, ← hchar, hL.thetaCharacter_intCast hE haN,
    TauCeti.kroneckerSym_eq_jacobiSym _ haodd]

end ZLattice.IsEven
