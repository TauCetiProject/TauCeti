/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ThetaSeries.GaussSum

/-!
# The nebentypus of an even lattice

For an even full lattice `L` of even rank, the Kronecker character `(D_L / ·)` of the signed
discriminant `D_L = signedDiscr L` lives at modulus `|D_L|`. Its conductor divides the level
`N = level L` (`ZLattice.IsEven.conductor_kroneckerChar_signedDiscr_dvd_level`), so its primitive
character can be induced at level `N`. That induced character is the **nebentypus**
`χ_L : DirichletCharacter ℂ (level L)` of the theta series of `L`.

The order matters: the character is constructed at modulus `|D_L|`, where periodicity is
elementary, and the passage to modulus `N` is the lattice conductor theorem, not Mathlib's generic
`DirichletCharacter.conductor_dvd_level`. No divisibility between `N` and `|D_L|` is used.

The unit-homomorphism face of `χ_L` needed by spaces of modular forms with character is
`MulChar.equivToUnitHom (discChar L)`; it is not given a separate name.

## Main definitions and results

* `ZLattice.discChar`: the nebentypus `χ_L`, the trivial character off its hypotheses.
* `ZLattice.IsEven.discChar_intCast`: `χ_L a = (D_L / a)` for `a` coprime to the level.
* `ZLattice.discChar_isQuadratic`: `χ_L` is quadratic.
* `ZLattice.IsEven.discChar_neg_one`: `χ_L (-1) = (-1)^k` in rank `2k`.
* `ZLattice.IsEven.discChar_eq_one_of_isSquare` and
  `ZLattice.IsEven.discChar_eq_one_of_isUnimodular`: `χ_L` is trivial when `D_L` is a square, in
  particular when `L` is unimodular.

## References

* B. Schoeneberg, *Elliptic Modular Functions*, Springer, 1974, Chapter IX.
-/

public section

open Module

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

open scoped Classical in
/-- The **nebentypus** `χ_L : DirichletCharacter ℂ (level L)` of an even full lattice `L` of even
rank: the Kronecker character of the signed discriminant, constructed at modulus `|D_L|`, made
primitive, and induced at the level through the conductor theorem
`IsEven.conductor_kroneckerChar_signedDiscr_dvd_level`. It is the trivial character when `L` is
not even or its rank is odd. -/
noncomputable def discChar : DirichletCharacter ℂ (level L) :=
  if h : IsEven L ∧ Even (finrank ℝ E) then
    DirichletCharacter.changeLevel
      (h.1.conductor_kroneckerChar_signedDiscr_dvd_level ℂ h.2)
      (TauCeti.kroneckerChar ℂ (signedDiscr L) (h.1.signedDiscr_modEq_zero_or_one h.2)
        h.1.isIntegral.signedDiscr_ne_zero).primitiveCharacter
  else 1

variable {L}

namespace IsEven

variable (hL : IsEven L) (hE : Even (finrank ℝ E))
include hL hE

/-- Unfolding `discChar` under its hypotheses. -/
theorem discChar_eq_changeLevel :
    discChar L = DirichletCharacter.changeLevel
      (hL.conductor_kroneckerChar_signedDiscr_dvd_level ℂ hE)
      (TauCeti.kroneckerChar ℂ (signedDiscr L) (hL.signedDiscr_modEq_zero_or_one hE)
        hL.isIntegral.signedDiscr_ne_zero).primitiveCharacter := by
  simp only [discChar, hL, hE, and_self, dite_true]

/-- **The defining evaluation**: away from the level, `χ_L` is the Kronecker symbol of the signed
discriminant. -/
theorem discChar_intCast {a : ℤ} (ha : IsCoprime a (level L)) :
    discChar L a = (TauCeti.kroneckerSym (signedDiscr L) a : ℂ) := by
  have hD : IsCoprime a ((signedDiscr L).natAbs : ℤ) := by
    rw [Int.natCast_natAbs]
    exact (isCoprime_signedDiscr_of_isCoprime_level ha).abs_right
  rw [hL.discChar_eq_changeLevel hE, DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ ha,
    DirichletCharacter.primitiveCharacter_apply_of_isCoprime _ hD, TauCeti.kroneckerChar_intCast]

/-- `χ_L` agrees with the Kronecker symbol on natural numbers coprime to the level. -/
theorem discChar_natCast {a : ℕ} (ha : a.Coprime (level L)) :
    discChar L a = (TauCeti.kroneckerSym (signedDiscr L) a : ℂ) := by
  simpa using hL.discChar_intCast hE (Nat.isCoprime_iff_coprime.mpr ha)

omit hE in
/-- **Parity**: in rank `2k`, `χ_L (-1) = (-1)^k`, the compatibility with the weight demanded by
the parity lemma for modular forms with character. -/
theorem discChar_neg_one {k : ℕ} (hk : finrank ℝ E = 2 * k) :
    discChar L (-1) = (-1) ^ k := by
  have hE : Even (finrank ℝ E) := ⟨k, hk.trans (two_mul k)⟩
  have h := hL.kroneckerChar_signedDiscr_neg_one ℂ hk
  have h₁ : IsCoprime (-1 : ℤ) (level L) := isCoprime_one_left.neg_left
  rw [← Int.cast_one, ← Int.cast_neg, TauCeti.kroneckerChar_intCast] at h
  rw [← Int.cast_one, ← Int.cast_neg, hL.discChar_intCast hE h₁, h]

/-- `χ_L` is trivial when the signed discriminant is a square. -/
theorem discChar_eq_one_of_isSquare (hsq : IsSquare (signedDiscr L)) : discChar L = 1 := by
  rw [hL.discChar_eq_changeLevel hE, TauCeti.primitiveCharacter_kroneckerChar_of_isSquare _ _ hsq,
    DirichletCharacter.changeLevel_one]

/-- `χ_L` is trivial for an even unimodular lattice of even rank. -/
theorem discChar_eq_one_of_isUnimodular (hU : IsUnimodular L) : discChar L = 1 :=
  hL.discChar_eq_one_of_isSquare hE
    (by rw [hL.signedDiscr_eq_one_of_isUnimodular hU]; exact ⟨1, rfl⟩)

end IsEven

/-- `χ_L` is a quadratic character. This holds with no hypothesis, since the junk value is the
trivial character. -/
theorem discChar_isQuadratic : (discChar L).IsQuadratic := by
  intro x
  by_cases h : IsEven L ∧ Even (finrank ℝ E)
  · have : NeZero (level L) := ⟨h.1.isIntegral.level_pos.ne'⟩
    rw [← ZMod.intCast_zmod_cast x]
    by_cases hx : IsCoprime (x.cast : ℤ) (level L)
    · rw [h.1.discChar_intCast h.2 hx]
      rcases TauCeti.kroneckerSym_trichotomy (signedDiscr L) (x.cast : ℤ) with h | h | h <;>
        simp [h]
    · exact Or.inl ((DirichletCharacter.apply_eq_zero_iff _ _).mpr hx)
  · simp only [discChar, h, dite_false]
    by_cases hx : IsUnit x
    · simp [MulChar.one_apply hx]
    · simp [MulChar.map_nonunit _ hx]

end ZLattice
