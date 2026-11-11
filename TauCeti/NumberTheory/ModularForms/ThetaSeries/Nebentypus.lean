/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ThetaSeries.GaussSum
public import TauCeti.Algebra.Module.ZLattice.RootLattice

/-!
# The nebentypus of an even lattice

Let `L` be an even full lattice of even rank `2k` and level `N` in a real inner product space, with
signed discriminant `D_L = (-1)^k det L` (`ZLattice.signedDiscr L`). The Kronecker character
`(D_L / ·)` is a Dirichlet character of modulus `|D_L|`, and its conductor divides `N`
(`ZLattice.IsEven.conductor_kroneckerChar_signedDiscr_dvd_level`), even though `N` need not divide
`|D_L|`. Inducing its primitive character up to modulus `N` gives the **nebentypus**

`χ_L : DirichletCharacter R N`,

the character that appears in the Hecke–Schoeneberg transformation law `Θ_L ∣[k] A = χ_L(d) Θ_L`
of the theta series of `L` under `Γ₀(N)`; that law is not proved in this file. The nebentypus is
characterized by its values on integers coprime to `N`, where it is the Kronecker symbol:
`χ_L a = (D_L / a)`, which is the Jacobi symbol when `a` is odd
(`ZLattice.IsEven.nebentypus_intCast`, `ZLattice.IsEven.nebentypus_natCast_eq_jacobiSym`). It is
quadratic, it takes the value `(-1)^k` at `-1`, it has the same conductor as `(D_L / ·)`, and it is
trivial when `D_L` is a square, in particular when `L` is unimodular.

The coefficient ring `R` only needs `2 ≠ 0`, the hypothesis under which the conductor of `(D_L / ·)`
is known to divide `N`. The unit-homomorphism form of `χ_L`, used for spaces of modular forms with
character, is `MulChar.equivToUnitHom (hL.nebentypus R hE)`.

For the root lattices: the nebentypus of `A₂` (level `3`, `D = -3`) is the primitive character
`(-3 / ·)` modulo `3`, and the nebentypus of `D₄` (level `2`, `D = 4`) is trivial.

## Main definitions

* `ZLattice.IsEven.nebentypus R hL hE`: the nebentypus `χ_L : DirichletCharacter R (level L)` of an
  even full lattice `L` of even rank.

## Main statements

* `ZLattice.IsEven.nebentypus_intCast`: `χ_L a = (D_L / a)` for every integer `a` coprime to the
  level.
* `ZLattice.IsEven.nebentypus_isQuadratic`, `ZLattice.IsEven.nebentypus_neg_one`: `χ_L` is quadratic
  and `χ_L (-1) = (-1)^k`.
* `ZLattice.IsEven.conductor_nebentypus`: `χ_L` and `(D_L / ·)` have the same conductor.
* `ZLattice.IsEven.nebentypus_eq_one_of_isSquare`,
  `ZLattice.IsEven.nebentypus_eq_one_of_isUnimodular`: `χ_L` is trivial when `D_L` is a square,
  and in particular when `L` is unimodular.
* `TauCeti.IntegralLattice.nebentypus_realModel_typeARootLattice_two_intCast`,
  `TauCeti.IntegralLattice.isPrimitive_nebentypus_realModel_typeARootLattice_two`,
  `TauCeti.IntegralLattice.nebentypus_realModel_checkerboardLattice_four`: the nebentypus of `A₂` is
  the primitive character `(-3 / ·)` modulo `3`, and that of `D₄` is trivial.

## References

* E. Hecke, *Analytische Arithmetik der positiven quadratischen Formen*, Kgl. Danske Vid. Selsk.
  Math.-fys. Medd. XVII, 12 (1940).
* B. Schoeneberg, *Elliptic Modular Functions*, Springer, 1974, Chapter IX.
* W. Ebeling, *Lattices and Codes*, 3rd ed., Springer, 2013, Chapter 3.
-/

public section

open Module

namespace ZLattice.IsEven

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
  (R : Type*) [CommRing R] [NeZero (2 : R)] (hL : IsEven L) (hE : Even (finrank ℝ E))

/-- The **nebentypus** `χ_L` of an even full lattice `L` of even rank: the primitive character of
the Kronecker character `(D_L / ·)` of the signed discriminant `D_L = signedDiscr L`, induced up to
modulus `level L`. This is legitimate because the conductor of `(D_L / ·)` divides the level
(`ZLattice.IsEven.conductor_kroneckerChar_signedDiscr_dvd_level`). On integers `a` coprime to the
level, `χ_L a = (D_L / a)` (`ZLattice.IsEven.nebentypus_intCast`). -/
noncomputable def nebentypus : DirichletCharacter R (level L) :=
  DirichletCharacter.changeLevel (hL.conductor_kroneckerChar_signedDiscr_dvd_level R hE)
    (TauCeti.kroneckerChar R (signedDiscr L) (hL.signedDiscr_modEq_zero_or_one hE)
      hL.isIntegral.signedDiscr_ne_zero).primitiveCharacter

variable {R}

/-- **The values of the nebentypus.** On an integer `a` coprime to the level, `χ_L a` is the
Kronecker symbol `(D_L / a)` of the signed discriminant. -/
theorem nebentypus_intCast {a : ℤ} (ha : IsCoprime a (level L)) :
    hL.nebentypus R hE a = TauCeti.kroneckerSym (signedDiscr L) a := by
  rw [nebentypus, DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ ha,
    DirichletCharacter.primitiveCharacter_apply_of_isCoprime _ ?_, TauCeti.kroneckerChar_intCast]
  rw [Int.natCast_natAbs, IsCoprime.abs_right_iff]
  exact isCoprime_signedDiscr_of_isCoprime_level ha

/-- On a natural number `a` coprime to the level, `χ_L a` is the Kronecker symbol `(D_L / a)`. -/
theorem nebentypus_natCast {a : ℕ} (ha : a.Coprime (level L)) :
    hL.nebentypus R hE a = TauCeti.kroneckerSym (signedDiscr L) a := by
  rw [← Int.cast_natCast, hL.nebentypus_intCast hE (Nat.isCoprime_iff_coprime.mpr ha)]

/-- On an odd natural number `a` coprime to the level, `χ_L a` is the Jacobi symbol
`J(D_L | a)`. -/
theorem nebentypus_natCast_eq_jacobiSym {a : ℕ} (hodd : Odd a) (ha : a.Coprime (level L)) :
    hL.nebentypus R hE a = jacobiSym (signedDiscr L) a := by
  rw [hL.nebentypus_natCast hE ha, TauCeti.kroneckerSym_eq_jacobiSym _ hodd]

/-- The nebentypus is quadratic: it takes only the values `0`, `1` and `-1`. -/
theorem nebentypus_isQuadratic : (hL.nebentypus R hE).IsQuadratic := by
  intro x
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  by_cases ha : IsCoprime a (level L)
  · rw [hL.nebentypus_intCast hE ha]
    rcases TauCeti.kroneckerSym_trichotomy (signedDiscr L) a with h | h | h <;> simp [h]
  · exact Or.inl (MulChar.map_nonunit _
      (by rwa [ZMod.isUnit_intCast_iff_isCoprime, isCoprime_comm]))

/-- **Parity of the nebentypus.** For an even full lattice of rank `2k`, `χ_L (-1) = (-1)^k`. -/
theorem nebentypus_neg_one {k : ℕ} (hk : finrank ℝ E = 2 * k) :
    hL.nebentypus R hE (-1) = (-1) ^ k := by
  have h := hL.nebentypus_intCast (R := R) hE (a := -1) isCoprime_one_left.neg_left
  rw [Int.cast_neg, Int.cast_one] at h
  rw [h, ← TauCeti.kroneckerChar_intCast (hL.signedDiscr_modEq_zero_or_one hE)
    hL.isIntegral.signedDiscr_ne_zero, Int.cast_neg, Int.cast_one,
    hL.kroneckerChar_signedDiscr_neg_one R hk]

/-- The nebentypus has the same conductor as the Kronecker character `(D_L / ·)`. -/
theorem conductor_nebentypus :
    (hL.nebentypus R hE).conductor =
      (TauCeti.kroneckerChar R (signedDiscr L) (hL.signedDiscr_modEq_zero_or_one hE)
        hL.isIntegral.signedDiscr_ne_zero).conductor := by
  have : NeZero (level L) := ⟨hL.isIntegral.level_pos.ne'⟩
  rw [nebentypus, DirichletCharacter.conductor_changeLevel]
  exact (DirichletCharacter.isPrimitive_def _).mp
    (DirichletCharacter.primitiveCharacter_isPrimitive _)

/-- If the signed discriminant `D_L` is a square, the nebentypus is the trivial character modulo
the level. -/
theorem nebentypus_eq_one_of_isSquare (hsq : IsSquare (signedDiscr L)) :
    hL.nebentypus R hE = 1 := by
  rw [nebentypus, TauCeti.primitiveCharacter_kroneckerChar_of_isSquare _ _ hsq,
    DirichletCharacter.changeLevel_one]

/-- The nebentypus of an even unimodular full lattice is trivial, since its signed discriminant is
`1`. -/
theorem nebentypus_eq_one_of_isUnimodular (hU : IsUnimodular L) : hL.nebentypus R hE = 1 :=
  hL.nebentypus_eq_one_of_isSquare hE ⟨1, by rw [hL.signedDiscr_eq_one_of_isUnimodular hU]; rfl⟩

end ZLattice.IsEven

/-! ### The root lattices `A₂` and `D₄` -/

namespace TauCeti.IntegralLattice

variable (R : Type*) [CommRing R] [NeZero (2 : R)]

/-- The nebentypus of the real model of `A₂` is the Kronecker character `(-3 / ·)` modulo `3`: its
value at every integer `a` is `(-3 / a)`. -/
theorem nebentypus_realModel_typeARootLattice_two_intCast (a : ℤ) :
    ((isEven_realModel_iff _ (isPosDef_typeARootLattice 2)).mpr
      (isEven_typeARootLattice 2)).nebentypus R (by simp [finrank_carrier]) a =
      kroneckerSym (-3) a := by
  by_cases ha : IsCoprime a (ZLattice.level
    ((typeARootLattice 2).realModel (isPosDef_typeARootLattice 2)))
  · rw [ZLattice.IsEven.nebentypus_intCast _ _ ha, signedDiscr_realModel_typeARootLattice_two]
  · rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_intCast_iff_isCoprime, isCoprime_comm]),
      kroneckerSym_eq_zero_iff.mpr, Int.cast_zero]
    rw [level_realModel_typeARootLattice_two, Nat.cast_ofNat] at ha
    rwa [Ne, ← Int.isCoprime_iff_gcd_eq_one, IsCoprime.neg_left_iff, isCoprime_comm]

/-- The nebentypus of the real model of `A₂` is primitive: its conductor `3` is the level. -/
theorem isPrimitive_nebentypus_realModel_typeARootLattice_two :
    (((isEven_realModel_iff _ (isPosDef_typeARootLattice 2)).mpr
      (isEven_typeARootLattice 2)).nebentypus R (by simp [finrank_carrier])).IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def, ZLattice.IsEven.conductor_nebentypus,
    conductor_kroneckerChar_signedDiscr_realModel_typeARootLattice_two,
    level_realModel_typeARootLattice_two]

/-- The nebentypus of the real model of `D₄` is trivial, since its signed discriminant `4` is a
square. -/
theorem nebentypus_realModel_checkerboardLattice_four :
    ((isEven_realModel_iff _ (isPosDef_checkerboardLattice 4)).mpr
      (isEven_checkerboardLattice 4)).nebentypus R ⟨2, by simp [finrank_carrier]⟩ = 1 :=
  ZLattice.IsEven.nebentypus_eq_one_of_isSquare _ _
    ⟨2, by rw [signedDiscr_realModel_checkerboardLattice_four]; norm_num⟩

end TauCeti.IntegralLattice
