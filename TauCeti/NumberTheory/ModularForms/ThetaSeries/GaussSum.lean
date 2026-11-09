/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Reciprocity
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.CosetSplitting
public import TauCeti.Algebra.Module.ZLattice.SignedDiscriminant

/-!
# The closed formula for lattice Gauss sums

For an even full lattice `L` of rank `2k`, an odd positive integer `a`, and a positive multiple
`c` of the level prime to `a`, the Gauss sum is

`G_L(a, c) = c^k √|L^∨/L| i^k ((-1)^k |L^∨/L| / a)`.

The symbol on the right is the Jacobi symbol. The factor `√|L^∨/L|` is the covolume, not the
determinant. Combining lattice reciprocity with the evaluation of the dual sum at the odd
modulus `a` gives this formula without evaluating any Gauss sum at an even modulus directly.

The normalized scalar `(-i)^k c^(-k) (covol L)^(-1) G_L(a, c)` is consequently just the Jacobi
symbol. This evaluates the scalar in the theta transformation law for matrices whose first
column is positive and whose upper-left entry is odd. No character at the level, or reduction
of arbitrary matrices to this case, is asserted here.

The sum depends only on `a` modulo `c`. At `c = level L`, comparing an odd `a ≡ 1` with `1`
therefore shows `(D_L / a) = 1` for the signed discriminant `D_L = signedDiscr L =
(-1)^k |L^∨/L|`. The unit-kernel criterion `TauCeti.conductor_kroneckerChar_dvd_iff` then proves
that the conductor of the Kronecker character of `D_L` divides `level L`
(`ZLattice.IsEven.conductor_kroneckerChar_signedDiscr_dvd_level`). No divisibility between the
level and `|D_L|` is assumed. This is the arithmetic descent needed to put the theta
transformation character at the lattice's level.

## References

* B. Schoeneberg, *Elliptic Modular Functions*, Springer, 1974, Chapter IX.
* W. Ebeling, *Lattices and Codes*, 3rd ed., Springer (2013), Chapter 3.
-/

public section

open Complex Module
open scoped Pointwise Real ModularForm UpperHalfPlane MatrixGroups

namespace ZLattice.IsEven

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] {k : ℕ} (hL : IsEven L)

include hL

/-- The closed formula for `G_L(a, c)` when `a` is odd, `c` is a positive multiple of the level,
and `a` and `c` are coprime. The discriminant is written as `|L^∨/L|`. -/
theorem gaussSum_eq_sqrt_card_mul_jacobiSym (hk : finrank ℝ E = 2 * k) {a c : ℕ}
    [NeZero c] (ha : Odd a) (hN : level L ∣ c) (hac : a.Coprime c) :
    gaussSum L hL a c = (c : ℂ) ^ k * (√(Nat.card (DiscriminantGroup L) : ℝ) : ℂ) *
      I ^ k * jacobiSym ((-1) ^ k * Nat.card (DiscriminantGroup L)) a := by
  classical
  borelize E
  have : NeZero a := ⟨ha.pos.ne'⟩
  have := hL.isIntegral.finite_quotient_smul_submoduleOf_dual a
  let := Fintype.ofFinite (dual L ⧸ ((a : ℝ) • L).submoduleOf (dual L))
  have hD : (Nat.card (DiscriminantGroup L) : ℂ) = (covolume L : ℂ) ^ 2 := by
    exact_mod_cast (hL.isIntegral.det_eq_card_discriminantGroup.symm.trans (det_def L))
  rw [hL.gaussSum_eq_mul_dualGaussSum hk a c,
    hL.dualGaussSum_eq_jacobiSym hk ha (dvd_neg.mpr (Int.natCast_dvd_natCast.mpr hN))
      hac.symm.isCoprime.neg_left, hD, ← hL.isIntegral.covolume_eq_sqrt_card_discriminantGroup]
  have ha0 : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne a)
  have hcov0 : (covolume L : ℂ) ≠ 0 := ofReal_ne_zero.mpr (covolume_pos L).ne'
  rw [div_pow]
  field_simp

variable [MeasurableSpace E] [BorelSpace E]

/-- The normalized Gauss scalar in the theta transformation law is the Jacobi symbol of the
signed discriminant, for odd positive `a` prime to the positive level-multiple `c`. -/
theorem normalized_gaussSum_eq_jacobiSym (hk : finrank ℝ E = 2 * k) {a c : ℕ}
    [NeZero c] (ha : Odd a) (hN : level L ∣ c) (hac : a.Coprime c) :
    (-I) ^ k * ((c : ℂ) ^ k)⁻¹ * (covolume L : ℂ)⁻¹ * gaussSum L hL a c =
      jacobiSym ((-1) ^ k * Nat.card (DiscriminantGroup L)) a := by
  have hI : (-I) ^ k * I ^ k = 1 := by rw [← mul_pow]; simp
  rw [hL.gaussSum_eq_sqrt_card_mul_jacobiSym hk ha hN hac,
    ← hL.isIntegral.covolume_eq_sqrt_card_discriminantGroup]
  have hc0 : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne c)
  have hcov0 : (covolume L : ℂ) ≠ 0 := ofReal_ne_zero.mpr (covolume_pos L).ne'
  field_simp
  linear_combination (jacobiSym ((-1) ^ k * Nat.card (DiscriminantGroup L)) a : ℂ) * hI

/-- The evaluated theta transformation law when the first column is positive and the upper-left
entry is odd. The Jacobi symbol here has denominator `a`, not the matrix's lower-right entry;
passing to a character at the level is a separate arithmetic assertion. -/
theorem thetaSeries_slash_eq_jacobiSym_smul (hk : finrank ℝ E = 2 * k) (A : SL(2, ℤ))
    {a c : ℕ} [NeZero c] (ha : A 0 0 = a) (hc : A 1 0 = c) (haodd : Odd a)
    (hN : level L ∣ c) :
    thetaSeries L ∣[(k : ℤ)] A =
      (jacobiSym ((-1) ^ k * Nat.card (DiscriminantGroup L)) a : ℂ) • thetaSeries L := by
  have hac : IsCoprime (a : ℤ) c := by
    simpa only [ha, hc] using A.isCoprime_col 0
  rw [hL.thetaSeries_slash_eq_gaussSum_smul hk A hc hN, ha,
    hL.normalized_gaussSum_eq_jacobiSym hk haodd hN hac.natCoprime]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The Jacobi symbol of the signed discriminant is `1` on odd natural numbers
congruent to `1` modulo the level. No separate coprimality assumption is needed. -/
theorem jacobiSym_signedDiscr_eq_one (hk : finrank ℝ E = 2 * k) {a : ℕ}
    (ha : Odd a) (hmod : a ≡ 1 [MOD level L]) :
    jacobiSym (signedDiscr L) a = 1 := by
  classical
  borelize E
  have : NeZero (level L) := ⟨hL.isIntegral.level_pos.ne'⟩
  have hcop : a.Coprime (level L) := by
    rw [Nat.coprime_iff_gcd_eq_one, hmod.gcd_eq, Nat.gcd_one_left]
  have hsum : gaussSum L hL a (level L) = gaussSum L hL 1 (level L) :=
    gaussSum_eq_of_modEq hL (by exact_mod_cast hmod)
  have hone := hL.gaussSum_eq_sqrt_card_mul_jacobiSym hk odd_one dvd_rfl
    (Nat.coprime_one_left (level L))
  simp only [Nat.cast_one, jacobiSym.one_right, Int.cast_one, mul_one] at hone
  rw [hL.gaussSum_eq_sqrt_card_mul_jacobiSym hk ha dvd_rfl hcop, hone] at hsum
  have hcard : (0 : ℝ) < Nat.card (DiscriminantGroup L) := by
    have := hL.isIntegral.finite_discriminantGroup
    exact_mod_cast Nat.card_pos
  have hne : (level L : ℂ) ^ k * (√(Nat.card (DiscriminantGroup L) : ℝ) : ℂ) * I ^ k ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne _)))
      (ofReal_ne_zero.mpr (Real.sqrt_pos.2 hcard).ne')) (pow_ne_zero _ I_ne_zero)
  rw [signedDiscr_of_finrank_eq L hk]
  exact_mod_cast (mul_left_cancel₀ hne (hsum.trans (mul_one _).symm))

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The discriminant-character conductor divides the lattice level.** The character
is initially defined modulo `|D_L|`; its primitive character can consequently be
induced to `level L`. The coefficient ring need only distinguish `1` and `-1`. -/
theorem conductor_kroneckerChar_signedDiscr_dvd_level (R : Type*) [CommRing R]
    [NeZero (2 : R)] (hE : Even (finrank ℝ E)) :
    (TauCeti.kroneckerChar R (signedDiscr L) (hL.signedDiscr_modEq_zero_or_one hE)
      hL.isIntegral.signedDiscr_ne_zero).conductor ∣ level L := by
  obtain ⟨k, hk⟩ := hE
  have hk' : finrank ℝ E = 2 * k := hk.trans (two_mul k).symm
  apply (TauCeti.conductor_kroneckerChar_dvd_iff _ _).mpr
  intro a ha _ hmod
  rw [TauCeti.kroneckerSym_eq_jacobiSym _ ha]
  exact hL.jacobiSym_signedDiscr_eq_one hk' ha hmod

end ZLattice.IsEven
