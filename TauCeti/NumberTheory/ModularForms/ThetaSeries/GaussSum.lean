/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Reciprocity
public import TauCeti.Algebra.Module.ZLattice.SignedDiscriminant

/-!
# Closed Gauss sums and the conductor of the discriminant character

For an even full lattice `L` of rank `2k`, an odd positive `a` prime to `c`, and
`level L ∣ c`, the lattice Gauss sum is

`G_L(a, c) = c^k covolume(L) i^k (D_L / a)`.

Here `D_L = signedDiscr L` and the symbol is Jacobi's. The covolume is the positive
square root of the determinant, not the determinant itself. This formula combines
`ZLattice.IsEven.gaussSum_eq_mul_dualGaussSum` with the finite evaluation
`ZLattice.IsEven.dualGaussSum_eq_jacobiSym`.

The sum depends only on `a` modulo `c`. At `c = level L`, comparing an odd `a ≡ 1`
with `1` therefore shows `(D_L / a) = 1`. The unit-kernel criterion
`TauCeti.conductor_kroneckerChar_dvd_iff` then proves that the conductor of the
Kronecker character of `D_L` divides `level L`. No divisibility between the level
and `|D_L|` is assumed. This is the arithmetic descent needed to put the theta
transformation character at the lattice's level.

## References

* B. Schoeneberg, *Elliptic Modular Functions*, Springer (1974), Chapter IX.
* W. Ebeling, *Lattices and Codes*, 3rd ed., Springer (2013), Chapter 3.
-/

public section

open Complex Module
open scoped Pointwise Real

namespace ZLattice.IsEven

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
  (hL : IsEven L) {k : ℕ}

include hL

/-- **Closed evaluation of the lattice Gauss sum.** For an odd positive numerator `a`
prime to a positive multiple `c` of the level, the Gauss sum is
`c^k √(det L) i^k (D_L / a)`. The positive square root is written as the covolume. -/
theorem gaussSum_eq_covolume_mul_jacobiSym [MeasurableSpace E] [BorelSpace E]
    (hk : finrank ℝ E = 2 * k) {a c : ℕ} [NeZero c] (ha : Odd a)
    (hac : a.Coprime c) (hc : level L ∣ c) :
    gaussSum L hL a c =
      (c : ℂ) ^ k * covolume L * I ^ k * jacobiSym (signedDiscr L) a := by
  have : NeZero a := ⟨ha.pos.ne'⟩
  have := hL.isIntegral.finite_quotient_smul_submoduleOf_dual a
  let := Fintype.ofFinite (dual L ⧸ ((a : ℝ) • L).submoduleOf (dual L))
  have hcov : (Nat.card (DiscriminantGroup L) : ℂ) = (covolume L : ℂ) ^ 2 := by
    have h := hL.isIntegral.det_eq_card_discriminantGroup
    rw [det_def] at h
    exact_mod_cast h.symm
  rw [hL.gaussSum_eq_mul_dualGaussSum hk a c,
    hL.dualGaussSum_eq_jacobiSym hk ha (dvd_neg.mpr (Int.natCast_dvd_natCast.mpr hc))
      (Nat.isCoprime_iff_coprime.mpr hac.symm).neg_left,
    ← signedDiscr_of_finrank_eq L hk, hcov, div_pow]
  field_simp [(Nat.cast_ne_zero.mpr ha.pos.ne' : (a : ℂ) ≠ 0),
    (ofReal_ne_zero.mpr (covolume_pos L).ne' : (covolume L : ℂ) ≠ 0)]

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
  have hone := hL.gaussSum_eq_covolume_mul_jacobiSym hk odd_one
    (Nat.coprime_one_left (level L)) dvd_rfl
  simp only [Nat.cast_one, jacobiSym.one_right, Int.cast_one, mul_one] at hone
  rw [hL.gaussSum_eq_covolume_mul_jacobiSym hk ha hcop dvd_rfl, hone] at hsum
  have hne : (level L : ℂ) ^ k * covolume L * I ^ k ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne _)))
      (ofReal_ne_zero.mpr (covolume_pos L).ne')) (pow_ne_zero _ I_ne_zero)
  exact_mod_cast (mul_left_cancel₀ hne (hsum.trans (mul_one _).symm))

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
