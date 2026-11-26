/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.Char
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.ClassOfOne

/-!
# Principal Jacobi characters

A square factor in the modulus changes the Jacobi character only by induction to the new
level. Thus at odd level it is principal exactly when the modulus is a square, by the
nontriviality of the Jacobi character of an odd squarefree modulus greater than one.

The nontriviality statement used for character-sum estimates appears in
`New.dirichletCharacter_jacobiSym_ne_one` in `grh/src/Lib/Analytic/QuadraticTwist.lean` of
[grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207).
-/

public section

namespace TauCeti

/-- Multiplying the modulus by a square only changes the Jacobi character by induction to
the larger level. -/
theorem jacobiChar_sq_mul (R : Type*) [CommRing R] {a b : ℕ} [NeZero a] [NeZero b] :
    jacobiChar R (a ^ 2 * b) = (jacobiChar R b).changeLevel (dvd_mul_left b (a ^ 2)) := by
  refine MulChar.ext fun u ↦ ?_
  rw [jacobiChar_apply, changeLevel_jacobiChar_apply_units, jacobiSym.mul_right' _
    (pow_ne_zero _ (NeZero.ne a)) (NeZero.ne b), jacobiSym.pow_right]
  have hu := u.isUnit
  rw [← ZMod.natCast_zmod_val (u : ZMod (a ^ 2 * b)), ZMod.isUnit_iff_coprime] at hu
  have ha : a ∣ a ^ 2 * b := (dvd_pow_self _ two_ne_zero).trans (dvd_mul_right _ _)
  have hcop := hu.coprime_dvd_right ha
  rw [jacobiSym.sq_one (by rw [Int.gcd_natCast_natCast, Nat.coprime_iff_gcd_eq_one.mp hcop]),
    one_mul]

/-- At odd level, the Jacobi character is principal exactly when the level is a square. -/
theorem jacobiChar_eq_one_iff_of_odd {R : Type*} [CommRing R] (hR : (-1 : R) ≠ 1)
    {b : ℕ} [NeZero b] (hb : Odd b) : jacobiChar R b = 1 ↔ IsSquare b := by
  constructor
  · intro h
    obtain ⟨s, a, hs, ha, rfl, hsf⟩ := Nat.sq_mul_squarefree_of_pos (NeZero.pos b)
    let : NeZero s := ⟨hs.ne'⟩
    let : NeZero a := ⟨ha.ne'⟩
    rw [jacobiChar_sq_mul, DirichletCharacter.changeLevel_eq_one_iff] at h
    suffices s = 1 from ⟨a, by simp [this, sq]⟩
    by_contra! hs₁
    obtain ⟨v, _, hv, hval⟩ := exists_modEq_one_jacobiSym_eq_neg_one_of_squarefree
      (Nat.odd_mul.mp hb).2 (by omega : 1 < s) hsf (Nat.coprime_one_right s)
    have hv' := (ZMod.isUnit_iff_coprime v s).2 (by simpa using hv)
    apply hR
    simpa [jacobiChar_natCast, hval, MulChar.one_apply hv'] using DFunLike.congr_fun h (v : ZMod s)
  · rintro ⟨a, ha⟩
    have hne : a ≠ 0 := fun h ↦ NeZero.ne b (by simp [ha, h])
    have hb' : b = a ^ 2 * 1 := by simpa [sq] using ha
    -- Substitute the factored level so its dependent `NeZero` instance is transported as well.
    clear ha
    subst b
    let : NeZero a := ⟨hne⟩
    have h₁ : jacobiChar R 1 = 1 := Subsingleton.elim _ _
    rw [jacobiChar_sq_mul, h₁, DirichletCharacter.changeLevel_one]

end TauCeti
