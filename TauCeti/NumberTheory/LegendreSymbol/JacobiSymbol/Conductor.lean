/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.Char
public import TauCeti.NumberTheory.DirichletCharacter.Conductor
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Conductors of Jacobi characters at odd level

Square factors of the denominator affect the vanishing at nonunits, but not the character
on units. The conductor at odd level is the squarefree factor left after removing a square.
This determines when Pólya–Vinogradov applies to a sum of Jacobi symbols. In particular,
the nonprincipality test used in `New.dirichletCharacter_jacobiSym_ne_one` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh)
follows here from the exact conductor.
-/

public section

namespace TauCeti

open DirichletCharacter

/-- Multiplying the denominator by a square induces the Jacobi character to the new level. -/
theorem jacobiChar_sq_mul (R : Type*) [CommRing R] (a b : ℕ) [NeZero a] [NeZero b] :
    jacobiChar R (a ^ 2 * b) = (jacobiChar R b).changeLevel (dvd_mul_left b (a ^ 2)) := by
  refine MulChar.ext fun u ↦ ?_
  have hc : ((u : ZMod (a ^ 2 * b)).val : ℤ).gcd a = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact (ZMod.val_coe_unit_coprime u).coprime_dvd_right
      ((dvd_pow_self a two_ne_zero).trans (dvd_mul_right (a ^ 2) b))
  rw [jacobiChar_apply, changeLevel_jacobiChar_apply_units, jacobiSym.mul_right,
    jacobiSym.pow_right, jacobiSym.sq_one hc, one_mul]

/-- At an odd squarefree level the Jacobi character is primitive, provided `-1 ≠ 1`
in its coefficient ring. -/
theorem isPrimitive_jacobiChar_of_odd_squarefree {R : Type*} [CommRing R]
    (hR : (-1 : R) ≠ 1) {n : ℕ} [NeZero n] (hn : Odd n) (hs : Squarefree n) :
    (jacobiChar R n).IsPrimitive := by
  rw [isPrimitive_def]
  -- The nonzero-level instance must vary with the modulus in the induction hypotheses.
  revert ‹NeZero n›
  induction n using Nat.recOnMul with
  | zero =>
    intro _
    exact (NeZero.ne 0 rfl).elim
  | one =>
    intro _
    exact Nat.dvd_one.mp (conductor_dvd_level _)
  | prime p hp =>
    intro _
    let : Fact p.Prime := ⟨hp⟩
    have hp₂ : p ≠ 2 := hn.ne_two_of_dvd_nat dvd_rfl
    obtain ⟨u, hu⟩ := quadraticChar_exists_neg_one' (F := ZMod p)
      (by rwa [ZMod.ringChar_zmod_n])
    apply (isPrimitive_def _).mp (isPrimitive_of_ne_one_of_prime hp ?_)
    rw [jacobiChar_eq_ringHomComp_quadraticChar]
    refine MulChar.ne_one_iff.mpr ⟨u, ?_⟩
    simpa [MulChar.ringHomComp_apply, hu] using hR
  | mul m n ihm ihn =>
    intro _
    obtain ⟨hcop, hsm, hsn⟩ := Nat.squarefree_mul_iff.mp hs
    let hm₀ : NeZero m := ⟨hsm.ne_zero⟩
    let hn₀ : NeZero n := ⟨hsn.ne_zero⟩
    obtain ⟨hom, hon⟩ := Nat.odd_mul.mp hn
    have hm := ihm hom hsm
    have hn' := ihn hon hsn
    rw [jacobiChar_mul, conductor_mul_of_coprime, conductor_changeLevel, conductor_changeLevel,
      hm, hn']
    rwa [conductor_changeLevel, conductor_changeLevel, hm, hn']

/-- The Jacobi character at level `a² * b`, with `b` odd and squarefree, has conductor `b`
if `-1` and `1` are distinct in the coefficient ring. -/
theorem conductor_jacobiChar_sq_mul {R : Type*} [CommRing R] (hR : (-1 : R) ≠ 1)
    (a : ℕ) [NeZero a] {b : ℕ} [NeZero b] (hb : Odd b) (hs : Squarefree b) :
    (jacobiChar R (a ^ 2 * b)).conductor = b := by
  rw [jacobiChar_sq_mul, conductor_changeLevel]
  exact (isPrimitive_def _).mp (isPrimitive_jacobiChar_of_odd_squarefree hR hb hs)

/-- At an odd level the Jacobi character is principal precisely when the level is a square. -/
theorem jacobiChar_eq_one_iff_isSquare {R : Type*} [CommRing R] (hR : (-1 : R) ≠ 1)
    {n : ℕ} [NeZero n] (hn : Odd n) : jacobiChar R n = 1 ↔ IsSquare n := by
  constructor
  · intro h
    obtain ⟨b, a, _, ha, rfl, hb⟩ := Nat.sq_mul_squarefree_of_pos hn.pos
    let : NeZero a := ⟨ha.ne'⟩
    let : NeZero b := ⟨hb.ne_zero⟩
    have hbodd := (Nat.odd_mul.mp hn).2
    rw [eq_one_iff_conductor_eq_one, conductor_jacobiChar_sq_mul hR a hbodd hb] at h
    exact ⟨a, by simp [h, pow_two]⟩
  · rintro ⟨a, rfl⟩
    let : NeZero a := ⟨fun h ↦ NeZero.ne (a * a) (by simp [h])⟩
    refine MulChar.ext fun u ↦ ?_
    have hc : ((u : ZMod (a * a)).val : ℤ).gcd a = 1 := by
      rw [Int.gcd_natCast_natCast]
      exact (ZMod.val_coe_unit_coprime u).coprime_dvd_right (dvd_mul_right a a)
    rw [jacobiChar_apply, jacobiSym.mul_right, ← sq, jacobiSym.sq_one hc,
      Int.cast_one, MulChar.one_apply_coe]

end TauCeti
