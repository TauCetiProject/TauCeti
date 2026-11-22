/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.DirichletCharacter.Dyadic.Quadratic
import TauCeti.NumberTheory.DirichletCharacter.Conrey
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.RingTheory.ZMod.UnitsTwoPow
import TauCeti.Data.ZMod.UnitSquare
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-!
# Examples of dyadic conductors

The quadratic characters of discriminants `-4`, `8` and `-8` attain the allowed positive
dyadic exponents. The existing Conrey pairing gives a primitive character of order four
modulo sixteen, showing why quadraticity is necessary for the bound. We also exercise
descent with an odd factor, the level-zero convention and the square-kernel input.
-/

open DirichletCharacter

-- Level sixteen is the first new exclusion; odd factors need not be squarefree here.
example (χ : DirichletCharacter ℤ 16) (hquad : χ.IsQuadratic) : ¬χ.IsPrimitive := by
  intro hχ
  have := hχ.factorization_two_le_three hquad
  have : (16 : ℕ).factorization 2 = 4 := Nat.factorization_pow_self (n := 4) Nat.prime_two
  omega

example (χ : DirichletCharacter ℤ (16 * 9)) (hquad : χ.IsQuadratic) :
    χ.FactorsThrough (8 * 9) :=
  χ.factorsThrough_half_of_sq_eq_one hquad.sq_eq_one (by decide)

-- The classical characters attain dyadic exponents two and three.
example : conductor ZMod.χ₄ = 4 :=
  conductor_eq_four_of_apply_one_ne_apply_three _ (by decide)

example : conductor ZMod.χ₈ = 8 :=
  conductor_eq_eight_of_apply_one_ne_apply_five _ (by decide)

example : conductor ZMod.χ₈' = 8 :=
  conductor_eq_eight_of_apply_one_ne_apply_five _ (by decide)

example : (8 : ℕ).factorization 2 ≤ 3 := by
  have hp : IsPrimitive ZMod.χ₈ :=
    (isPrimitive_def _).mpr
      (conductor_eq_eight_of_apply_one_ne_apply_five ZMod.χ₈ (by decide))
  exact hp.factorization_two_le_three ZMod.isQuadratic_χ₈

-- The zero-level convention and the primitive level-one boundary are included.
example : (0 : ℕ).factorization 2 ≤ 3 :=
  (isPrimitive_one_level_zero (R := ℤ)).factorization_two_le_three_of_sq_eq_one (by simp)

example : (1 : ℕ).factorization 2 = 0 ∨ (1 : ℕ).factorization 2 = 2 ∨
    (1 : ℕ).factorization 2 = 3 :=
  (isPrimitive_one_level_one (R := ℤ)).factorization_two_eq_zero_or_two_or_three
    (MulChar.isQuadratic_iff_sq_eq_one.mpr (by simp))

example : IsSquare (1 : ZMod 0) :=
  ZMod.isSquare_of_cast_half_eq_one 1 (by simp) (by simp)

example : IsSquare (73 : ZMod 144) :=
  ZMod.isSquare_of_cast_half_eq_one 73 (by decide) (by decide)

-- Divisibility by eight does not suffice for the square-kernel lemma.
example : ¬IsSquare (5 : ZMod 8) := by decide

-- The local Conrey character labelled by 5 takes the value I at 5 and has order four.
example :
    let χ : DirichletCharacter ℂ 16 := MulChar.ofUnitHom
      (Circle.toUnits.comp (TauCeti.conreyLocal 2 4 (ZMod.unitFive (n := 4))))
    χ 5 = Complex.I ∧ χ.IsPrimitive ∧ orderOf χ = 4 ∧ ¬χ.IsQuadratic := by
  let f := Circle.toUnits.comp (TauCeti.conreyLocal 2 4 (ZMod.unitFive (n := 4)))
  let χ : DirichletCharacter ℂ 16 := MulChar.ofUnitHom f
  have h5 : χ 5 = Complex.I := by
    rw [← ZMod.coe_unitFive (n := 4), MulChar.ofUnitHom_coe]
    rw [MonoidHom.comp_apply, Circle.toUnits_apply, Units.val_mk0]
    rw [TauCeti.conreyLocal_two_apply (e := 2) (x := 0) (y := 0)
      (a := 1) (b := 1) (by simp) (by simp)]
    norm_num only [Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero, zero_div,
      Complex.exp_zero, mul_one, one_mul]
    have hexp : 2 * (Real.pi : ℂ) * Complex.I / 4 =
        (Real.pi : ℂ) / 2 * Complex.I := by ring
    rw [hexp]
    exact Complex.exp_pi_div_two_mul_I
  have hsq : (5 : ZMod 16) ^ 2 = 9 := by decide
  have h9 : χ 9 = -1 := by
    simpa only [hsq, h5, Complex.I_sq]
      using map_pow χ 5 2
  have hp : χ.IsPrimitive :=
    (isPrimitive_def _).mpr
      (conductor_eq_prime_pow_of_emod_eq_of_apply_ne_apply (p := 2) (k := 4)
        (a := 1) (b := 9) Nat.prime_two χ
        isCoprime_one_left ⟨-7, 4, by norm_num⟩ (by norm_num)
        (by norm_num [Int.cast_ofNat, h9]))
  have hn : χ ^ 2 ≠ 1 := by
    intro hs
    have h := congrArg (fun ψ : DirichletCharacter ℂ 16 ↦
      ψ (ZMod.unitFive (n := 4))) hs
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe,
      ZMod.coe_unitFive, h5, Complex.I_sq] at h
    norm_num at h
  have hu : ∀ u : (ZMod 16)ˣ, u ^ 4 = 1 := by decide
  have h4 : χ ^ 4 = 1 := by
    refine MulChar.ext (fun u ↦ ?_)
    rw [MulChar.pow_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val,
      hu u]
    simp
  exact ⟨h5, hp, orderOf_eq_prime_pow (p := 2) (n := 1) hn h4,
    fun hq ↦ hn hq.sq_eq_one⟩
