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
    conductor_eq_eight_of_apply_one_ne_apply_five ZMod.χ₈ (by decide)
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

-- The Conrey pairing at the unit 5 detects the cyclic factor of order four.
example : ∃ χ : DirichletCharacter ℂ 16, χ.IsPrimitive ∧ orderOf χ = 4 := by
  -- The concrete levels coincide: 2 ^ 4 = 2 ^ (2 + 2) = 16, by numeral reduction.
  let f := Circle.toUnits.comp (TauCeti.conreyLocal 2 4 (TauCeti.ZMod.unitsTwoPowFive 2))
  let χ : DirichletCharacter ℂ 16 := MulChar.ofUnitHom f
  have h9 : χ (9 : ZMod 16) = -1 := by
    have h := TauCeti.conreyLocal_two_apply (e := 2)
      (m := TauCeti.ZMod.unitsTwoPowFive 2)
      (n := ZMod.unitOfCoprime 9 (by decide)) (x := 0) (y := 0) (a := 1) (b := 2)
      (by simp) (by decide)
    have hc : χ (9 : ZMod 16) =
        (TauCeti.conreyLocal 2 4 (TauCeti.ZMod.unitsTwoPowFive 2)
          (ZMod.unitOfCoprime 9 (by decide)) : ℂ) := by
      have hv : (9 : ZMod 16) =
          (ZMod.unitOfCoprime 9 (by decide) : (ZMod 16)ˣ) := by decide
      calc
        χ (9 : ZMod 16) = χ (ZMod.unitOfCoprime 9 (by decide) : (ZMod 16)ˣ) :=
          congrArg χ hv
        _ = _ := MulChar.ofUnitHom_coe f (ZMod.unitOfCoprime 9 (by decide))
    -- The nontrivial factor is exp(πi) = -1.
    have hexp : 2 * Real.pi * Complex.I * 2 / 2 ^ 2 = Real.pi * Complex.I := by ring
    rw [hc, h]
    simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, mul_zero, zero_div,
      Complex.exp_zero, one_mul, hexp, Complex.exp_pi_mul_I]
  have hp : χ.IsPrimitive :=
    conductor_eq_prime_pow_of_emod_eq_of_apply_ne_apply (p := 2) (k := 4)
      (a := 1) (b := 9) Nat.prime_two χ
      isCoprime_one_left ⟨-7, 4, by norm_num⟩ (by norm_num)
      (by norm_num [Int.cast_ofNat, h9])
  have hnot : χ ^ 2 ≠ 1 := by
    intro hs
    have hh := congrArg (fun ψ : DirichletCharacter ℂ 16 ↦ ψ (5 : ZMod 16)) hs
    have hsq : (5 : ZMod 16) ^ 2 = 9 := by decide
    rw [MulChar.pow_apply' χ two_ne_zero, ← map_pow, hsq, h9,
      MulChar.one_apply (by decide : IsUnit (5 : ZMod 16))] at hh
    norm_num at hh
  have hfour : χ ^ 4 = 1 := by
    apply MulChar.ext
    intro u
    have hu : u ^ 4 = 1 := (by decide : ∀ u : (ZMod 16)ˣ, u ^ 4 = 1) u
    rw [MulChar.pow_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val, hu]
    simp
  exact ⟨χ, hp, orderOf_eq_prime_pow (p := 2) (n := 1) hnot hfour⟩
