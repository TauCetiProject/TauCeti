/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.DirichletCharacter.Quadratic.FundamentalDiscriminant
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Conductor
import TauCeti.NumberTheory.DirichletCharacter.Quadratic
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Values
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime

/-!
# Examples of primitive discriminants of quadratic Dirichlet characters

Concrete instances exercising the primitive-discriminant correspondence at primitive and
imprimitive levels, naturality under `changeLevel`, sign separation at conductor `8`, the
squarefree-radicand bijection, and the odd-prime Legendre dictionary (together with its boundary at
`p = 2` and at primes dividing the level).
-/

open DirichletCharacter TauCeti.Multiquadratic

-- Small fundamental discriminants, their squarefree radicands, and exclusion of `-12`.
example : Int.IsFundamentalDiscr 1 ∧ Int.IsFundamentalDiscr (-4) ∧
    Int.IsFundamentalDiscr 8 ∧ Int.IsFundamentalDiscr (-8) ∧
    Int.IsFundamentalDiscr 5 ∧ Int.IsFundamentalDiscr (-3) ∧
    Int.IsFundamentalDiscr 12 ∧ ¬ Int.IsFundamentalDiscr (-12) := by
  have h1 : Int.IsFundamentalDiscr 1 := by
    simpa using isFundamentalDiscr_fundamentalDiscriminant squarefree_one
  have h5 : Int.IsFundamentalDiscr 5 := by
    have hsf : Squarefree (5 : ℤ) :=
      (Nat.prime_iff_prime_int.mp (by norm_num : Nat.Prime 5)).squarefree
    simpa [fundamentalDiscriminant_def] using isFundamentalDiscr_fundamentalDiscriminant hsf
  have hm3 : Int.IsFundamentalDiscr (-3) := by
    have hsf : Squarefree (-3 : ℤ) :=
      (Nat.prime_iff_prime_int.mp Nat.prime_three).squarefree.neg
    simpa [fundamentalDiscriminant_def] using isFundamentalDiscr_fundamentalDiscriminant hsf
  have h12 : Int.IsFundamentalDiscr 12 := by
    have hsf : Squarefree (3 : ℤ) := (Nat.prime_iff_prime_int.mp Nat.prime_three).squarefree
    simpa [fundamentalDiscriminant_def] using isFundamentalDiscr_fundamentalDiscriminant hsf
  have hm12 : ¬ Int.IsFundamentalDiscr (-12) := fun h ↦
    absurd (h.2.1 (-3) (by norm_num)).2 (by norm_num)
  exact ⟨h1, isPrimeDiscriminant_neg_four.isFundamentalDiscr,
    isPrimeDiscriminant_eight.isFundamentalDiscr,
    isPrimeDiscriminant_neg_eight.isFundamentalDiscr, h5, hm3, h12, hm12⟩

example :
    fundamentalDiscriminantRadicand 1 = 1 ∧
      fundamentalDiscriminantRadicand (-4) = -1 ∧
      fundamentalDiscriminantRadicand 8 = 2 ∧
      fundamentalDiscriminantRadicand (-8) = -2 ∧
      fundamentalDiscriminantRadicand 5 = 5 ∧
      fundamentalDiscriminantRadicand (-3) = -3 ∧
      fundamentalDiscriminantRadicand 12 = 3 := by
  norm_num [fundamentalDiscriminantRadicand_def]

-- Sign separation at conductor `8`: `χ₈` has discriminant `8` and `χ₈'` has discriminant `-8`.
example :
    (if ZMod.χ₈ (-1) = 1 then ((conductor ZMod.χ₈ : ℕ) : ℤ) else -(conductor ZMod.χ₈ : ℤ)) = 8 ∧
    (if ZMod.χ₈' (-1) = 1 then ((conductor ZMod.χ₈' : ℕ) : ℤ) else -(conductor ZMod.χ₈' : ℤ)) =
      -8 := by
  have hc8 : conductor ZMod.χ₈ = 8 :=
    conductor_eq_eight_of_apply_one_ne_apply_five _ (by decide)
  have hc8' : conductor ZMod.χ₈' = 8 :=
    conductor_eq_eight_of_apply_one_ne_apply_five _ (by decide)
  have hs8 : ZMod.χ₈ (-1) = 1 := by decide
  have hs8' : ZMod.χ₈' (-1) = -1 := by decide
  simp [hc8, hc8', hs8, hs8']

-- Principal character at level `6`: unique discriminant `D = 1`, vanishing at `2` and `3`.
example :
    let χ : DirichletCharacter ℂ 6 := 1
    (∃ hD : Int.IsFundamentalDiscr 1,
      (1 : ℤ).natAbs = χ.conductor ∧
        ∀ n : ℤ, IsCoprime n 6 → χ n = fundamentalDiscriminantCharCast ℂ 1 hD n) ∧
    χ 2 = 0 ∧ χ 3 = 0 ∧ χ 5 = 1 := by
  intro χ
  have hq : χ.IsQuadratic := MulChar.isQuadratic_one
  have hc : χ.conductor = 1 := conductor_one
  have h1 : χ (-1) = 1 := MulChar.one_apply isUnit_one.neg
  have hite : (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) = 1 := by simp [h1, hc]
  have hD1 : Int.IsFundamentalDiscr 1 := by
    simpa [hite] using isFundamentalDiscr_ite_conductor hq
  refine ⟨⟨hD1, by simp [hc], fun n hn ↦ ?_⟩, ?_, ?_, ?_⟩
  · rw [apply_eq_fundamentalDiscriminantCharCast_ite_conductor hq hn]
    simp only [fundamentalDiscriminantCharCast_apply, fundamentalDiscriminantChar_intCast, hite]
  · exact MulChar.map_nonunit χ (by decide)
  · exact MulChar.map_nonunit χ (by decide)
  · exact MulChar.one_apply (by decide)

-- `χ₄` lifted to level `12` has conductor `4` and discriminant `-4`, but vanishes at `3` while
-- the primitive character of `-4` takes `-1` there: coprimality to the level is required.
example :
    let χ : DirichletCharacter ℂ 12 :=
      changeLevel (by decide : 4 ∣ 12) (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))
    χ.conductor = 4 ∧
      (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) = -4 ∧
      χ 3 = 0 ∧
      fundamentalDiscriminantCharCast ℂ (-4) isPrimeDiscriminant_neg_four.isFundamentalDiscr 3 =
        -1 := by
  intro χ
  have hc4 : conductor ZMod.χ₄ = 4 :=
    conductor_eq_four_of_apply_one_ne_apply_three _ (by decide)
  have hc : χ.conductor = 4 := by
    rw [conductor_changeLevel, conductor_ringHomComp _ _ Int.cast_injective, hc4]
  have hneg1 : χ (-1) = -1 := by
    rw [changeLevel_apply_neg_one, MulChar.ringHomComp_apply]
    have h4 : ZMod.χ₄ (-1) = -1 := by decide
    simp [h4]
  have h3 : χ 3 = 0 := MulChar.map_nonunit χ (by decide)
  have hf3 :
      fundamentalDiscriminantCharCast ℂ (-4) isPrimeDiscriminant_neg_four.isFundamentalDiscr
        (3 : ℤ) = -1 := by
    rw [fundamentalDiscriminantCharCast_apply, fundamentalDiscriminantChar_neg_four]
    have hv : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
    simp [hv]
  refine ⟨hc, ?_, h3, hf3⟩
  rw [hc, hneg1]
  norm_num

-- Conductor-`12` product `χ₄ · (Legendre mod 3)`: conductor `12`, discriminant `D = 12`, and
-- naturality when lifted to level `24`.
example :
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    let χ : DirichletCharacter ℤ 12 :=
      changeLevel (by decide : 4 ∣ 12) ZMod.χ₄ *
        changeLevel (by decide : 3 ∣ 12) (quadraticChar (ZMod 3))
    χ.conductor = 12 ∧
      (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) = 12 ∧
      (changeLevel (by decide : 12 ∣ 24) χ).conductor = 12 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro χ
  let χ4 : DirichletCharacter ℤ 12 := changeLevel (by decide : 4 ∣ 12) ZMod.χ₄
  let χ3 : DirichletCharacter ℤ 12 := changeLevel (by decide : 3 ∣ 12) (quadraticChar (ZMod 3))
  have hχ : χ = χ4 * χ3 := rfl
  have hc4 : χ4.conductor = 4 := by
    rw [conductor_changeLevel]
    exact conductor_eq_four_of_apply_one_ne_apply_three _ (by decide)
  have hc3 : χ3.conductor = 3 := by
    convert conductor_changeLevel_quadraticChar (R := ℤ) (p := 3) (by simp) (by decide)
      (by decide : 3 ∣ 12) using 3
    ext
    simp
  have hc : χ.conductor = 12 := by
    rw [hχ, conductor_mul_of_coprime (by rw [hc4, hc3]; decide), hc4, hc3]
  have hneg1 : χ (-1) = 1 := by
    rw [hχ, MulChar.mul_apply, changeLevel_apply_neg_one, changeLevel_apply_neg_one]
    have h4 : ZMod.χ₄ (-1) = -1 := by decide
    have h3 : quadraticChar (ZMod 3) (-1 : ZMod 3) = -1 := by
      change quadraticChar (ZMod 3) ((-1 : ℤ) : ZMod 3) = -1
      rw [← legendreSym]
      norm_num
    rw [h4, h3]
    norm_num
  refine ⟨hc, by simp [hc, hneg1], ?_⟩
  rw [conductor_changeLevel, hc]

-- Odd-prime Legendre dictionary and nonsquare certificates at `D = 12` (radicand `d = 3`).
example :
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    ∃ h12 : Int.IsFundamentalDiscr 12,
      fundamentalDiscriminantChar 12 h12 5 = -1 ∧
        fundamentalDiscriminantChar 12 h12 7 = -1 ∧
        fundamentalDiscriminantChar 12 h12 11 = 1 ∧
        ¬ IsSquare (12 : ZMod 5) ∧ ¬ IsSquare (3 : ZMod 5) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h12 : Int.IsFundamentalDiscr 12 := by
    have hsf : Squarefree (3 : ℤ) := (Nat.prime_iff_prime_int.mp Nat.prime_three).squarefree
    simpa [fundamentalDiscriminant_def] using isFundamentalDiscr_fundamentalDiscriminant hsf
  let χ := fundamentalDiscriminantCharCast ℤ 12 h12
  have hval : ∀ n : ℤ, IsCoprime n 12 → χ n = fundamentalDiscriminantCharCast ℤ 12 h12 n :=
    fun _ _ ↦ rfl
  have h5 := fundamentalDiscriminantChar_natCast_eq_jacobiSym h12 (by decide : Odd 5)
  have h7 := fundamentalDiscriminantChar_natCast_eq_jacobiSym h12 (by decide : Odd 7)
  have h11 := fundamentalDiscriminantChar_natCast_eq_jacobiSym h12 (by decide : Odd 11)
  norm_num at h5 h7 h11
  have hχ5 : χ 5 = -1 := by
    rw [fundamentalDiscriminantCharCast_apply]
    exact_mod_cast h5
  have hnsq12 : ¬ IsSquare (12 : ZMod 5) :=
    (apply_prime_eq_neg_one_iff_not_isSquare h12 hval (p := 5) (by decide) (by decide)).mp hχ5
  have hrad : fundamentalDiscriminantRadicand 12 = 3 := by
    norm_num [fundamentalDiscriminantRadicand_def]
  have hnsq3 : ¬ IsSquare (3 : ZMod 5) := by
    rw [← Int.cast_ofNat 3, ← hrad]
    exact (apply_prime_eq_neg_one_iff_not_isSquare_radicand h12 hval (p := 5)
      (by decide) (by decide)).mp hχ5
  exact ⟨h12, h5, h7, h11, hnsq12, hnsq3⟩

-- At `p = 2` the odd-prime Legendre dictionary fails: `χ_5(2) = -1`, while `legendreSym 2 5 = 1`.
example :
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    ∃ h5 : Int.IsFundamentalDiscr 5,
      fundamentalDiscriminantChar 5 h5 2 = -1 ∧
        legendreSym 2 5 = 1 ∧ IsSquare (5 : ZMod 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h5 : Int.IsFundamentalDiscr 5 := by
    have hsf : Squarefree (5 : ℤ) :=
      (Nat.prime_iff_prime_int.mp (by norm_num : Nat.Prime 5)).squarefree
    simpa [fundamentalDiscriminant_def] using isFundamentalDiscr_fundamentalDiscriminant hsf
  refine ⟨h5, ?_, by norm_num, ⟨1, rfl⟩⟩
  rw [fundamentalDiscriminantChar_two]
  decide
