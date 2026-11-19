/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.RingTheory.ZMod.UnitsCyclic
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Conrey
public import TauCeti.NumberTheory.DirichletCharacter.OddPrimePower.Quadratic

/-!
# Local quadratic-character examples

These examples check QuadraticCharactersAndReduction §§1.1–1.2 on actual complex Dirichlet
characters. At level nine, the two primitive characters of order three distinguish the complete
character group from its quadratic subgroup. The level-three and level-twenty-five tables include
nonunits, where the characters vanish. At level sixteen the four quadratic value triples exclude
the all-minus-one triple, while the local Conrey character labelled by 5 takes the value `I` at 5
and is primitive of order four.
-/

public section

open DirichletCharacter

/-! ## Odd prime-power levels -/

-- The principal character and the Legendre character at level three.
example :
    (1 : DirichletCharacter ℂ 3) 1 = 1 ∧
    (1 : DirichletCharacter ℂ 3) 2 = 1 ∧
    (1 : DirichletCharacter ℂ 3) 3 = 0 := by
  norm_num [MulChar.one_apply (by decide : IsUnit (2 : ZMod 3)),
    MulChar.map_nonunit (1 : DirichletCharacter ℂ 3) (by decide : ¬IsUnit (3 : ZMod 3))]

example :
    let χ : DirichletCharacter ℂ 3 := (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)
    χ 1 = 1 ∧ χ 2 = -1 ∧ χ 3 = 0 ∧ χ.conductor = 3 := by
  dsimp only
  have hc : conductor ((quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)) = 3 := by
    simpa using conductor_changeLevel_quadraticChar (R := ℂ)
      (by norm_num) (by decide : 3 ≠ 2) (dvd_refl 3)
  norm_num [hc, MulChar.ringHomComp_apply,
    show quadraticChar (ZMod 3) 2 = -1 by decide,
    show quadraticChar (ZMod 3) 3 = 0 by decide]

-- There are six characters at level nine, but only two are quadratic.
example : Nat.card {χ : DirichletCharacter ℂ 9 // χ ≠ 1} = 5 := by
  rw [← Nat.card_congr (Equiv.subtypeEquiv (TauCeti.conreyCharacter 9).toEquiv
    (fun u ↦ (TauCeti.conreyCharacter 9).map_ne_one_iff.symm))]
  norm_num [Nat.card_eq_fintype_card, show Nat.totient 9 = 6 by decide]

example :
    let χ : DirichletCharacter ℂ 9 :=
      changeLevel (by decide : 3 ∣ 9)
        ((quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ))
    (∀ ψ : DirichletCharacter ℂ 9, orderOf ψ = 2 ↔ ψ = χ) ∧ χ.conductor = 3 := by
  dsimp only
  refine ⟨?_, conductor_changeLevel_quadraticChar (by norm_num) (by decide) _⟩
  intro ψ
  rw [orderOf_eq_prime_iff, ← MulChar.isQuadratic_iff_sq_eq_one,
    isQuadratic_iff_eq_one_or_eq_changeLevel_quadraticChar (p := 3) (by decide) 2 ψ]
  have hn : changeLevel (by decide : 3 ∣ 9)
      ((quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)) ≠ 1 := by
    simpa only [ne_eq, changeLevel_eq_one_iff] using
      quadraticChar_ringHomComp_ne_one (R := ℂ) (by norm_num) (by decide : 3 ≠ 2)
  simp only [exists_prop_of_true (by decide : 3 ∣ 3 ^ 2), or_and_right, and_not_self,
    false_or, and_iff_left_iff_imp]
  exact fun h ↦ h.symm ▸ hn

-- The remaining order-three characters must not be included in the quadratic classification.
example : Nat.card {χ : DirichletCharacter ℂ 9 // orderOf χ = 3} = 2 := by
  rw [← Nat.card_congr (Equiv.subtypeEquiv (p := fun u ↦ orderOf u = 3)
    (TauCeti.conreyCharacter 9).toEquiv (fun u ↦ (congrArg (fun n : ℕ ↦ n = 3)
      ((TauCeti.conreyCharacter 9).orderOf_eq u)).symm.to_iff))]
  simp_rw [orderOf_eq_prime_iff (p := 3)]
  exact Nat.card_eq_fintype_card.trans (by decide)

example (χ : DirichletCharacter ℂ 9) (hχ : orderOf χ = 3) :
    χ.IsPrimitive ∧ ¬χ.IsQuadratic := by
  have ho : orderOf χ.primitiveCharacter = 3 :=
    (orderOf_injective (changeLevel χ.conductor_dvd_level)
      (changeLevel_injective _) χ.primitiveCharacter).symm.trans
      ((congrArg orderOf χ.changeLevel_primitiveCharacter).trans hχ)
  have hd : 3 ∣ Nat.card (DirichletCharacter ℂ χ.conductor) :=
    ho ▸ orderOf_dvd_natCard χ.primitiveCharacter
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  rw [card_eq_totient_of_hasEnoughRootsOfUnity] at hd
  -- The concrete level is 3² = 9.
  obtain ⟨k, hk, hc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (show χ.conductor ∣ 3 ^ 2 from χ.conductor_dvd_level)
  refine ⟨?_, fun hq ↦ by simpa [hχ] using orderOf_dvd_of_pow_eq_one hq.sq_eq_one⟩
  interval_cases k
  · norm_num [hc] at hd
  · norm_num [hc, Nat.totient_prime Nat.prime_three] at hd
  · exact (isPrimitive_def χ).mpr hc

section LevelTwentyFive

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- The Legendre lift retains conductor five and vanishes on the nonunits of level twenty-five.
example :
    let χ : DirichletCharacter ℂ 25 := changeLevel (by decide : 5 ∣ 25)
      ((quadraticChar (ZMod 5)).ringHomComp (Int.castRingHom ℂ))
    χ (2 : ℕ) = -1 ∧ χ 5 = 0 ∧ χ 10 = 0 ∧ χ.conductor = 5 := by
  dsimp only
  refine ⟨?_, MulChar.map_nonunit _ (by decide : ¬IsUnit (5 : ZMod 25)),
    MulChar.map_nonunit _ (by decide : ¬IsUnit (10 : ZMod 25)),
    conductor_changeLevel_quadraticChar (by norm_num) (by decide) _⟩
  rw [changeLevel_natCast_of_coprime _ _ (by decide : Nat.Coprime 2 25),
    MulChar.ringHomComp_apply, show quadraticChar (ZMod 5) (2 : ℕ) = -1 by decide]
  simp

end LevelTwentyFive

/-! ## The four quadratic characters at level sixteen -/

example : Nat.card {χ : DirichletCharacter ℂ 16 // χ.IsQuadratic} = 4 ∧
    Nat.card (DirichletCharacter ℂ 16) = 8 := by
  refine ⟨?_, ?_⟩
  · rw [← Nat.card_congr (Equiv.subtypeEquiv (p := fun u ↦ u ^ 2 = 1)
      (TauCeti.conreyCharacter 16).toEquiv (fun u ↦ by
        -- The underlying equivalence evaluates the same character.
        change u ^ 2 = 1 ↔ ((TauCeti.conreyCharacter 16) u).IsQuadratic
        rw [MulChar.isQuadratic_iff_sq_eq_one, ← map_pow (TauCeti.conreyCharacter 16) u 2,
          (TauCeti.conreyCharacter 16).map_eq_one_iff]))]
    exact Nat.card_eq_fintype_card.trans (by decide)
  · rw [card_eq_totient_of_hasEnoughRootsOfUnity]
    decide

example :
    (1 : DirichletCharacter ℂ 16) (3 : ℕ) = 1 ∧
    (1 : DirichletCharacter ℂ 16) (5 : ℕ) = 1 ∧
    (1 : DirichletCharacter ℂ 16) (7 : ℕ) = 1 := by
  exact ⟨MulChar.one_apply (by decide), MulChar.one_apply (by decide),
    MulChar.one_apply (by decide)⟩

example :
    let χ : DirichletCharacter ℂ 16 := changeLevel (by decide : 4 ∣ 16)
      (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))
    χ (3 : ℕ) = -1 ∧ χ (5 : ℕ) = 1 ∧ χ (7 : ℕ) = -1 := by
  dsimp only
  rw [changeLevel_natCast_of_coprime _ _ (by decide : Nat.Coprime 3 16),
    changeLevel_natCast_of_coprime _ _ (by decide : Nat.Coprime 5 16),
    changeLevel_natCast_of_coprime _ _ (by decide : Nat.Coprime 7 16)]
  norm_num [MulChar.ringHomComp_apply,
    show ZMod.χ₄ (3 : ℕ) = -1 by decide,
    show ZMod.χ₄ (5 : ℕ) = 1 by decide,
    show ZMod.χ₄ (7 : ℕ) = -1 by decide]

example :
    let χ : DirichletCharacter ℂ 16 := changeLevel (by decide : 8 ∣ 16)
      (ZMod.χ₈.ringHomComp (Int.castRingHom ℂ))
    χ (3 : ℕ) = -1 ∧ χ (5 : ℕ) = -1 ∧ χ (7 : ℕ) = 1 := by
  dsimp only
  rw [changeLevel_natCast_of_coprime _ _ (by decide : Nat.Coprime 3 16),
    changeLevel_natCast_of_coprime _ _ (by decide : Nat.Coprime 5 16),
    changeLevel_natCast_of_coprime _ _ (by decide : Nat.Coprime 7 16)]
  norm_num [MulChar.ringHomComp_apply,
    show ZMod.χ₈ (3 : ℕ) = -1 by decide,
    show ZMod.χ₈ (5 : ℕ) = -1 by decide,
    show ZMod.χ₈ (7 : ℕ) = 1 by decide]

example :
    let χ : DirichletCharacter ℂ 16 := changeLevel (by decide : 8 ∣ 16)
      (ZMod.χ₈'.ringHomComp (Int.castRingHom ℂ))
    χ (3 : ℕ) = 1 ∧ χ (5 : ℕ) = -1 ∧ χ (7 : ℕ) = -1 := by
  dsimp only
  rw [changeLevel_natCast_of_coprime _ _ (by decide : Nat.Coprime 3 16),
    changeLevel_natCast_of_coprime _ _ (by decide : Nat.Coprime 5 16),
    changeLevel_natCast_of_coprime _ _ (by decide : Nat.Coprime 7 16)]
  norm_num [MulChar.ringHomComp_apply,
    show ZMod.χ₈' (3 : ℕ) = 1 by decide,
    show ZMod.χ₈' (5 : ℕ) = -1 by decide,
    show ZMod.χ₈' (7 : ℕ) = -1 by decide]

-- This obstruction uses multiplicativity alone, without a quadraticity assumption.
example : ¬∃ χ : DirichletCharacter ℂ 16, χ 3 = -1 ∧ χ 5 = -1 ∧ χ 7 = -1 := by
  rintro ⟨χ, h3, h5, h7⟩
  have h9 : χ 9 = 1 := by
    simpa only [show (5 : ZMod 16) ^ 2 = 9 by decide, h5, neg_one_sq] using map_pow χ 5 2
  have h15 : χ 15 = 1 := by
    simpa only [show (3 : ZMod 16) * 5 = 15 by decide, h3, h5, neg_mul_neg, one_mul]
      using map_mul χ 3 5
  have h := map_mul χ 15 9
  rw [show (15 : ZMod 16) * 9 = 7 by decide, h7, h15, h9] at h
  norm_num at h

-- The actual local Conrey witness also records the value omitted by the weaker existential check.
example :
    let χ : DirichletCharacter ℂ 16 := MulChar.ofUnitHom
      (Circle.toUnits.comp (TauCeti.conreyLocal 2 4 (ZMod.unitFive (n := 4))))
    χ 5 = Complex.I ∧ χ.IsPrimitive ∧ orderOf χ = 4 ∧ ¬χ.IsQuadratic := by
  let f := Circle.toUnits.comp (TauCeti.conreyLocal 2 4 (ZMod.unitFive (n := 4)))
  let χ : DirichletCharacter ℂ 16 := MulChar.ofUnitHom f
  have h5 : χ 5 = Complex.I := by
    rw [← ZMod.coe_unitFive (n := 4), MulChar.ofUnitHom_coe]
    -- Coercing the unit hom recovers the circle-valued Conrey pairing.
    change (TauCeti.conreyLocal 2 4 (ZMod.unitFive (n := 4))
      (ZMod.unitFive (n := 4)) : ℂ) = Complex.I
    rw [TauCeti.conreyLocal_two_apply (e := 2) (x := 0) (y := 0)
      (a := 1) (b := 1) (by simp) (by simp)]
    norm_num only [Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero, zero_div,
      Complex.exp_zero, mul_one, one_mul]
    rw [show 2 * (Real.pi : ℂ) * Complex.I / 4 = (Real.pi : ℂ) / 2 * Complex.I by ring]
    exact Complex.exp_pi_div_two_mul_I
  have h9 : χ 9 = -1 := by
    simpa only [show (5 : ZMod 16) ^ 2 = 9 by decide, h5, Complex.I_sq]
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
  have h4 : χ ^ 4 = 1 := by
    refine MulChar.ext (fun u ↦ ?_)
    rw [MulChar.pow_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val,
      (by decide : ∀ u : (ZMod 16)ˣ, u ^ 4 = 1) u]
    simp
  exact ⟨h5, hp, orderOf_eq_prime_pow (p := 2) (n := 1) hn h4,
    fun hq ↦ hn hq.sq_eq_one⟩
