/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Conrey
public import TauCeti.NumberTheory.DirichletCharacter.OddPrimePower.Quadratic

/-!
# Local quadratic-character examples

Worked computations of complex Dirichlet characters at levels 3, 9, 25 and 16.
At level nine, the two primitive characters of order three distinguish the complete character
group from its quadratic subgroup. The level-three and level-twenty-five tables include
nonunits, where the characters vanish. At level sixteen the four quadratic value triples exclude
the all-minus-one triple.
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
  have h2 : quadraticChar (ZMod 3) 2 = -1 := by decide
  have h3 : quadraticChar (ZMod 3) 3 = 0 := by decide
  norm_num [hc, MulChar.ringHomComp_apply, h2, h3]

-- There are five nonprincipal characters at level nine.
example : Nat.card {χ : DirichletCharacter ℂ 9 // χ ≠ 1} = 5 := by
  rw [← Nat.card_congr (Equiv.subtypeEquiv (TauCeti.conreyCharacter 9).toEquiv
    (fun u ↦ (TauCeti.conreyCharacter 9).map_ne_one_iff.symm))]
  have ht : Nat.totient 9 = 6 := by decide
  norm_num [Nat.card_eq_fintype_card, ht]

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
  have hlevel : χ.conductor ∣ 3 ^ 2 := χ.conductor_dvd_level
  obtain ⟨k, hk, hc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hlevel
  refine ⟨?_, fun hq ↦ by simpa [hχ] using orderOf_dvd_of_pow_eq_one hq.sq_eq_one⟩
  interval_cases k
  · norm_num [hc] at hd
  · norm_num [hc, Nat.totient_prime Nat.prime_three] at hd
  · exact (isPrimitive_def χ).mpr hc

-- The Legendre lift retains conductor five and vanishes on the nonunits of level twenty-five.
example :
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    let χ : DirichletCharacter ℂ 25 := changeLevel (by decide : 5 ∣ 25)
      ((quadraticChar (ZMod 5)).ringHomComp (Int.castRingHom ℂ))
    χ (2 : ℕ) = -1 ∧ χ 5 = 0 ∧ χ 10 = 0 ∧ χ.conductor = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  dsimp only
  refine ⟨?_, MulChar.map_nonunit _ (by decide : ¬IsUnit (5 : ZMod 25)),
    MulChar.map_nonunit _ (by decide : ¬IsUnit (10 : ZMod 25)),
    conductor_changeLevel_quadraticChar (by norm_num) (by decide) _⟩
  have h2 : quadraticChar (ZMod 5) (2 : ℕ) = -1 := by decide
  rw [changeLevel_natCast_of_coprime _ _ (by decide : Nat.Coprime 2 25),
    MulChar.ringHomComp_apply, h2]
  simp

/-! ## The four quadratic characters at level sixteen -/

example : Nat.card {χ : DirichletCharacter ℂ 16 // χ.IsQuadratic} = 4 ∧
    Nat.card (DirichletCharacter ℂ 16) = 8 := by
  refine ⟨?_, ?_⟩
  · rw [← Nat.card_congr (Equiv.subtypeEquiv (p := fun u ↦ u ^ 2 = 1)
      (TauCeti.conreyCharacter 16).toEquiv (fun u ↦ by
        rw [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
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
  have h3 : ZMod.χ₄ (3 : ℕ) = -1 := by decide
  have h5 : ZMod.χ₄ (5 : ℕ) = 1 := by decide
  have h7 : ZMod.χ₄ (7 : ℕ) = -1 := by decide
  norm_num [MulChar.ringHomComp_apply, h3, h5, h7]

example :
    let χ : DirichletCharacter ℂ 16 := changeLevel (by decide : 8 ∣ 16)
      (ZMod.χ₈.ringHomComp (Int.castRingHom ℂ))
    χ (3 : ℕ) = -1 ∧ χ (5 : ℕ) = -1 ∧ χ (7 : ℕ) = 1 := by
  dsimp only
  rw [changeLevel_natCast_of_coprime _ _ (by decide : Nat.Coprime 3 16),
    changeLevel_natCast_of_coprime _ _ (by decide : Nat.Coprime 5 16),
    changeLevel_natCast_of_coprime _ _ (by decide : Nat.Coprime 7 16)]
  have h3 : ZMod.χ₈ (3 : ℕ) = -1 := by decide
  have h5 : ZMod.χ₈ (5 : ℕ) = -1 := by decide
  have h7 : ZMod.χ₈ (7 : ℕ) = 1 := by decide
  norm_num [MulChar.ringHomComp_apply, h3, h5, h7]

example :
    let χ : DirichletCharacter ℂ 16 := changeLevel (by decide : 8 ∣ 16)
      (ZMod.χ₈'.ringHomComp (Int.castRingHom ℂ))
    χ (3 : ℕ) = 1 ∧ χ (5 : ℕ) = -1 ∧ χ (7 : ℕ) = -1 := by
  dsimp only
  rw [changeLevel_natCast_of_coprime _ _ (by decide : Nat.Coprime 3 16),
    changeLevel_natCast_of_coprime _ _ (by decide : Nat.Coprime 5 16),
    changeLevel_natCast_of_coprime _ _ (by decide : Nat.Coprime 7 16)]
  have h3 : ZMod.χ₈' (3 : ℕ) = 1 := by decide
  have h5 : ZMod.χ₈' (5 : ℕ) = -1 := by decide
  have h7 : ZMod.χ₈' (7 : ℕ) = -1 := by decide
  norm_num [MulChar.ringHomComp_apply, h3, h5, h7]

-- This obstruction uses multiplicativity alone, without a quadraticity assumption.
example : ¬∃ χ : DirichletCharacter ℂ 16, χ 3 = -1 ∧ χ 5 = -1 ∧ χ 7 = -1 := by
  rintro ⟨χ, h3, h5, h7⟩
  have hsq : (5 : ZMod 16) ^ 2 = 9 := by decide
  have hprod : (3 : ZMod 16) * 5 = 15 := by decide
  have hprod' : (15 : ZMod 16) * 9 = 7 := by decide
  have h9 : χ 9 = 1 := by
    simpa only [hsq, h5, neg_one_sq] using map_pow χ 5 2
  have h15 : χ 15 = 1 := by
    simpa only [hprod, h3, h5, neg_mul_neg, one_mul]
      using map_mul χ 3 5
  have h := map_mul χ 15 9
  rw [hprod', h7, h15, h9] at h
  norm_num at h
