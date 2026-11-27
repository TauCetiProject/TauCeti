/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Bundle
public import TauCeti.NumberTheory.DirichletCharacter.Quadratic.LegendreTwist
import TauCeti.NumberTheory.DirichletCharacter.Quadratic.LocalFactor
import TauCeti.NumberTheory.DirichletCharacter.CoprimeLevel

/-!
# Quadratic characters with two auxiliary prime factors

In a tower of moduli `2 ^ k * m * q * d`, where `q` and `d` are distinct auxiliary primes
coprime to the base level, every quadratic character is induced by a quadratic character
of conductor dividing `8 * m`, or by one of its three Legendre twists. Thus zero-free
conditions imposed on twists of the fixed finite family at `8 * m` can control real
characters even when the dyadic layer grows.

This is the character decomposition used in Levent Alpöge's `UpperTheory.Top.RealBox`
(`Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean`).
-/

public section

namespace DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R]

/-- Increasing the dyadic part of a level introduces no characters of order dividing two
whose conductor fails to divide eight times the original level. -/
theorem conductor_dvd_eight_mul_of_sq_eq_one {m k : ℕ}
    {χ : DirichletCharacter R (2 ^ k * m)} (hχ : χ ^ 2 = 1) : χ.conductor ∣ 8 * m := by
  by_cases hm : m = 0
  · simp [hm]
  have hN : 2 ^ k * m ≠ 0 := mul_ne_zero (pow_ne_zero _ (by decide)) hm
  let : NeZero (2 ^ k * m) := ⟨hN⟩
  rw [← Nat.factorization_le_iff_dvd χ.conductor_ne_zero (mul_ne_zero (by decide) hm)]
  intro p
  have h₈ : (8 : ℕ).factorization = Finsupp.single 2 3 := Nat.prime_two.factorization_pow (k := 3)
  rw [Nat.factorization_mul (by decide : 8 ≠ 0) hm, h₈]
  by_cases hp : p = 2
  · subst p
    have hχ₂ := factorization_two_conductor_eq_zero_or_two_or_three_of_sq_eq_one hχ
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
    omega
  · have h := (Nat.factorization_le_iff_dvd χ.conductor_ne_zero hN).mpr
      χ.conductor_dvd_level p
    simpa [Nat.factorization_mul (pow_ne_zero k (by decide : 2 ≠ 0)) hm,
      Nat.prime_two.factorization_pow, Finsupp.single_eq_of_ne hp] using h

/-- At a level obtained by adjoining a coprime prime, a quadratic character is the lift of
its quadratic base factor or the Legendre twist of that factor. -/
theorem exists_eq_changeLevel_or_eq_legendreTwist {m p : ℕ} [Fact p.Prime]
    (hmp : m.Coprime p) {χ : DirichletCharacter ℂ (m * p)} (hχ : χ.IsQuadratic) :
    ∃ ψ : DirichletCharacter ℂ m, ψ.IsQuadratic ∧
      (χ = changeLevel (dvd_mul_right m p) ψ ∨ χ = ψ.legendreTwist p) := by
  let e := coprimeLevelEquiv (R := ℂ) hmp
  obtain ⟨⟨ψ, η⟩, h⟩ := e.surjective χ
  have hpow : (ψ, η) ^ 2 = 1 := e.injective (by rw [map_pow, h, hχ.sq_eq_one, map_one])
  have hψ : ψ.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr (congrArg Prod.fst hpow)
  have hη : η.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr (congrArg Prod.snd hpow)
  have heq := (coprimeLevelEquiv_apply hmp ψ η).symm.trans h
  refine ⟨ψ, hψ, ?_⟩
  rcases (isQuadratic_iff_eq_one_or_eq_quadraticChar η).mp hη with (rfl | rfl)
  · exact Or.inl (by simpa only [map_one, mul_one] using heq.symm)
  · exact Or.inr (heq.symm.trans (legendreTwist_def ψ p).symm)

open TauCeti in
/-- A quadratic character at level `2 ^ k * m * q * d` is induced by a primitive quadratic
character of conductor dividing `8 * m`, possibly twisted by either or both auxiliary
Legendre characters. The four alternatives compare primitive characters, not the functions
at the possibly imprimitive original level. -/
theorem exists_primitive_legendre_twist_of_isQuadratic {m k q d : ℕ} [NeZero m]
    [Fact q.Prime] [Fact d.Prime] (hq : (2 ^ k * m).Coprime q)
    (hd : (2 ^ k * m * q).Coprime d) {χ : DirichletCharacter ℂ (2 ^ k * m * q * d)}
    (hχ : χ.IsQuadratic) :
    ∃ ρ : PrimitiveDirichletCharacter, (ρ.level : ℕ) ∣ 8 * m ∧ ρ.character.IsQuadratic ∧
      (PrimitiveDirichletCharacter.of χ = ρ ∨
        PrimitiveDirichletCharacter.of χ = PrimitiveDirichletCharacter.of
          (ρ.character.legendreTwist q) ∨
        PrimitiveDirichletCharacter.of χ = PrimitiveDirichletCharacter.of
          (ρ.character.legendreTwist d) ∨
        PrimitiveDirichletCharacter.of χ = PrimitiveDirichletCharacter.of
          ((ρ.character.legendreTwist q).legendreTwist d)) := by
  let : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  let : NeZero d := ⟨(Fact.out : d.Prime).ne_zero⟩
  let : NeZero (2 ^ k * m) := ⟨mul_ne_zero (pow_ne_zero _ (by decide)) (NeZero.ne m)⟩
  obtain ⟨η, hη, hχeq⟩ := exists_eq_changeLevel_or_eq_legendreTwist hd hχ
  obtain ⟨ψ, hψ, hηeq⟩ := exists_eq_changeLevel_or_eq_legendreTwist hq hη
  let ρ := PrimitiveDirichletCharacter.of ψ
  have hρ := PrimitiveDirichletCharacter.level_of_dvd ψ
  have hlift : changeLevel hρ ρ.character = ψ :=
    PrimitiveDirichletCharacter.changeLevel_character_of ψ
  refine ⟨ρ, ?_, (isQuadratic_changeLevel_iff hρ).mp (by rwa [hlift]), ?_⟩
  · simpa only [ρ, PrimitiveDirichletCharacter.level_of] using
      conductor_dvd_eight_mul_of_sq_eq_one hψ.sq_eq_one
  -- Each twist commutes with raising the level, which the primitive bundle forgets.
  rcases hχeq with hχeq | hχeq <;> rcases hηeq with hηeq | hηeq
  · exact Or.inl (by simp only [hχeq, hηeq, PrimitiveDirichletCharacter.of_changeLevel, ρ])
  · exact Or.inr (Or.inl (by simp only [hχeq, hηeq, ← hlift, legendreTwist_changeLevel,
      PrimitiveDirichletCharacter.of_changeLevel]))
  · exact Or.inr (Or.inr (Or.inl (by simp only [hχeq, hηeq, ← hlift, legendreTwist_changeLevel,
      PrimitiveDirichletCharacter.of_changeLevel])))
  · exact Or.inr (Or.inr (Or.inr (by simp only [hχeq, hηeq, ← hlift, legendreTwist_changeLevel,
      PrimitiveDirichletCharacter.of_changeLevel])))

end DirichletCharacter
