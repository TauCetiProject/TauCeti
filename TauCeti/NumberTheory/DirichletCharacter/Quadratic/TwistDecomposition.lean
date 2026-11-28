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

At a product level `m * q * d`, a quadratic character is a lift of a quadratic character
modulo `m` or one of its three Legendre twists. In a tower of moduli `2 ^ k * m * q * d`,
where `q` and `d` are distinct auxiliary primes coprime to the dyadic base level, every
quadratic character is induced by a quadratic character
of conductor dividing `8 * m`, or by one of its three Legendre twists. Thus zero-free
conditions imposed on twists of the fixed finite family at `8 * m` can control real
characters even when the dyadic layer grows.

This is the character decomposition used in Levent Alpöge's `UpperTheory.Top.RealBox`
(`Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean`).
-/

public section

namespace DirichletCharacter

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

/-- A quadratic character at level `m * q * d` comes from a quadratic character at level `m`
by twisting at neither, either, or both of the two coprime auxiliary primes. All four
possibilities are compared at the common level `m * q * d`. -/
theorem exists_eq_legendreTwists_of_isQuadratic {m q d : ℕ} [Fact q.Prime] [Fact d.Prime]
    (χ : DirichletCharacter ℂ (m * q * d)) (hχ : χ.IsQuadratic)
    (hq : m.Coprime q) (hd : (m * q).Coprime d) :
    ∃ ψ : DirichletCharacter ℂ m, ψ.IsQuadratic ∧
      (χ = ψ.changeLevel ((dvd_mul_right m q).trans (dvd_mul_right (m * q) d)) ∨
        χ = (ψ.legendreTwist q).changeLevel (dvd_mul_right (m * q) d) ∨
        χ = (ψ.legendreTwist d).changeLevel (Nat.mul_dvd_mul_right (dvd_mul_right m q) d) ∨
        χ = (ψ.legendreTwist q).legendreTwist d) := by
  obtain ⟨η, hη, hχη⟩ := exists_eq_changeLevel_or_eq_legendreTwist hd hχ
  obtain ⟨ψ, hψ, hηψ⟩ := exists_eq_changeLevel_or_eq_legendreTwist hq hη
  refine ⟨ψ, hψ, ?_⟩
  rcases hχη with hχη | hχη <;> rcases hηψ with hηψ | hηψ
  · exact Or.inl (by rw [hχη, hηψ, ← changeLevel_trans])
  · exact Or.inr (Or.inl (by rw [hχη, hηψ]))
  · exact Or.inr (Or.inr (Or.inl (by rw [hχη, hηψ, legendreTwist_changeLevel])))
  · exact Or.inr (Or.inr (Or.inr (by rw [hχη, hηψ])))

open TauCeti in
/-- A quadratic character at level `2 ^ k * m * q * d` is induced by a primitive quadratic
character of conductor dividing `8 * m`, possibly twisted by either or both auxiliary
Legendre characters. The four alternatives compare primitive characters, not the functions
at the possibly imprimitive original level. -/
theorem exists_primitive_legendreTwist_of_isQuadratic {m k q d : ℕ} [NeZero m]
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
  obtain ⟨ψ, hψ, hχeq⟩ := χ.exists_eq_legendreTwists_of_isQuadratic hχ hq hd
  let ρ := PrimitiveDirichletCharacter.of ψ
  have hρ := PrimitiveDirichletCharacter.level_of_dvd ψ
  have hlift : changeLevel hρ ρ.character = ψ :=
    PrimitiveDirichletCharacter.changeLevel_character_of ψ
  refine ⟨ρ, ?_, (isQuadratic_changeLevel_iff hρ).mp (by rwa [hlift]), ?_⟩
  · simpa only [ρ, PrimitiveDirichletCharacter.level_of] using
      conductor_dvd_eight_mul_of_sq_eq_one hψ.sq_eq_one
  -- Each twist commutes with raising the level, which the primitive bundle forgets.
  rcases hχeq with hχeq | hχeq | hχeq | hχeq
  · exact Or.inl (by simp only [hχeq, PrimitiveDirichletCharacter.of_changeLevel, ρ])
  · exact Or.inr (Or.inl (by simp only [hχeq, ← hlift, legendreTwist_changeLevel,
      PrimitiveDirichletCharacter.of_changeLevel]))
  · exact Or.inr (Or.inr (Or.inl (by simp only [hχeq, ← hlift, legendreTwist_changeLevel,
      PrimitiveDirichletCharacter.of_changeLevel])))
  · exact Or.inr (Or.inr (Or.inr (by simp only [hχeq, ← hlift, legendreTwist_changeLevel,
      PrimitiveDirichletCharacter.of_changeLevel])))

end DirichletCharacter
