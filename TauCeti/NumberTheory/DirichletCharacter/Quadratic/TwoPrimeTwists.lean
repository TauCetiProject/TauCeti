/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Quadratic.LegendreTwist
import Mathlib.Algebra.Group.Prod
import TauCeti.NumberTheory.DirichletCharacter.Quadratic

/-!
# Quadratic twists at two auxiliary primes

At a level formed by adjoining two distinct auxiliary primes coprime to the base level,
every quadratic character is a lift of a base character or one of its three Legendre twists.
This identifies the characters to test when seeking a common real zero gap.

The twist family is the one used in Levent Alpöge's `UpperTheory.Top.RealBox`
(`Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean`).
-/

public section

namespace DirichletCharacter

/-- At a product of coprime levels, a character of order dividing two splits as the product
of lifts of characters of order dividing two from the two levels. -/
theorem exists_eq_changeLevel_mul_of_coprime_of_sq_eq_one {R : Type*} [CommMonoidWithZero R]
    {M N : ℕ} (χ : DirichletCharacter R (M * N)) (hMN : M.Coprime N) (hχ : χ ^ 2 = 1) :
    ∃ ψ : DirichletCharacter R M, ∃ φ : DirichletCharacter R N,
      ψ ^ 2 = 1 ∧ φ ^ 2 = 1 ∧
        χ = ψ.changeLevel (dvd_mul_right M N) * φ.changeLevel (dvd_mul_left N M) := by
  let e := (Units.mapEquiv (ZMod.chineseRemainder hMN).toMulEquiv).trans MulEquiv.prodUnits
  let f := χ.toUnitHom.comp e.symm.toMonoidHom
  let ψ : DirichletCharacter R M := MulChar.ofUnitHom (f.comp (MonoidHom.inl _ _))
  let φ : DirichletCharacter R N := MulChar.ofUnitHom (f.comp (MonoidHom.inr _ _))
  have he (u : (ZMod (M * N))ˣ) : e u =
      (ZMod.unitsMap (dvd_mul_right M N) u, ZMod.unitsMap (dvd_mul_left N M) u) := by
    have he' : (ZMod.chineseRemainder hMN : ZMod (M * N) →+* ZMod M × ZMod N) =
        (ZMod.castHom (dvd_mul_right M N) (ZMod M)).prod
          (ZMod.castHom (dvd_mul_left N M) (ZMod N)) := RingHom.ext_zmod _ _
    exact Prod.ext (Units.ext congr(($(he') u).1)) (Units.ext congr(($(he') u).2))
  have hsq (u : (ZMod (M * N))ˣ) : χ u ^ 2 = 1 := by
    rw [← MulChar.pow_apply_coe, hχ, MulChar.one_apply_coe]
  refine ⟨ψ, φ, MulChar.ext ?_, MulChar.ext ?_, MulChar.ext ?_⟩
  · intro u
    simpa [ψ, f, MulChar.pow_apply_coe, MulChar.one_apply_coe] using hsq (e.symm (u, 1))
  · intro u
    simpa [φ, f, MulChar.pow_apply_coe, MulChar.one_apply_coe] using hsq (e.symm (1, u))
  · intro u
    have hu : ((e u).1, 1) * (1, (e u).2) = e u := by simp
    have hm := congrArg (fun v ↦ χ (e.symm v : (ZMod (M * N))ˣ)) hu
    simp only [map_mul, Units.val_mul, MulEquiv.symm_apply_apply] at hm
    simpa [ψ, φ, f, changeLevel_def, he] using hm.symm

/-- Adjoining a prime coprime to the base level gives only two possibilities for a quadratic
character: it is a lift from the base level, or a Legendre twist of a quadratic character
from that level. -/
theorem exists_eq_changeLevel_or_legendreTwist_of_isQuadratic {M p : ℕ} [Fact p.Prime]
    (χ : DirichletCharacter ℂ (M * p)) (hχ : χ.IsQuadratic) (hMp : M.Coprime p) :
    ∃ ψ : DirichletCharacter ℂ M, ψ.IsQuadratic ∧
      (χ = ψ.changeLevel (dvd_mul_right M p) ∨ χ = ψ.legendreTwist p) := by
  obtain ⟨ψ, φ, hψ, hφ, rfl⟩ :=
    χ.exists_eq_changeLevel_mul_of_coprime_of_sq_eq_one hMp hχ.sq_eq_one
  refine ⟨ψ, MulChar.isQuadratic_iff_sq_eq_one.mpr hψ, ?_⟩
  rcases (isQuadratic_iff_eq_one_or_eq_quadraticChar φ).mp
    (MulChar.isQuadratic_iff_sq_eq_one.mpr hφ) with rfl | rfl
  · exact Or.inl (by simp)
  · exact Or.inr (legendreTwist_def ψ p).symm

/-- A quadratic character at level `M * q * d` comes from a quadratic character at level `M`
by twisting at neither, either, or both of the two coprime auxiliary primes. All four
possibilities are compared at the common level `M * q * d`. -/
theorem exists_eq_legendreTwists_of_isQuadratic {M q d : ℕ} [Fact q.Prime] [Fact d.Prime]
    (χ : DirichletCharacter ℂ (M * q * d)) (hχ : χ.IsQuadratic)
    (hMq : M.Coprime q) (hMqd : (M * q).Coprime d) :
    ∃ ψ : DirichletCharacter ℂ M, ψ.IsQuadratic ∧
      (χ = ψ.changeLevel ((dvd_mul_right M q).trans (dvd_mul_right (M * q) d)) ∨
        χ = (ψ.legendreTwist q).changeLevel (dvd_mul_right (M * q) d) ∨
        χ = (ψ.legendreTwist d).changeLevel (mul_dvd_mul_right (dvd_mul_right M q) d) ∨
        χ = (ψ.legendreTwist q).legendreTwist d) := by
  obtain ⟨ξ, hξ, hχξ⟩ := χ.exists_eq_changeLevel_or_legendreTwist_of_isQuadratic hχ hMqd
  obtain ⟨ψ, hψ, hξψ⟩ := ξ.exists_eq_changeLevel_or_legendreTwist_of_isQuadratic hξ hMq
  refine ⟨ψ, hψ, ?_⟩
  rcases hχξ with hχξ | hχξ <;> rcases hξψ with hξψ | hξψ
  · exact Or.inl (by rw [hχξ, hξψ, ← changeLevel_trans])
  · exact Or.inr (Or.inl (by rw [hχξ, hξψ]))
  · exact Or.inr (Or.inr (Or.inl (by rw [hχξ, hξψ, legendreTwist_changeLevel])))
  · exact Or.inr (Or.inr (Or.inr (by rw [hχξ, hξψ])))

end DirichletCharacter
