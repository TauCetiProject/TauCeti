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

The twist family is the one used in `UpperTheory.Top.RealBox`
(`src/Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean`) of Levent Alpöge's
formalization of the Riemann hypothesis for Dirichlet L-functions,
https://github.com/leanprover-community/riemann-hypothesis (rev. `40e56ba`).
-/

public section

namespace ZMod

/-- The Chinese remainder isomorphism on units sends a unit modulo `M * N` to the pair of its
reductions modulo `M` and modulo `N`. -/
theorem prodUnits_mapEquiv_chineseRemainder {M N : ℕ} (hMN : M.Coprime N)
    (u : (ZMod (M * N))ˣ) :
    MulEquiv.prodUnits (Units.mapEquiv (chineseRemainder hMN).toMulEquiv u) =
      (unitsMap (dvd_mul_right M N) u, unitsMap (dvd_mul_left N M) u) := by
  have he : (chineseRemainder hMN : ZMod (M * N) →+* ZMod M × ZMod N) =
      (castHom (dvd_mul_right M N) (ZMod M)).prod (castHom (dvd_mul_left N M) (ZMod N)) :=
    RingHom.ext_zmod _ _
  exact Prod.ext (Units.ext congr(($(he) u).1)) (Units.ext congr(($(he) u).2))

/-- For coprime `M` and `N`, every pair of units modulo `M` and modulo `N` is the pair of
reductions of a unit modulo `M * N`. -/
theorem exists_unitsMap_eq_and_unitsMap_eq {M N : ℕ} (hMN : M.Coprime N) (v : (ZMod M)ˣ)
    (w : (ZMod N)ˣ) :
    ∃ u : (ZMod (M * N))ˣ, unitsMap (dvd_mul_right M N) u = v ∧
      unitsMap (dvd_mul_left N M) u = w := by
  let e := (Units.mapEquiv (chineseRemainder hMN).toMulEquiv).trans MulEquiv.prodUnits
  refine ⟨e.symm (v, w), ?_⟩
  have h := prodUnits_mapEquiv_chineseRemainder hMN (e.symm (v, w))
  have h' : e (e.symm (v, w)) = (v, w) := e.apply_symm_apply _
  exact Prod.ext_iff.mp (h.symm.trans h')

end ZMod

namespace DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R]

/-- At a product of coprime levels, every Dirichlet character is the product of lifts of
characters from the two levels. -/
theorem exists_eq_changeLevel_mul_of_coprime {M N : ℕ} (χ : DirichletCharacter R (M * N))
    (hMN : M.Coprime N) :
    ∃ ψ : DirichletCharacter R M, ∃ φ : DirichletCharacter R N,
      χ = ψ.changeLevel (dvd_mul_right M N) * φ.changeLevel (dvd_mul_left N M) := by
  let e := (Units.mapEquiv (ZMod.chineseRemainder hMN).toMulEquiv).trans MulEquiv.prodUnits
  let f := χ.toUnitHom.comp e.symm.toMonoidHom
  refine ⟨MulChar.ofUnitHom (f.comp (MonoidHom.inl _ _)),
    MulChar.ofUnitHom (f.comp (MonoidHom.inr _ _)), MulChar.ext fun u ↦ ?_⟩
  have he : e u = (ZMod.unitsMap (dvd_mul_right M N) u, ZMod.unitsMap (dvd_mul_left N M) u) :=
    ZMod.prodUnits_mapEquiv_chineseRemainder hMN u
  have hu : e.symm (ZMod.unitsMap (dvd_mul_right M N) u, 1) *
      e.symm (1, ZMod.unitsMap (dvd_mul_left N M) u) = u := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul, ← he, e.symm_apply_apply]
  rw [MulChar.mul_apply, changeLevel_def, changeLevel_def, MulChar.ofUnitHom_coe,
    MulChar.ofUnitHom_coe]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply,
    MonoidHom.inr_apply, MulChar.ofUnitHom_coe, f, MulEquiv.coe_toMonoidHom]
  rw [← Units.val_mul, ← map_mul, hu]
  rfl

/-- At a product of coprime levels, a character of order dividing two splits as the product
of lifts of characters of order dividing two from the two levels. -/
theorem exists_eq_changeLevel_mul_of_coprime_of_sq_eq_one {M N : ℕ}
    (χ : DirichletCharacter R (M * N)) (hMN : M.Coprime N) (hχ : χ ^ 2 = 1) :
    ∃ ψ : DirichletCharacter R M, ∃ φ : DirichletCharacter R N,
      ψ ^ 2 = 1 ∧ φ ^ 2 = 1 ∧
        χ = ψ.changeLevel (dvd_mul_right M N) * φ.changeLevel (dvd_mul_left N M) := by
  obtain ⟨ψ, φ, rfl⟩ := χ.exists_eq_changeLevel_mul_of_coprime hMN
  have hchange {K : ℕ} (hK : K ∣ M * N) (ξ : DirichletCharacter R K) (u : (ZMod (M * N))ˣ) :
      ξ.changeLevel hK u = ξ (ZMod.unitsMap hK u) := by
    rw [changeLevel_def, MulChar.ofUnitHom_coe]
    rfl
  have hsq (v : (ZMod M)ˣ) (w : (ZMod N)ˣ) : (ψ v * φ w) ^ 2 = 1 := by
    obtain ⟨u, hv, hw⟩ := ZMod.exists_unitsMap_eq_and_unitsMap_eq hMN v w
    have := congr($(hχ) (u : ZMod (M * N)))
    rwa [MulChar.pow_apply_coe, MulChar.one_apply_coe, MulChar.mul_apply, hchange, hchange,
      hv, hw] at this
  refine ⟨MulChar.ext fun v ↦ ?_, MulChar.ext fun w ↦ ?_, rfl⟩
  · simpa only [MulChar.pow_apply_coe, MulChar.one_apply_coe, Units.val_one, MulChar.map_one,
      mul_one] using hsq v 1
  · simpa only [MulChar.pow_apply_coe, MulChar.one_apply_coe, Units.val_one, MulChar.map_one,
      one_mul] using hsq 1 w

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
