/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Conductor
import TauCeti.NumberTheory.MulChar.Prod

/-!
# Dirichlet characters at a product of coprime levels

At coprime levels `m` and `n`, lifting and multiplying identifies pairs of Dirichlet
characters with characters of level `m * n`. This is `MulChar.coprodEquiv` transported
along the Chinese remainder isomorphism `ZMod.chineseRemainder`.

`DirichletCharacter.conductor_eq_mul_coprimeLevelEquiv_symm` gives the conductor as the product
of the two factor conductors, using `DirichletCharacter.conductor_mul_of_coprime` and Mathlib's
`DirichletCharacter.conductor_changeLevel`. Consequently,
`DirichletCharacter.isPrimitive_iff_coprimeLevelEquiv_symm` tests primitivity on the two factors.
-/

public section

namespace DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R] {m n : ℕ}

/-- The Chinese remainder decomposition of a Dirichlet character at coprime levels.
The forward map lifts the two factors to the product level and multiplies them. -/
noncomputable def coprimeLevelEquiv (h : m.Coprime n) :
    DirichletCharacter R m × DirichletCharacter R n ≃* DirichletCharacter R (m * n) :=
  MulChar.coprodEquiv.trans <| MulChar.mulEquivToUnitHom.trans <|
    (MulEquiv.monoidHomCongrLeft (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).symm).trans
      MulChar.mulEquivToUnitHom.symm

/-- Multiply the lifts of the two factors to assemble their character at the product level. -/
@[simp]
theorem coprimeLevelEquiv_apply (h : m.Coprime n)
    (χ : DirichletCharacter R m) (ψ : DirichletCharacter R n) :
    coprimeLevelEquiv h (χ, ψ) =
      changeLevel (dvd_mul_right m n) χ * changeLevel (dvd_mul_left n m) ψ := by
  -- The components of the Chinese remainder map are reduction to the two levels.
  have hcast (x : ZMod (m * n)) : ZMod.chineseRemainder h x =
      (ZMod.castHom (dvd_mul_right m n) _ x, ZMod.castHom (dvd_mul_left n m) _ x) :=
    DFunLike.congr_fun (RingHom.ext_zmod (ZMod.chineseRemainder h).toRingHom
      ((ZMod.castHom (dvd_mul_right m n) _).prod (ZMod.castHom (dvd_mul_left n m) _))) x
  apply MulChar.ext
  intro u
  rw [MulChar.mul_apply, changeLevel_apply_unitsMap, changeLevel_apply_unitsMap]
  simp [coprimeLevelEquiv, MulChar.coprodEquiv_apply, hcast, ZMod.unitsMap_val]

/-- The character behind `coprimeLevelEquiv` transported back to `ZMod m × ZMod n` is `χ`
composed with the inverse Chinese remainder map, including at nonunits, where both vanish. -/
private theorem equivToUnitHom_symm_comp_chineseRemainder_apply (h : m.Coprime n)
    (χ : DirichletCharacter R (m * n)) (x : ZMod m × ZMod n) :
    MulChar.equivToUnitHom.symm ((MulChar.equivToUnitHom χ).comp
      ↑(Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv.symm)) x =
      χ ((ZMod.chineseRemainder h).symm x) := by
  by_cases hx : IsUnit x
  · obtain ⟨w, rfl⟩ := hx
    rw [MulChar.equivToUnitHom_symm_coe]
    simp [MulChar.coe_equivToUnitHom]
  · rw [MulChar.map_nonunit _ hx, MulChar.map_nonunit]
    exact fun hy ↦ hx (by simpa using hy.map (ZMod.chineseRemainder h))

/-- The level-`m` factor of `χ` is `χ` read on the Chinese remainder lifts of `(x, 1)`. -/
@[simp]
theorem coprimeLevelEquiv_symm_apply_fst (h : m.Coprime n)
    (χ : DirichletCharacter R (m * n)) (x : ZMod m) :
    ((coprimeLevelEquiv h).symm χ).1 x = χ ((ZMod.chineseRemainder h).symm (x, 1)) := by
  simpa [coprimeLevelEquiv] using equivToUnitHom_symm_comp_chineseRemainder_apply h χ (x, 1)

/-- The level-`n` factor of `χ` is `χ` read on the Chinese remainder lifts of `(1, y)`. -/
@[simp]
theorem coprimeLevelEquiv_symm_apply_snd (h : m.Coprime n)
    (χ : DirichletCharacter R (m * n)) (y : ZMod n) :
    ((coprimeLevelEquiv h).symm χ).2 y = χ ((ZMod.chineseRemainder h).symm (1, y)) := by
  simpa [coprimeLevelEquiv] using equivToUnitHom_symm_comp_chineseRemainder_apply h χ (1, y)

/-- The conductor of a character modulo `m * n`, for coprime `m` and `n`, is the product of the
conductors of its two Chinese remainder factors. -/
theorem conductor_eq_mul_coprimeLevelEquiv_symm (χ : DirichletCharacter R (m * n))
    (h : m.Coprime n) :
    χ.conductor = ((coprimeLevelEquiv h).symm χ).1.conductor *
      ((coprimeLevelEquiv h).symm χ).2.conductor := by
  rcases eq_zero_or_neZero (m * n) with hzero | hlevel
  · rw [conductor_eq_zero_iff_level_eq_zero.mpr hzero]
    rcases mul_eq_zero.mp hzero with hm | hn
    · rw [conductor_eq_zero_iff_level_eq_zero.mpr hm, zero_mul]
    · rw [conductor_eq_zero_iff_level_eq_zero.mpr hn, mul_zero]
  let ψ := (coprimeLevelEquiv h).symm χ
  have hχ : χ = changeLevel (dvd_mul_right m n) ψ.1 * changeLevel (dvd_mul_left n m) ψ.2 :=
    ((coprimeLevelEquiv h).apply_symm_apply χ).symm.trans (coprimeLevelEquiv_apply h ψ.1 ψ.2)
  have hc : ψ.1.conductor.Coprime ψ.2.conductor :=
    (h.of_dvd_left ψ.1.conductor_dvd_level).of_dvd_right ψ.2.conductor_dvd_level
  have hlift : (changeLevel (dvd_mul_right m n) ψ.1).conductor.Coprime
      (changeLevel (dvd_mul_left n m) ψ.2).conductor := by
    simpa only [conductor_changeLevel] using hc
  calc
    χ.conductor =
        (changeLevel (dvd_mul_right m n) ψ.1 * changeLevel (dvd_mul_left n m) ψ.2).conductor :=
      congrArg conductor hχ
    _ = ψ.1.conductor * ψ.2.conductor := by
      simp only [conductor_mul_of_coprime hlift, conductor_changeLevel]

/-- A Dirichlet character modulo a product of coprime levels is primitive if and only if both
of its Chinese remainder factors are primitive. -/
theorem isPrimitive_iff_coprimeLevelEquiv_symm {χ : DirichletCharacter R (m * n)}
    (h : m.Coprime n) :
    χ.IsPrimitive ↔ ((coprimeLevelEquiv h).symm χ).1.IsPrimitive ∧
      ((coprimeLevelEquiv h).symm χ).2.IsPrimitive := by
  let ψ := (coprimeLevelEquiv h).symm χ
  simp only [isPrimitive_def, χ.conductor_eq_mul_coprimeLevelEquiv_symm h]
  have hm : ψ.1.conductor ∣ m := ψ.1.conductor_dvd_level
  have hn : ψ.2.conductor ∣ n := ψ.2.conductor_dvd_level
  refine ⟨fun heq ↦ ⟨Nat.dvd_antisymm hm ?_, Nat.dvd_antisymm hn ?_⟩, ?_⟩
  · apply (h.of_dvd_right hn).dvd_of_dvd_mul_right
    exact heq.symm ▸ dvd_mul_right m n
  · apply (h.symm.of_dvd_right hm).dvd_of_dvd_mul_left
    exact heq.symm ▸ dvd_mul_left n m
  · exact fun ⟨hm', hn'⟩ ↦ congrArg₂ (· * ·) hm' hn'

end DirichletCharacter
