/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.MulChar.Prod

/-!
# Dirichlet characters at a product of coprime levels

At coprime levels `m` and `n`, lifting and multiplying identifies pairs of Dirichlet
characters with characters of level `m * n`. This is `MulChar.coprodEquiv` transported
along the Chinese remainder isomorphism `ZMod.chineseRemainder`.
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

end DirichletCharacter
