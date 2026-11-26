/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Monomial
public import TauCeti.NumberTheory.ModularForms.ArithmeticSubgroups

/-!
# Split Cartan levels: examples

The split Cartan subgroup `C_s(ℓ)` of `GL₂(𝔽_ℓ)` is the diagonal torus and `C_s⁺(ℓ)` is the
monomial subgroup. Both contain `-1`, so their projective indices are their indices:
`[GL₂(𝔽₁₃) : ±C_s⁺(13)] = 91` and `[GL₂(𝔽₁₃) : ±C_s(13)] = 182`. At `ℓ = 2` the monomial
subgroup has order `2` and index `3`, while the normalizer of the (trivial) split Cartan
subgroup is all of `GL₂(𝔽₂)`, of order `6`. The determinant is surjective on `C_s(13)` and
`C_s⁺(13)`, and `C_s(13)` has index `2` in `C_s⁺(13)`.
-/

public section

open TauCeti

namespace TauCeti.MonomialGLExamples

instance : Fact (Nat.Prime 13) := ⟨by decide⟩

/-- `[GL₂(𝔽₁₃) : ±C_s⁺(13)] = 91`. -/
example : (monomialGL (ZMod 13) 2).projectiveIndex = 91 := by
  rw [Subgroup.projectiveIndex_eq_index neg_one_mem_monomialGL]
  have h := two_mul_index_monomialGL_two (ZMod 13)
  rw [Nat.card_zmod] at h
  omega

/-- `[GL₂(𝔽₁₃) : ±C_s(13)] = 182`. -/
example : (diagonalTorus (ZMod 13) 2).projectiveIndex = 182 := by
  rw [Subgroup.projectiveIndex_eq_index neg_one_mem_diagonalTorus, index_diagonalTorus_two,
    Nat.card_zmod]

/-- `C_s(13)` has index `2` in `C_s⁺(13)`. -/
example : (diagonalTorus (ZMod 13) 2).relIndex (monomialGL (ZMod 13) 2) = 2 :=
  relIndex_diagonalTorus_monomialGL (ZMod 13) 2

/-- At `ℓ = 2` the monomial subgroup has order `2`. -/
example : Nat.card (monomialGL (ZMod 2) 2) = 2 := by
  rw [natCard_monomialGL, Nat.card_zmod]
  rfl

/-- At `ℓ = 2` the monomial subgroup has index `3`. -/
example : (monomialGL (ZMod 2) 2).index = 3 := by
  have h := two_mul_index_monomialGL_two (ZMod 2)
  rw [Nat.card_zmod] at h
  omega

/-- At `ℓ = 2` the normalizer of the split Cartan subgroup is all of `GL₂(𝔽₂)`, which has order
`6`, so it is not the monomial subgroup. -/
example : Subgroup.normalizer (diagonalTorus (ZMod 2) 2 : Set (GL (Fin 2) (ZMod 2))) = ⊤ ∧
    Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
  -- `𝔽₂` has a single unit.
  have : Subsingleton (ZMod 2)ˣ :=
    ⟨fun a b ↦ Units.ext ((by decide : ∀ x y : ZMod 2, x ≠ 0 → y ≠ 0 → x = y) _ _
      a.ne_zero b.ne_zero)⟩
  refine ⟨?_, natCard_GL_fin_two_of_card_eq_two (Nat.card_zmod 2)⟩
  rw [diagonalTorus_eq_bot]
  exact Subgroup.normalizer_eq_top_iff.2 Subgroup.normal_bot

/-- The determinant is surjective on `C_s(13)` and on `C_s⁺(13)`. -/
example : (diagonalTorus (ZMod 13) 2).map Matrix.GeneralLinearGroup.det = ⊤ ∧
    (monomialGL (ZMod 13) 2).map Matrix.GeneralLinearGroup.det = ⊤ :=
  ⟨map_det_diagonalTorus, map_det_monomialGL⟩

end TauCeti.MonomialGLExamples
