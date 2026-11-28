/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Reflections compatible with a Hermitian matrix

Given a Hermitian matrix `H : Matrix n n R` and a vector `u : n → R`, the reflection associated to
`H` and `u` is `Matrix.formReflection H u`, sending `w` to
`(2 * (star u ⬝ᵥ H *ᵥ w) / (star u ⬝ᵥ H *ᵥ u)) • u - w`. Whenever `star u ⬝ᵥ H *ᵥ u ≠ 0`, it fixes
`u` and negates the `H`-orthogonal complement of `u`.

Conversely, if `J = vecMulVec u w - 1` is any reflection fixing `u` (meaning `w ⬝ᵥ u = 2`) such
that `H * J` is Hermitian and `star u ⬝ᵥ H *ᵥ u ≠ 0`, then `w` is uniquely determined as
`(2 / (star u ⬝ᵥ H *ᵥ u)) • (star u ᵥ* H)` (`Matrix.eq_smul_vecMul_of_isHermitian_mul_sub_one`).
When `H * J` is positive definite and `(2 : R) ≠ 0`, positivity at `u` automatically yields
`0 < star u ⬝ᵥ H *ᵥ u` and identifies `J` with `Matrix.formReflection H u`
(`Matrix.pos_and_eq_formReflection_of_posDef`).

## Main definitions and results

* `Matrix.formReflection`: the reflection
  `vecMulVec u ((2 / (star u ⬝ᵥ H *ᵥ u)) • (star u ᵥ* H)) - 1`.
* `Matrix.eq_smul_vecMul_of_isHermitian_mul_sub_one`: a reflection `vecMulVec u w - 1` with
  `H * (vecMulVec u w - 1)` Hermitian and `star u ⬝ᵥ H *ᵥ u ≠ 0` has `w` determined by `H` and `u`.
* `Matrix.pos_and_eq_formReflection_of_posDef`: if `H` is Hermitian and `H * (vecMulVec u w - 1)`
  is positive definite, then `0 < star u ⬝ᵥ H *ᵥ u` and `vecMulVec u w - 1 = formReflection H u`.

## Provenance

Generalized from `grh-lean` (https://github.com/lsernau/grh-lean at commit
72fead102f663d5c7a407964a13dc0cf9d977207, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Shimura/Uniformisation/BallModel.lean` (`formReflection`, `exists_eq_formReflection`).
-/

public section

namespace Matrix

universe u v

/-- The reflection associated to a matrix `H` and vector `u`:
`w ↦ (2 * (star u ⬝ᵥ H *ᵥ w) / (star u ⬝ᵥ H *ᵥ u)) • u - w`. When `star u ⬝ᵥ H *ᵥ u ≠ 0`, it
fixes `u` and negates the `H`-orthogonal complement of `u`. -/
noncomputable def formReflection {n : Type u} {R : Type v} [Fintype n] [DecidableEq n]
    [Field R] [StarRing R] (H : Matrix n n R) (u : n → R) : Matrix n n R :=
  vecMulVec u ((2 / (star u ⬝ᵥ H *ᵥ u)) • (star u ᵥ* H)) - 1

/-- If `H` is Hermitian, `w ⬝ᵥ u = 2`, `H * (vecMulVec u w - 1)` is Hermitian, and
`star u ⬝ᵥ H *ᵥ u ≠ 0`, then `w = (2 / (star u ⬝ᵥ H *ᵥ u)) • (star u ᵥ* H)`. -/
theorem eq_smul_vecMul_of_isHermitian_mul_sub_one {n : Type u} {R : Type v}
    [Fintype n] [DecidableEq n] [Field R] [StarRing R] {H : Matrix n n R} (hH : H.IsHermitian)
    {u w : n → R} (hwu : w ⬝ᵥ u = 2) (hHJ : (H * (vecMulVec u w - 1)).IsHermitian)
    (hu : star u ⬝ᵥ H *ᵥ u ≠ 0) :
    w = (2 / (star u ⬝ᵥ H *ᵥ u)) • (star u ᵥ* H) := by
  have h_fix : (vecMulVec u w - 1) *ᵥ u = u := by
    simp [hwu, two_smul, sub_mulVec, vecMulVec_mulVec]
  have h_symm (x : n → R) :
      (w ⬝ᵥ x) * (star u ⬝ᵥ H *ᵥ u) - star u ⬝ᵥ H *ᵥ x = star u ⬝ᵥ H *ᵥ x := by
    have h1 := congrArg star (hHJ.star_dotProduct_mulVec_comm u x)
    have h2 : star x ⬝ᵥ (H * (vecMulVec u w - 1)) *ᵥ u = star x ⬝ᵥ H *ᵥ u := by
      rw [← mulVec_mulVec, h_fix]
    rw [star_star, h2, hH.star_dotProduct_mulVec_comm x u] at h1
    simpa only [← mulVec_mulVec, sub_mulVec, vecMulVec_mulVec, one_mulVec, mulVec_sub, mulVec_smul,
      dotProduct_sub, dotProduct_smul, op_smul_eq_mul, mul_comm (star u ⬝ᵥ H *ᵥ u)] using h1
  refine dotProduct_eq _ _ fun x ↦ ?_
  have h2 : (w ⬝ᵥ x) * (star u ⬝ᵥ H *ᵥ u) = 2 * (star u ⬝ᵥ H *ᵥ x) := by
    rw [two_mul, ← sub_eq_iff_eq_add.mp (h_symm x)]
  rw [smul_dotProduct, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hu, ← dotProduct_mulVec]
  exact h2

/-- If `H` is Hermitian, `w ⬝ᵥ u = 2`, and `H * (vecMulVec u w - 1)` is positive definite over a
partially ordered star field with `2 ≠ 0`, then `0 < star u ⬝ᵥ H *ᵥ u` and
`vecMulVec u w - 1 = formReflection H u`. -/
theorem pos_and_eq_formReflection_of_posDef {n : Type u} {R : Type v}
    [Fintype n] [DecidableEq n] [Field R] [PartialOrder R] [StarRing R] [NeZero (2 : R)]
    {H : Matrix n n R} (hH : H.IsHermitian) {u w : n → R} (hwu : w ⬝ᵥ u = 2)
    (hHJ : (H * (vecMulVec u w - 1)).PosDef) :
    0 < star u ⬝ᵥ H *ᵥ u ∧ vecMulVec u w - 1 = formReflection H u := by
  have h_fix : (vecMulVec u w - 1) *ᵥ u = u := by
    simp [hwu, two_smul, sub_mulVec, vecMulVec_mulVec]
  have h_u_ne : u ≠ 0 := by
    rintro rfl
    simp [NeZero.ne' (2 : R)] at hwu
  have h_pos : 0 < star u ⬝ᵥ H *ᵥ u := by
    simpa only [← mulVec_mulVec, h_fix] using hHJ.dotProduct_mulVec_pos h_u_ne
  have h_w := eq_smul_vecMul_of_isHermitian_mul_sub_one hH hwu hHJ.isHermitian h_pos.ne'
  exact ⟨h_pos, by rw [h_w, formReflection]⟩

end Matrix
