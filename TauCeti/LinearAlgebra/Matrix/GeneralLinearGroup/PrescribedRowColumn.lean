/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Matrix.OneSubVecMulVec

/-!
# Invertible matrices with a prescribed row and column

Over a commutative ring `R`, let `u` and `v` be vectors of `n → R` with the same entry `c` at an
index `i`, and suppose that `c` is a unit. Then some invertible matrix has `u` as its column `i`
and `v` as its row `i`. Writing `e` for the `i`-th standard basis vector, `u₀ = u - c e` and
`v₀ = v - c e`, it is the product

  `(1 + c⁻¹ u₀ eᵀ) · diag(1, …, c, …, 1) · (1 + c⁻¹ e v₀ᵀ)`

of three invertible rank-one perturbations of the identity
(`TauCeti.oneSubVecMulVecGL`); with the index `i` placed last it is the block matrix
`[[1 + c⁻¹ u₀ v₀ᵀ, u₀], [v₀ᵀ, c]]`. The hypothesis that `c` is a unit cannot be dropped: an
invertible matrix whose row `i` is `c eᵀ` has `c` as a factor of its determinant.

## Main results

* `TauCeti.exists_col_eq_and_row_eq_of_isUnit`: a column `u` and a row `v` through a common unit
  entry are the column and the row of an invertible matrix.
-/

public section

open Matrix

namespace TauCeti

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- A row vector times a rank-one perturbation of the identity: `w (1 - u vᵀ) = w - (w ⬝ᵥ u) v`. -/
private theorem vecMul_one_sub_vecMulVec (u v w : n → R) :
    w ᵥ* (1 - vecMulVec u v) = w - (w ⬝ᵥ u) • v := by
  rw [vecMul_sub, vecMul_one, vecMul_vecMulVec]

/-- **Completing a row and a column through a unit.** If `u` and `v` have the same entry at `i`
and that entry is a unit, some invertible matrix has `u` as its column `i` and `v` as its row
`i`. -/
theorem exists_col_eq_and_row_eq_of_isUnit {u v : n → R} {i : n} (huv : u i = v i)
    (hu : IsUnit (u i)) :
    ∃ g : GL n R, (g : Matrix n n R).col i = u ∧ (g : Matrix n n R).row i = v := by
  obtain ⟨c, hc⟩ := hu
  set e : n → R := Pi.single i 1 with he
  have hee : e ⬝ᵥ e = 1 := by simp [he]
  -- the three factors `1 + c⁻¹ u₀ eᵀ`, `1 - (1 - c) e eᵀ` and `1 + c⁻¹ e v₀ᵀ`
  set a : n → R := -((c⁻¹ : Rˣ) : R) • (u - (c : R) • e) with ha
  set b : n → R := -((c⁻¹ : Rˣ) : R) • (v - (c : R) • e) with hb
  have hea : e ⬝ᵥ a = 0 := by simp [ha, he, hc]
  have hbe : b ⬝ᵥ e = 0 := by simp [hb, he, hc, huv]
  let X := oneSubVecMulVecGL (-1) a e (by rw [hea]; simp)
  let Z := oneSubVecMulVecGL (-c) ((1 - (c : R)) • e) e (by
    rw [dotProduct_smul, hee]; simp [add_comm, sub_eq_add_neg])
  let Y := oneSubVecMulVecGL (-1) e b (by rw [hbe]; simp)
  have hcinv : (c : R) * ((c⁻¹ : Rˣ) : R) = 1 := c.mul_inv
  refine ⟨X * Z * Y, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, ← mulVec_single_one, ← he, ← mulVec_mulVec,
      ← mulVec_mulVec]
    simp only [X, Y, Z, coe_oneSubVecMulVecGL, one_sub_vecMulVec_mulVec, hbe, hee, zero_smul,
      sub_zero, one_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul, mul_one]
    rw [ha]
    ext j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (u j - c * e j) * hcinv
  · rw [Units.val_mul, Units.val_mul, ← single_one_vecMul, ← he, ← vecMul_vecMul,
      ← vecMul_vecMul]
    simp only [X, Y, Z, coe_oneSubVecMulVecGL, vecMul_one_sub_vecMulVec, hea, zero_smul,
      sub_zero, dotProduct_smul, sub_dotProduct, smul_dotProduct, hee, smul_eq_mul, mul_one]
    rw [hb]
    ext j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (v j - c * e j) * hcinv

end TauCeti
