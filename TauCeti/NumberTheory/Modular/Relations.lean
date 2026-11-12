/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup

/-!
# Relations among the generators of `PSL(2, ℤ)`

In `PSL(2, ℤ)` the classes of `S = (0 -1; 1 0)` and `U = T * S = (1 -1; 1 0)`, where
`T = (1 1; 0 1)`, satisfy `S² = 1` and `U³ = 1`, and `U * S = T`. In `SL(2, ℤ)` the first two
products are `-1` and the last is `-T`, so each relation is proved by checking that the
corresponding element of `SL(2, ℤ)` is `±1`, that is, central. Likewise `U² * S` is the class of
the lower-triangular matrix `T′ = (1 0; 1 1)`. The classes of `S` and `U` generate `PSL(2, ℤ)`,
and hence also its opposite group.

`U` is written `(T : PSL(2, ℤ)) * S`, the simp-normal form of the class of `T * S`.

## Main results

* `TauCeti.ModularGroup.T_mul_S_pow_three`: `(T * S)³ = -1` in `SL(2, ℤ)`.
* `TauCeti.ModularGroup.coe_S_sq`, `TauCeti.ModularGroup.coe_S_inv`: `S² = 1` and `S⁻¹ = S`.
* `TauCeti.ModularGroup.coe_T_mul_coe_S_pow_three`, `TauCeti.ModularGroup.coe_T_mul_coe_S_inv`,
  `TauCeti.ModularGroup.coe_T_mul_coe_S_sq_inv`: `U³ = 1`, `U⁻¹ = U²` and `(U²)⁻¹ = U`.
* `Matrix.ProjectiveSpecialLinearGroup.mul_coe_S_mul_coe_S`: `g * S * S = g`, the product form of
  `S² = 1`; in particular `U * S = T`.
* `TauCeti.ModularGroup.closure_coe_S_coe_T_mul_coe_S`,
  `TauCeti.ModularGroup.closure_op_coe_S_op_coe_T_mul_coe_S`: `S` and `U` generate `PSL(2, ℤ)`
  and, as right multipliers, `PSL(2, ℤ)ᵐᵒᵖ`.
* `TauCeti.ModularGroup.tPrime`, `TauCeti.ModularGroup.coe_tPrime`,
  `TauCeti.ModularGroup.coe_T_mul_coe_S_sq_mul_coe_S`: the matrix `T′ = (1 0; 1 1)` and
  `U² * S = T′`.
-/

public section

open Matrix
open scoped MatrixGroups

namespace TauCeti.ModularGroup

open _root_.ModularGroup

/-- `U³ = -1` in `SL(2, ℤ)`, for `U = T * S`. -/
theorem T_mul_S_pow_three : (T * S) ^ 3 = (-1 : SL(2, ℤ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The class of `S` has order dividing `2` in `PSL(2, ℤ)`: in `SL(2, ℤ)`, `S² = -1`. -/
@[simp]
theorem coe_S_sq : (S : PSL(2, ℤ)) ^ 2 = 1 := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  exact Or.inr (by decide +kernel)

/-- The projective involution `S` has exact order two. -/
@[simp]
theorem orderOf_coe_S : orderOf (S : PSL(2, ℤ)) = 2 := by
  apply orderOf_eq_prime coe_S_sq
  rw [ne_eq, QuotientGroup.eq_one_iff,
    SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  decide

/-- A projective translation is the identity exactly when its integer exponent is zero. -/
@[simp]
theorem coe_T_zpow_eq_one_iff (n : ℤ) : (T : PSL(2, ℤ)) ^ n = 1 ↔ n = 0 := by
  constructor
  · intro h
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff,
      SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one] at h
    rcases h with h | h <;>
      simpa [coe_T_zpow] using congrArg (fun g : SL(2, ℤ) ↦ g 0 1) h
  · rintro rfl
    simp

/-- The projective cusp translation has infinite order, encoded by `orderOf = 0`. -/
@[simp]
theorem orderOf_coe_T : orderOf (T : PSL(2, ℤ)) = 0 := by
  apply orderOf_eq_zero_iff'.mpr
  intro n hn h
  have hz : (T : PSL(2, ℤ)) ^ (n : ℤ) = 1 := by simpa using h
  exact (Nat.ne_of_gt hn) (Int.natCast_eq_zero.mp ((coe_T_zpow_eq_one_iff _).mp hz))

/-- The standard classes of `S` and `T` generate the projective modular group. -/
theorem closure_coe_S_coe_T : Subgroup.closure {(S : PSL(2, ℤ)), (T : PSL(2, ℤ))} = ⊤ := by
  have h := congrArg (Subgroup.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))))
    _root_.SpecialLinearGroup.SL2Z_generators
  rwa [MonoidHom.map_closure, Set.image_pair,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h

/-- The class of `S` is its own inverse in `PSL(2, ℤ)`. -/
@[simp]
theorem coe_S_inv : (S : PSL(2, ℤ))⁻¹ = S :=
  inv_eq_of_mul_eq_one_right (by rw [← sq, coe_S_sq])

/-- The class of `U = T * S` has order dividing `3` in `PSL(2, ℤ)`: in `SL(2, ℤ)`,
`(T * S)³ = -1`. -/
@[simp]
theorem coe_T_mul_coe_S_pow_three : ((T : PSL(2, ℤ)) * S) ^ 3 = 1 := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  exact Or.inr (by decide +kernel)

/-- The inverse of the class of `U = T * S` in `PSL(2, ℤ)` is `U²`. -/
theorem coe_T_mul_coe_S_inv : ((T : PSL(2, ℤ)) * S)⁻¹ = ((T : PSL(2, ℤ)) * S) ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ', coe_T_mul_coe_S_pow_three])

/-- The inverse of `U²`, for `U = T * S` in `PSL(2, ℤ)`, is `U`. -/
@[simp]
theorem coe_T_mul_coe_S_sq_inv : (((T : PSL(2, ℤ)) * S) ^ 2)⁻¹ = (T : PSL(2, ℤ)) * S := by
  rw [← coe_T_mul_coe_S_inv, inv_inv]

/-- The classes of `S` and `U = T * S` generate `PSL(2, ℤ)`. -/
theorem closure_coe_S_coe_T_mul_coe_S :
    Subgroup.closure {(S : PSL(2, ℤ)), (T : PSL(2, ℤ)) * S} = ⊤ := by
  have h := congrArg (Subgroup.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))))
    TauCeti.Matrix.SpecialLinearGroup.closure_S_T_mul_S
  rwa [MonoidHom.map_closure, Set.image_pair,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h

/-- The classes of `S` and `U = T * S` generate `PSL(2, ℤ)ᵐᵒᵖ`, the group acting on the right. -/
theorem closure_op_coe_S_op_coe_T_mul_coe_S :
    Subgroup.closure {MulOpposite.op (S : PSL(2, ℤ)), .op ((T : PSL(2, ℤ)) * S)} = ⊤ := by
  have hop := congrArg Subgroup.op closure_coe_S_coe_T_mul_coe_S
  rw [Subgroup.op_closure, Subgroup.op_top] at hop
  convert hop using 2
  ext g
  obtain ⟨g, rfl⟩ := MulOpposite.op_surjective g
  simp [-MulOpposite.op_mul]

/-- Right multiplication by `S` is an involution of `PSL(2, ℤ)`. -/
@[simp]
theorem _root_.Matrix.ProjectiveSpecialLinearGroup.mul_coe_S_mul_coe_S (g : PSL(2, ℤ)) :
    g * S * S = g := by
  rw [mul_assoc, ← sq, coe_S_sq, mul_one]

/-- Popa and Zagier's `T′ = (1 0; 1 1)`, the lower-triangular counterpart of `T`. -/
def tPrime : SL(2, ℤ) := ⟨!![1, 0; 1, 1], by decide +kernel⟩

/-- The matrix of `T′`. -/
@[simp]
theorem coe_tPrime : (tPrime : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 1, 1] :=
  (rfl)

/-- In `PSL(2, ℤ)`, `U² * S = T′` for `U = T * S`; in `SL(2, ℤ)` the product is `-T′`. -/
@[simp]
theorem coe_T_mul_coe_S_sq_mul_coe_S : ((T : PSL(2, ℤ)) * S) ^ 2 * S = (tPrime : PSL(2, ℤ)) := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul, QuotientGroup.eq,
    SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  exact Or.inr (by decide +kernel)

end TauCeti.ModularGroup
