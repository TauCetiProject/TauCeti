/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Relations among the generators of `PSL(2, ℤ)`

In `PSL(2, ℤ)` the classes of `S = (0 -1; 1 0)` and `U = T * S = (1 -1; 1 0)`, where
`T = (1 1; 0 1)`, satisfy `S² = 1` and `U³ = 1`, and `U * S = T`. In `SL(2, ℤ)` the first two
products are `-1` and the last is `-T`, so each relation is proved by checking that the
corresponding element of `SL(2, ℤ)` is `±1`, that is, central. Likewise `U² * S` is the class of
the lower-triangular matrix `T′ = (1 0; 1 1)`.

`U` is written `(T : PSL(2, ℤ)) * S`, the simp-normal form of the class of `T * S`.

## Main results

* `TauCeti.ModularGroup.coe_S_sq`, `TauCeti.ModularGroup.coe_S_inv`: `S² = 1` and `S⁻¹ = S`.
* `TauCeti.ModularGroup.coe_T_mul_coe_S_pow_three`, `TauCeti.ModularGroup.coe_T_mul_coe_S_inv`,
  `TauCeti.ModularGroup.coe_T_mul_coe_S_sq_inv`: `U³ = 1`, `U⁻¹ = U²` and `(U²)⁻¹ = U`.
* `TauCeti.ModularGroup.coe_S_mul_coe_S`, `TauCeti.ModularGroup.mul_coe_S_mul_coe_S`: `S * S = 1`
  and `g * S * S = g`, the product forms of `S² = 1`; in particular `U * S = T`.
* `TauCeti.ModularGroup.tPrime`, `TauCeti.ModularGroup.coe_tPrime`,
  `TauCeti.ModularGroup.coe_T_mul_coe_S_sq_mul_coe_S`: the matrix `T′ = (1 0; 1 1)` and
  `U² * S = T′`.
-/

public section

open Matrix
open scoped MatrixGroups

namespace TauCeti.ModularGroup

open _root_.ModularGroup

/-- The class of `S` has order dividing `2` in `PSL(2, ℤ)`: in `SL(2, ℤ)`, `S² = -1`. -/
@[simp]
theorem coe_S_sq : (S : PSL(2, ℤ)) ^ 2 = 1 := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  exact Or.inr (by decide +kernel)

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

/-- The product form of `S² = 1` in `PSL(2, ℤ)`. -/
@[simp]
theorem coe_S_mul_coe_S : (S : PSL(2, ℤ)) * S = 1 := by
  rw [← sq, coe_S_sq]

/-- Right multiplication by `S` is an involution of `PSL(2, ℤ)`. -/
@[simp]
theorem mul_coe_S_mul_coe_S (g : PSL(2, ℤ)) : g * S * S = g := by
  rw [mul_assoc, coe_S_mul_coe_S, mul_one]

/-- Popa and Zagier's `T′ = (1 0; 1 1)`, the lower-triangular counterpart of `T`. -/
@[expose] def tPrime : SL(2, ℤ) := ⟨!![1, 0; 1, 1], by decide +kernel⟩

/-- The matrix of `T′`. -/
@[simp]
theorem coe_tPrime : (tPrime : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 1, 1] :=
  rfl

/-- In `PSL(2, ℤ)`, `U² * S = T′` for `U = T * S`; in `SL(2, ℤ)` the product is `-T′`. -/
@[simp]
theorem coe_T_mul_coe_S_sq_mul_coe_S : ((T : PSL(2, ℤ)) * S) ^ 2 * S = (tPrime : PSL(2, ℤ)) := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul, QuotientGroup.eq,
    SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  exact Or.inr (by decide +kernel)

end TauCeti.ModularGroup
