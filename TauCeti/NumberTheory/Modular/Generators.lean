/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.NumberTheory.Modular.Relations

/-!
# The order-three generators of the modular group

Besides Mathlib's `S = (0 -1; 1 0)` and `T = (1 1; 0 1)`, the modular group has two standard
elliptic generators of order three in `PSL(2, ℤ)`:

* `R = S * T = (0 -1; 1 1)`, which fixes `ρ = e^{2πi/3}` and satisfies `R³ = -1` in `SL(2, ℤ)`;
* `U = S * T⁻¹ = (0 -1; 1 -1)`, which fixes `e^{πi/3}` and satisfies `U³ = 1` in `SL(2, ℤ)`.

In `PSL(2, ℤ)` the classes of `S`, `R` and `U` have orders `2`, `3` and `3`, while the class of `T`
has infinite order. The relation `T * S * U = -1` in `SL(2, ℤ)` makes the classes of `U`, `S`, `T`
a triple of elements of orders `3`, `2`, `∞` with product `T S U = 1`: they are the images of the
generators `x`, `y`, `z` of the triangle group `Δ(3, 2, ∞)` under the presentation of `PSL(2, ℤ)`
(`TauCeti.ModularGroup.modularEquiv`). Through the action of `PSL(2, ℤ)` on the cosets of a
finite-index subgroup they become the three permutations `σ0`, `σ1`, `σinf` of a permutation
triple.

The elements of `PSL(2, ℤ)` are written as coercions `(g : PSL(2, ℤ))` of elements of `SL(2, ℤ)`.
The product `T * S`, used as the order-three generator in
`TauCeti.NumberTheory.Modular.Relations`, is the conjugate `S⁻¹ R S` of `R`.

## Main declarations

* `TauCeti.ModularGroup.R`, `TauCeti.ModularGroup.U`: the elements `S * T` and `S * T⁻¹` of
  `SL(2, ℤ)`, with their matrices `coe_R` and `coe_U`.
* `TauCeti.ModularGroup.S_sq`, `TauCeti.ModularGroup.R_pow_three`,
  `TauCeti.ModularGroup.U_pow_three`, `TauCeti.ModularGroup.T_mul_S_mul_U`: the relations
  `S² = -1`, `R³ = -1`, `U³ = 1` and `T S U = -1` in `SL(2, ℤ)`.
* `TauCeti.ModularGroup.S_mul_R_inv_mul_S_inv`: `S R⁻¹ S⁻¹ = -U`, so that the two order-three
  generators agree up to sign and conjugation.
* `TauCeti.ModularGroup.coe_T_mul_coe_S_mul_coe_U`,
  `TauCeti.ModularGroup.coe_S_mul_coe_R_inv_mul_coe_S_inv`: `T S U = 1` and `S R⁻¹ S⁻¹ = U` in
  `PSL(2, ℤ)`.
* `TauCeti.ModularGroup.closure_coe_S_coe_T`: the classes of `S` and `T` generate `PSL(2, ℤ)`.
* `TauCeti.ModularGroup.orderOf_coe_S`, `TauCeti.ModularGroup.orderOf_coe_R`,
  `TauCeti.ModularGroup.orderOf_coe_U`, `TauCeti.ModularGroup.orderOf_coe_T`: the orders `2`,
  `3`, `3` and `0` (infinite order) in `PSL(2, ℤ)`.

## References

* Jean-Pierre Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973,
  Chapter VII, §1.
* Jean-Pierre Serre, *Trees*, Springer, 1980, Chapter I, §4.2.
-/

public section

open Matrix
open scoped MatrixGroups

namespace TauCeti.ModularGroup

open _root_.ModularGroup

/-- The elliptic element `R = S * T = (0 -1; 1 1)` of `SL(2, ℤ)`, of order `6`; it fixes
`ρ = e^{2πi/3}` and its class in `PSL(2, ℤ)` has order `3`. -/
def R : SL(2, ℤ) := S * T

/-- The elliptic element `U = S * T⁻¹ = (0 -1; 1 -1)` of `SL(2, ℤ)`, of order `3`; it fixes
`e^{πi/3}`. -/
def U : SL(2, ℤ) := S * T⁻¹

/-- The definition of `R` as `S * T`. -/
theorem R_def : R = S * T := (rfl)

/-- The definition of `U` as `S * T⁻¹`. -/
theorem U_def : U = S * T⁻¹ := (rfl)

/-- The matrix of `R = S * T`. -/
@[simp]
theorem coe_R : (R : Matrix (Fin 2) (Fin 2) ℤ) = !![0, -1; 1, 1] := by
  rw [R_def, SpecialLinearGroup.coe_mul, coe_S, coe_T]
  simp

/-- The matrix of `U = S * T⁻¹`. -/
@[simp]
theorem coe_U : (U : Matrix (Fin 2) (Fin 2) ℤ) = !![0, -1; 1, -1] := by
  rw [U_def, SpecialLinearGroup.coe_mul, coe_S, coe_T_inv]
  simp

/-- `S² = -1` in `SL(2, ℤ)`. -/
theorem S_sq : S ^ 2 = (-1 : SL(2, ℤ)) :=
  (sq S).trans (Subtype.ext S_mul_S_eq)

/-- `S` has order `4` in `SL(2, ℤ)`. -/
theorem S_pow_four : S ^ 4 = (1 : SL(2, ℤ)) := by
  rw [show 4 = 2 * 2 by rfl, pow_mul, S_sq, neg_one_sq]

/-- `R³ = -1` in `SL(2, ℤ)`. -/
theorem R_pow_three : R ^ 3 = (-1 : SL(2, ℤ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- `R` has order `6` in `SL(2, ℤ)`. -/
theorem R_pow_six : R ^ 6 = (1 : SL(2, ℤ)) := by
  rw [show 6 = 3 * 2 by rfl, pow_mul, R_pow_three, neg_one_sq]

/-- `U³ = 1` in `SL(2, ℤ)`, unlike `R³ = -1`. -/
theorem U_pow_three : U ^ 3 = (1 : SL(2, ℤ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- `T * S * U = -1` in `SL(2, ℤ)`. -/
theorem T_mul_S_mul_U : T * S * U = (-1 : SL(2, ℤ)) := by
  rw [U_def, mul_assoc, ← mul_assoc S, ← sq, S_sq, neg_one_mul, mul_neg, mul_inv_cancel]

/-- `S * R⁻¹ * S⁻¹ = -U` in `SL(2, ℤ)`: up to sign, `U` is conjugate to `R⁻¹`. -/
theorem S_mul_R_inv_mul_S_inv : S * R⁻¹ * S⁻¹ = -U := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- `R * U⁻¹ = S * T² * S⁻¹` in `SL(2, ℤ)`. -/
theorem R_mul_U_inv : R * U⁻¹ = S * T ^ 2 * S⁻¹ := by
  rw [R_def, U_def, _root_.mul_inv_rev, inv_inv, sq]
  simp only [mul_assoc]

/-- `R³ = 1` in `PSL(2, ℤ)`. -/
@[simp]
theorem coe_R_pow_three : (R : PSL(2, ℤ)) ^ 3 = 1 := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one, R_pow_three]
  exact Or.inr rfl

/-- `U³ = 1` in `PSL(2, ℤ)`. -/
@[simp]
theorem coe_U_pow_three : (U : PSL(2, ℤ)) ^ 3 = 1 := by
  rw [← QuotientGroup.mk_pow, U_pow_three, QuotientGroup.mk_one]

/-- `T * S * U = 1` in `PSL(2, ℤ)`. -/
@[simp]
theorem coe_T_mul_coe_S_mul_coe_U : (T : PSL(2, ℤ)) * S * U = 1 := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff,
    SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one, T_mul_S_mul_U]
  exact Or.inr rfl

/-- `S * R⁻¹ * S⁻¹ = U` in `PSL(2, ℤ)`: the classes of the two order-three generators are
conjugate up to inversion. -/
theorem coe_S_mul_coe_R_inv_mul_coe_S_inv :
    (S : PSL(2, ℤ)) * (R : PSL(2, ℤ))⁻¹ * (S : PSL(2, ℤ))⁻¹ = U := by
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul, S_mul_R_inv_mul_S_inv, QuotientGroup.eq,
    SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  decide

/-- The classes of `S` and `T` generate `PSL(2, ℤ)`. -/
theorem closure_coe_S_coe_T : Subgroup.closure {(S : PSL(2, ℤ)), (T : PSL(2, ℤ))} = ⊤ := by
  have h := congrArg (Subgroup.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))))
    SpecialLinearGroup.SL2Z_generators
  rwa [MonoidHom.map_closure, Set.image_pair,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h

/-- The class of `S` has order `2` in `PSL(2, ℤ)`. -/
@[simp]
theorem orderOf_coe_S : orderOf (S : PSL(2, ℤ)) = 2 := by
  refine orderOf_eq_prime coe_S_sq ?_
  rw [Ne, QuotientGroup.eq_one_iff, SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  decide

/-- The class of `R` has order `3` in `PSL(2, ℤ)`. -/
@[simp]
theorem orderOf_coe_R : orderOf (R : PSL(2, ℤ)) = 3 := by
  refine orderOf_eq_prime coe_R_pow_three ?_
  rw [Ne, QuotientGroup.eq_one_iff, SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  decide

/-- The class of `U` has order `3` in `PSL(2, ℤ)`. -/
@[simp]
theorem orderOf_coe_U : orderOf (U : PSL(2, ℤ)) = 3 := by
  refine orderOf_eq_prime coe_U_pow_three ?_
  rw [Ne, QuotientGroup.eq_one_iff, SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  decide

/-- The class of `T` has infinite order in `PSL(2, ℤ)`: no positive power of `T` is `±1`. -/
@[simp]
theorem orderOf_coe_T : orderOf (T : PSL(2, ℤ)) = 0 := by
  refine orderOf_eq_zero_iff'.2 fun n hn h ↦ ?_
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one] at h
  rcases h with h | h
  · have := congrArg (fun g : SL(2, ℤ) ↦ (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1) h
    simp [← zpow_natCast, coe_T_zpow] at this
    omega
  · have := congrArg (fun g : SL(2, ℤ) ↦ (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
    simp [← zpow_natCast, coe_T_zpow] at this

end TauCeti.ModularGroup
