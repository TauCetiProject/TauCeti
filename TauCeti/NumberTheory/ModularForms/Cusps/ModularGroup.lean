/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.Cusps

/-!
# Modular-group action on rational cusps

The standard generators `S` and `T`, and their product `T * S`, act on rational cusps by
Möbius transformations. These evaluations describe the edges in the Manin-symbol relations.
-/

public section

open Matrix.SpecialLinearGroup ModularGroup OnePoint
open scoped MatrixGroups

namespace TauCeti

/-- `S` sends `∞` to `0` under the Möbius action. -/
@[simp]
theorem mapGL_S_smul_infty : mapGL ℚ S • (∞ : OnePoint ℚ) = (0 : ℚ) := by
  simp [OnePoint.smul_infty_eq_ite]

/-- `S` sends `0` to `∞` under the Möbius action. -/
@[simp]
theorem mapGL_S_smul_zero : mapGL ℚ S • ((0 : ℚ) : OnePoint ℚ) = ∞ := by
  simp [OnePoint.smul_some_eq_ite]

/-- `T` fixes `∞` under the Möbius action. -/
@[simp]
theorem mapGL_T_smul_infty : mapGL ℚ T • (∞ : OnePoint ℚ) = ∞ := by
  simp [OnePoint.smul_infty_eq_ite]

/-- `T` translates an affine cusp by one. -/
@[simp]
theorem mapGL_T_smul_coe (k : ℚ) :
    mapGL ℚ T • (k : OnePoint ℚ) = ((k + 1 : ℚ) : OnePoint ℚ) := by
  simp [OnePoint.smul_some_eq_ite]

/-- `T * S` sends `∞` to `1`. -/
@[simp]
theorem mapGL_T_mul_S_smul_infty :
    (mapGL ℚ T * mapGL ℚ S) • (∞ : OnePoint ℚ) = (1 : ℚ) := by
  rw [mul_smul, mapGL_S_smul_infty, mapGL_T_smul_coe]
  norm_num

/-- `T * S` sends `0` to `∞`. -/
@[simp]
theorem mapGL_T_mul_S_smul_zero :
    (mapGL ℚ T * mapGL ℚ S) • ((0 : ℚ) : OnePoint ℚ) = ∞ := by
  rw [mul_smul, mapGL_S_smul_zero, mapGL_T_smul_infty]

/-- `T * S` sends `1` to `0`. -/
@[simp]
theorem mapGL_T_mul_S_smul_one :
    (mapGL ℚ T * mapGL ℚ S) • ((1 : ℚ) : OnePoint ℚ) = (0 : ℚ) := by
  rw [mul_smul]
  simp [OnePoint.smul_some_eq_ite]

/-- `(T * S)²` sends `∞` to `0`. -/
@[simp]
theorem mapGL_T_mul_S_sq_smul_infty :
    (mapGL ℚ T * mapGL ℚ S) ^ 2 • (∞ : OnePoint ℚ) = (0 : ℚ) := by
  rw [pow_two, mul_smul, mapGL_T_mul_S_smul_infty, mapGL_T_mul_S_smul_one]

/-- `(T * S)²` sends `0` to `1`. -/
@[simp]
theorem mapGL_T_mul_S_sq_smul_zero :
    (mapGL ℚ T * mapGL ℚ S) ^ 2 • ((0 : ℚ) : OnePoint ℚ) = (1 : ℚ) := by
  rw [pow_two, mul_smul, mapGL_T_mul_S_smul_zero, mapGL_T_mul_S_smul_infty]

end TauCeti
