/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.Cusps

/-!
# Modular-group action on cusps

The standard generators `S` and `T` of the modular group, and their product `T * S`, act on the
projective line `OnePoint K` over a field `K` by Möbius transformations. For `K = ℚ` these
evaluations describe the edges in the Manin-symbol relations.
-/

public section

open Matrix Matrix.GeneralLinearGroup Matrix.SpecialLinearGroup ModularGroup OnePoint
open scoped MatrixGroups

namespace TauCeti

variable {K : Type*} [Field K] [DecidableEq K]

/-- `S` sends `∞` to `0` under the Möbius action. -/
@[simp]
theorem mapGL_S_smul_infty : mapGL K S • (∞ : OnePoint K) = (0 : K) := by
  simp [smul_infty_eq_ite]

/-- `S` sends `0` to `∞` under the Möbius action. -/
@[simp]
theorem mapGL_S_smul_zero : mapGL K S • ((0 : K) : OnePoint K) = ∞ := by
  simp [smul_some_eq_ite]

/-- `T` fixes `∞` under the Möbius action. -/
@[simp]
theorem mapGL_T_smul_infty : mapGL K T • (∞ : OnePoint K) = ∞ := by
  simp [smul_infty_eq_ite]

/-- `T` translates an affine point by one. -/
@[simp]
theorem mapGL_T_smul_coe (k : K) :
    mapGL K T • (k : OnePoint K) = ((k + 1 : K) : OnePoint K) := by
  simp [smul_some_eq_ite]

/-- `T * S` sends `∞` to `1`. -/
@[simp]
theorem mapGL_T_mul_S_smul_infty :
    (mapGL K T * mapGL K S) • (∞ : OnePoint K) = (1 : K) := by
  simp [mul_smul]

/-- `T * S` sends `0` to `∞`. -/
@[simp]
theorem mapGL_T_mul_S_smul_zero :
    (mapGL K T * mapGL K S) • ((0 : K) : OnePoint K) = ∞ := by
  simp [mul_smul]

/-- `T * S` sends `1` to `0`. -/
@[simp]
theorem mapGL_T_mul_S_smul_one :
    (mapGL K T * mapGL K S) • ((1 : K) : OnePoint K) = (0 : K) := by
  simp [mul_smul, smul_some_eq_ite]

/-- `(T * S)²` sends `∞` to `0`. -/
@[simp]
theorem mapGL_T_mul_S_sq_smul_infty :
    (mapGL K T * mapGL K S) ^ 2 • (∞ : OnePoint K) = (0 : K) := by
  rw [pow_two, mul_smul, mapGL_T_mul_S_smul_infty, mapGL_T_mul_S_smul_one]

/-- `(T * S)²` sends `0` to `1`. -/
@[simp]
theorem mapGL_T_mul_S_sq_smul_zero :
    (mapGL K T * mapGL K S) ^ 2 • ((0 : K) : OnePoint K) = (1 : K) := by
  rw [pow_two, mul_smul, mapGL_T_mul_S_smul_zero, mapGL_T_mul_S_smul_infty]

end TauCeti
