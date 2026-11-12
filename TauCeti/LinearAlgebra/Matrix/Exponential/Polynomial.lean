/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Nilpotent.Exp
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.Polynomial.Coeff

/-!
# Coefficients of a polynomial matrix exponential

For a nilpotent matrix `M`, the coefficient of degree `m` in `exp(tM)` is `Mᵐ / m!`.
In particular, the curve has velocity `M` at zero.
This entrywise coefficient calculation uses the finite exponential `IsNilpotent.exp` and
works over every commutative ring with a rational module structure, including nonreduced rings.
-/

public section

open scoped Polynomial

/-- The coefficient of `tᵐ` in the polynomial exponential `exp(tX)` is `Xᵐ / m!`. -/
theorem Matrix.coeff_exp_X_smul_C_mapMatrix
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [Module ℚ R]
    {X : Matrix ι ι R} (hX : IsNilpotent X) (m : ℕ) (i j : ι) :
    (IsNilpotent.exp ((Polynomial.X : R[X]) • Polynomial.C.mapMatrix X) i j).coeff m =
      ((m.factorial : ℚ)⁻¹ • X ^ m) i j := by
  obtain ⟨k, hk⟩ := hX
  have hk' : ((Polynomial.X : R[X]) • Polynomial.C.mapMatrix X) ^ (k + (m + 1)) = 0 := by
    rw [smul_pow, ← map_pow, pow_add X, hk, zero_mul, map_zero, smul_zero]
  rw [IsNilpotent.exp_eq_sum hk', Matrix.sum_apply, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single_of_mem m (Finset.mem_range.mpr (by omega)) fun l _ hl ↦ ?_] <;>
    rw [smul_pow, ← map_pow, Matrix.smul_apply, Matrix.smul_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, smul_eq_mul, Polynomial.coeff_smul, Polynomial.coeff_X_pow_mul']
  · simp
  · split_ifs with h
    · rw [Polynomial.coeff_C_of_ne_zero (by omega), smul_zero]
    · exact smul_zero _

/-- The linear coefficient of the polynomial exponential `exp(tX)` is `X`. -/
theorem Matrix.coeff_one_exp_X_smul_C_mapMatrix
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [Module ℚ R]
    {X : Matrix ι ι R} (hX : IsNilpotent X) (i j : ι) :
    (IsNilpotent.exp ((Polynomial.X : R[X]) • Polynomial.C.mapMatrix X) i j).coeff 1 =
      X i j := by
  rw [Matrix.coeff_exp_X_smul_C_mapMatrix hX, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
    pow_one]
