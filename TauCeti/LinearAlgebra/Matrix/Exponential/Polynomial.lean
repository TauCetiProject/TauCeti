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
# Linear coefficient of a polynomial matrix exponential

For a nilpotent matrix `M`, the polynomial curve `exp(tM)` has velocity `M` at zero.
This entrywise coefficient calculation uses the finite exponential `IsNilpotent.exp` and
works over every commutative rational algebra, including nonreduced ones.
-/

public section

namespace Matrix

open Polynomial

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [Module ℚ R]

/-- The linear coefficient of `exp(tM)` is `M`. -/
@[simp]
theorem coeff_one_exp_X_smul_map_C {M : Matrix ι ι R} (hM : IsNilpotent M) (i j : ι) :
    (IsNilpotent.exp ((X : R[X]) • M.map C) i j).coeff 1 = M i j := by
  classical
  -- Bundle the entrywise coefficient map so its homomorphism laws can transport matrix powers.
  change (IsNilpotent.exp ((X : R[X]) • C.mapMatrix M) i j).coeff 1 = M i j
  obtain ⟨n, hn⟩ := hM
  have hn' : ((X : R[X]) • C.mapMatrix M) ^ (n + 2) = 0 := by
    rw [smul_pow, ← map_pow, pow_eq_zero_of_le (by omega) hn, map_zero, smul_zero]
  rw [IsNilpotent.exp_eq_sum hn']
  simp only [Matrix.sum_apply, Matrix.smul_apply, finsetSum_coeff]
  have hterm (k : ℕ) :
      (((k.factorial : ℚ)⁻¹ • (((X : R[X]) • C.mapMatrix M) ^ k)) i j).coeff 1 =
        if k = 1 then M i j else 0 := by
    rw [smul_pow, ← map_pow]
    simp only [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
    -- Entrywise matrix scalar actions reduce to polynomial multiplication, while the
    -- outer scalar remains rational; state those actions explicitly before extracting coefficients.
    change (((k.factorial : ℚ)⁻¹ • (X ^ k * C ((M ^ k) i j)) : R[X])).coeff 1 = _
    calc
      _ = (k.factorial : ℚ)⁻¹ • ((X ^ k * C ((M ^ k) i j) : R[X]).coeff 1) :=
        map_rat_smul (lcoeff R 1).toAddMonoidHom _ _
      _ = _ := by
        by_cases hk : k = 1
        · simp [hk]
        · simp [coeff_X_pow, hk, Ne.symm hk]
  simp only [Matrix.smul_apply] at hterm
  simp_rw [hterm]
  simp

end Matrix
