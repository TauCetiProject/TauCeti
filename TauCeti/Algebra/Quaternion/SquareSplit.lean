/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuaternionBasis
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Quaternion symbols with a square parameter

This file constructs the explicit splitting of a quaternion symbol one of whose parameters is
a square, starting with the second parameter. For units `a` and `b` over a commutative ring in
which two is invertible, the equivalence

```text
QuaternionAlgebra R a 0 b² ≃ₐ[R] Matrix (Fin 2) (Fin 2) R
```

sends its standard generators to

```text
i ↦ !![0, a; 1, 0],   j ↦ !![b, 0; 0, -b].
```

The formulas for the equivalence and its inverse are recorded entrywise, so later symbol
relations can use the splitting without unfolding the quaternion-basis implementation.

## Main definitions

* `TauCeti.QuaternionAlgebra.secondSquareEquivMatrix`: the equivalence from the quaternion
  symbol `(a,b²)` to `Matrix (Fin 2) (Fin 2) R` for units `a` and `b`.
* `TauCeti.QuaternionAlgebra.firstSquareEquivMatrix`: the same for the symbol `(a²,b)`,
  obtained by exchanging the two generators.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter III, Section 2.11.
-/

public section

open scoped Matrix Quaternion

namespace TauCeti

namespace QuaternionAlgebra

variable {R : Type*} [CommRing R]

private def secondSquareMatrixBasis (a b : R) :
    _root_.QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) R) a 0 (b ^ 2) where
  i := !![0, a; 1, 0]
  j := !![b, 0; 0, -b]
  k := !![0, -(a * b); b, 0]
  i_mul_i := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  j_mul_j := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  i_mul_j := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  j_mul_i := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring

private theorem secondSquareMatrixBasis_liftHom_apply (a b : R) (q : ℍ[R,a,b ^ 2]) :
    (secondSquareMatrixBasis a b).liftHom q =
      !![q.re + b * q.imJ, a * q.imI - a * b * q.imK;
        q.imI + b * q.imK, q.re - b * q.imJ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [secondSquareMatrixBasis, _root_.QuaternionAlgebra.Basis.lift,
      Algebra.algebraMap_eq_smul_one] <;> ring

variable [Invertible (2 : R)]

/-- The explicit splitting of the symbol `(a,b²)` as `M₂(R)` for units `a` and `b` over a
commutative ring in which two is invertible. It sends the quaternion generators `i` and `j`
to `!![0, a; 1, 0]` and `!![b, 0; 0, -b]`, respectively. -/
noncomputable def secondSquareEquivMatrix (a b : Rˣ) :
    ℍ[R,(a : R),(b : R) ^ 2] ≃ₐ[R] Matrix (Fin 2) (Fin 2) R where
  __ := (secondSquareMatrixBasis (a : R) (b : R)).liftHom
  invFun M :=
    ⟨⅟(2 : R) * (M 0 0 + M 1 1),
      ⅟(2 : R) * (((a⁻¹ : Rˣ) : R) * M 0 1 + M 1 0),
      ⅟(2 : R) * (((b⁻¹ : Rˣ) : R) * (M 0 0 - M 1 1)),
      ⅟(2 : R) * (((b⁻¹ : Rˣ) : R) * (M 1 0 - ((a⁻¹ : Rˣ) : R) * M 0 1))⟩
  left_inv q := by
    rw [AlgHom.toFun_eq_coe, secondSquareMatrixBasis_liftHom_apply]
    ext <;> simp <;> grind [invOf_mul_self, Units.inv_mul]
  right_inv M := by
    rw [AlgHom.toFun_eq_coe, secondSquareMatrixBasis_liftHom_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> grind [invOf_mul_self, Units.inv_mul]

/-- The splitting equivalence on an arbitrary quaternion. -/
@[simp]
theorem secondSquareEquivMatrix_apply (a b : Rˣ) (q : ℍ[R,(a : R),(b : R) ^ 2]) :
    secondSquareEquivMatrix a b q =
      !![q.re + (b : R) * q.imJ, (a : R) * q.imI - (a : R) * (b : R) * q.imK;
        q.imI + (b : R) * q.imK, q.re - (b : R) * q.imJ] :=
  secondSquareMatrixBasis_liftHom_apply (a : R) (b : R) q

/-- The inverse splitting equivalence recovers the four quaternion coordinates from the four
matrix entries. -/
@[simp]
theorem secondSquareEquivMatrix_symm_apply (a b : Rˣ) (M : Matrix (Fin 2) (Fin 2) R) :
    (secondSquareEquivMatrix a b).symm M =
      ⟨⅟(2 : R) * (M 0 0 + M 1 1),
        ⅟(2 : R) * (((a⁻¹ : Rˣ) : R) * M 0 1 + M 1 0),
        ⅟(2 : R) * (((b⁻¹ : Rˣ) : R) * (M 0 0 - M 1 1)),
        ⅟(2 : R) * (((b⁻¹ : Rˣ) : R) *
          (M 1 0 - ((a⁻¹ : Rˣ) : R) * M 0 1))⟩ :=
  (rfl)

/-- The explicit splitting of the symbol `(a²,b)` as `M₂(R)` for units `a` and `b` over a
commutative ring in which two is invertible: exchange the two generators with
`QuaternionAlgebra.swapEquiv` and apply `secondSquareEquivMatrix`. It sends the quaternion
generators `i` and `j` to `!![a, 0; 0, -a]` and `!![0, b; 1, 0]`, respectively. -/
noncomputable def firstSquareEquivMatrix (a b : Rˣ) :
    ℍ[R,(a : R) ^ 2,(b : R)] ≃ₐ[R] Matrix (Fin 2) (Fin 2) R :=
  (_root_.QuaternionAlgebra.swapEquiv ((a : R) ^ 2) (b : R)).trans (secondSquareEquivMatrix b a)

/-- The first-parameter splitting equivalence on an arbitrary quaternion. -/
@[simp]
theorem firstSquareEquivMatrix_apply (a b : Rˣ)
    (q : ℍ[R,(a : R) ^ 2,(b : R)]) :
    firstSquareEquivMatrix a b q =
      !![q.re + (a : R) * q.imI, (b : R) * q.imJ + (b : R) * (a : R) * q.imK;
        q.imJ - (a : R) * q.imK, q.re - (a : R) * q.imI] := by
  simp [firstSquareEquivMatrix, _root_.QuaternionAlgebra.swapEquiv, sub_eq_add_neg]

/-- The inverse first-parameter splitting equivalence recovers the four quaternion coordinates
from the four matrix entries. -/
@[simp]
theorem firstSquareEquivMatrix_symm_apply (a b : Rˣ) (M : Matrix (Fin 2) (Fin 2) R) :
    (firstSquareEquivMatrix a b).symm M =
      ⟨⅟(2 : R) * (M 0 0 + M 1 1),
        ⅟(2 : R) * (((a⁻¹ : Rˣ) : R) * (M 0 0 - M 1 1)),
        ⅟(2 : R) * (((b⁻¹ : Rˣ) : R) * M 0 1 + M 1 0),
        -(⅟(2 : R) * (((a⁻¹ : Rˣ) : R) * (M 1 0 - ((b⁻¹ : Rˣ) : R) * M 0 1)))⟩ := by
  rw [firstSquareEquivMatrix, AlgEquiv.symm_trans_apply, secondSquareEquivMatrix_symm_apply]
  ext <;> simp [_root_.QuaternionAlgebra.swapEquiv]

end QuaternionAlgebra

end TauCeti
