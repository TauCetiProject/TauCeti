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
# Split quaternion algebras

This file constructs explicit algebra equivalences from split quaternion algebras to two-by-two
matrix algebras. For a unit `b` over a commutative ring in which two is invertible, the symbol
algebra `ℍ[R,1,b]` is split. The equivalence sends its standard generators to

```text
i ↦ !![1, 0; 0, -1],   j ↦ !![0, b; 1, 0].
```

The formulas for the equivalence and its inverse are recorded entrywise, so later splitting
arguments can use the construction without unfolding the quaternion-basis implementation.

## Main definition

* `TauCeti.QuaternionAlgebra.oneEquivMatrix`: the equivalence
  `ℍ[R,1,b] ≃ₐ[R] Matrix (Fin 2) (Fin 2) R` for a unit `b`.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter III, Section 2.11.
-/

public section

open scoped Matrix Quaternion

namespace TauCeti

namespace QuaternionAlgebra

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

private def oneMatrixBasis (b : R) :
    _root_.QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) R) 1 0 b where
  i := !![1, 0; 0, -1]
  j := !![0, b; 1, 0]
  k := !![0, b; -1, 0]
  i_mul_i := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  j_mul_j := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  i_mul_j := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  j_mul_i := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [Invertible (2 : R)] in
private theorem oneMatrixBasis_liftHom_apply (b : Rˣ) (q : ℍ[R,1,(b : R)]) :
    (oneMatrixBasis (b : R)).liftHom q =
      !![q.re + q.imI, (b : R) * (q.imJ + q.imK);
        q.imJ - q.imK, q.re - q.imI] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oneMatrixBasis, _root_.QuaternionAlgebra.Basis.liftHom,
      _root_.QuaternionAlgebra.Basis.lift, Algebra.algebraMap_eq_smul_one] <;> ring

private def oneMatrixInverse (b : Rˣ) (M : Matrix (Fin 2) (Fin 2) R) :
    ℍ[R,1,(b : R)] :=
  ⟨⅟(2 : R) * (M 0 0 + M 1 1),
    ⅟(2 : R) * (M 0 0 - M 1 1),
    ⅟(2 : R) * (((b⁻¹ : Rˣ) : R) * M 0 1 + M 1 0),
    ⅟(2 : R) * (((b⁻¹ : Rˣ) : R) * M 0 1 - M 1 0)⟩

private theorem invOf_two_mul_mul_two (x : R) : ⅟(2 : R) * (x * 2) = x := by
  calc
    ⅟(2 : R) * (x * 2) = (⅟(2 : R) * 2) * x := by ring
    _ = x := by rw [invOf_mul_self, one_mul]

private theorem unit_mul_invOf_two_mul_inv_mul_two (b : Rˣ) (x : R) :
    (b : R) * (⅟(2 : R) * (((b⁻¹ : Rˣ) : R) * (x * 2))) = x := by
  calc
    (b : R) * (⅟(2 : R) * (((b⁻¹ : Rˣ) : R) * (x * 2))) =
        ((b : R) * (b⁻¹ : Rˣ)) * (⅟(2 : R) * 2) * x := by ring
    _ = x := by
      have hb : (b : R) * ((b⁻¹ : Rˣ) : R) = 1 := b.val_inv
      rw [hb, invOf_mul_self, one_mul]
      exact one_mul x

private theorem oneMatrixInverse_leftInverse (b : Rˣ) :
    Function.LeftInverse (oneMatrixInverse b) (oneMatrixBasis (b : R)).liftHom := by
  intro q
  rw [oneMatrixBasis_liftHom_apply]
  ext <;> simp [oneMatrixInverse] <;> ring_nf
  all_goals simpa [mul_assoc] using (invOf_two_mul_mul_two (R := R) _)

private theorem oneMatrixInverse_rightInverse (b : Rˣ) :
    Function.RightInverse (oneMatrixInverse b) (oneMatrixBasis (b : R)).liftHom := by
  intro M
  rw [oneMatrixBasis_liftHom_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [oneMatrixInverse] <;> ring_nf
  all_goals first
    | simpa [mul_assoc] using (invOf_two_mul_mul_two (R := R) _)
    | simpa [mul_assoc] using (unit_mul_invOf_two_mul_inv_mul_two b _)

private theorem oneMatrixBasis_liftHom_bijective (b : Rˣ) :
    Function.Bijective (oneMatrixBasis (b : R)).liftHom := by
  exact ⟨(oneMatrixInverse_leftInverse b).injective, (oneMatrixInverse_rightInverse b).surjective⟩

/-- The explicit splitting `ℍ[R,1,b] ≃ₐ[R] M₂(R)` for a unit `b` over a commutative ring in
which two is invertible. It sends the quaternion generators `i` and `j` to
`!![1, 0; 0, -1]` and `!![0, b; 1, 0]`, respectively. -/
noncomputable def oneEquivMatrix (b : Rˣ) :
    ℍ[R,1,(b : R)] ≃ₐ[R] Matrix (Fin 2) (Fin 2) R :=
  AlgEquiv.ofBijective (oneMatrixBasis (b : R)).liftHom
    (oneMatrixBasis_liftHom_bijective b)

/-- The splitting equivalence on an arbitrary quaternion. -/
@[simp]
theorem oneEquivMatrix_apply (b : Rˣ) (q : ℍ[R,1,(b : R)]) :
    oneEquivMatrix b q =
      !![q.re + q.imI, (b : R) * (q.imJ + q.imK);
        q.imJ - q.imK, q.re - q.imI] := by
  rw [oneEquivMatrix, AlgEquiv.ofBijective_apply, oneMatrixBasis_liftHom_apply]

/-- The inverse splitting equivalence recovers the four quaternion coordinates from the four
matrix entries. -/
@[simp]
theorem oneEquivMatrix_symm_apply (b : Rˣ) (M : Matrix (Fin 2) (Fin 2) R) :
    (oneEquivMatrix b).symm M =
      ⟨⅟(2 : R) * (M 0 0 + M 1 1),
        ⅟(2 : R) * (M 0 0 - M 1 1),
        ⅟(2 : R) * (((b⁻¹ : Rˣ) : R) * M 0 1 + M 1 0),
        ⅟(2 : R) * (((b⁻¹ : Rˣ) : R) * M 0 1 - M 1 0)⟩ := by
  -- The displayed quaternion is definitionally the private inverse used in the bijectivity proof.
  change (oneEquivMatrix b).symm M = oneMatrixInverse b M
  apply (oneEquivMatrix b).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (oneMatrixInverse_rightInverse b M).symm

end QuaternionAlgebra

end TauCeti
