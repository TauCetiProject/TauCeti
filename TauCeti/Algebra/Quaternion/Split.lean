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
matrix algebras, over a commutative ring in which two is invertible.

For a unit `b`, the symbol algebra `ℍ[R,1,b]` is split. The equivalence sends its standard
generators to

```text
i ↦ !![1, 0; 0, -1],   j ↦ !![0, b; 1, 0].
```

For a unit `a`, the symbol algebra `ℍ[R,a,-a]` is split. The equivalence sends its standard
generators to

```text
i ↦ !![0, a; 1, 0],   j ↦ !![0, -a; 1, 0].
```

Their squares are respectively `a` and `-a`, and they anticommute. This is one of the standard
symbol relations for quaternion algebras, useful for reducing identities involving the symbol
`(a, -a)` to computations in a matrix algebra.

The formulas for the equivalences and their inverses are recorded entrywise, so later splitting
arguments can use the constructions without unfolding the quaternion-basis implementation.

## Main definitions

* `TauCeti.QuaternionAlgebra.oneEquivMatrix`: the equivalence
  `ℍ[R,1,b] ≃ₐ[R] Matrix (Fin 2) (Fin 2) R` for a unit `b`.
* `TauCeti.QuaternionAlgebra.aNegAEquivMatrix`: the equivalence
  `ℍ[R,a,-a] ≃ₐ[R] Matrix (Fin 2) (Fin 2) R` for a unit `a`.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter III, Section 2.11.
-/

public section

open scoped Matrix Quaternion

namespace TauCeti

namespace QuaternionAlgebra

variable {R : Type*} [CommRing R]

section One

variable [Invertible (2 : R)]

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

end One

section ANegA

/-- The standard quaternion basis of `2 × 2` matrices with parameters `a` and `-a`. -/
private def splitANegABasis (a : R) :
    _root_.QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) R) a 0 (-a) where
  i := !![0, a; 1, 0]
  j := !![0, -a; 1, 0]
  k := !![a, 0; 0, -a]
  i_mul_i := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp
  j_mul_j := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp
  i_mul_j := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp
  j_mul_i := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp

/-- The algebra homomorphism from `ℍ[R,a,-a]` to `2 × 2` matrices determined by the
standard split matrices. -/
private def splitANegAAlgHom (a : R) : ℍ[R,a,-a] →ₐ[R] Matrix (Fin 2) (Fin 2) R :=
  (splitANegABasis a).liftHom

/-- The entries of the standard matrix representation of `ℍ[R,a,-a]`. -/
private theorem splitANegAAlgHom_apply (a : R) (x : ℍ[R,a,-a]) :
    splitANegAAlgHom a x =
      !![x.re + a * x.imK, a * (x.imI - x.imJ);
         x.imI + x.imJ, x.re - a * x.imK] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitANegAAlgHom, splitANegABasis, _root_.QuaternionAlgebra.Basis.liftHom,
      _root_.QuaternionAlgebra.Basis.lift, Matrix.algebraMap_matrix_apply] <;> ring

variable [Invertible (2 : R)]

/-- The coordinate inverse to the standard matrix representation. -/
private def splitANegAPreimage (a : Rˣ) (M : Matrix (Fin 2) (Fin 2) R) :
    ℍ[R,(a : R),-(a : R)] :=
  ⟨⅟ (2 : R) * (M 0 0 + M 1 1),
    ⅟ (2 : R) * (M 1 0 + (↑(a⁻¹) : R) * M 0 1),
    ⅟ (2 : R) * (M 1 0 - (↑(a⁻¹) : R) * M 0 1),
    ⅟ (2 : R) * ((↑(a⁻¹) : R) * (M 0 0 - M 1 1))⟩

private theorem splitANegAPreimage_apply_splitANegAAlgHom (a : Rˣ)
    (x : ℍ[R,(a : R),-(a : R)]) :
    splitANegAPreimage a (splitANegAAlgHom (a : R) x) = x := by
  ext <;> simp [splitANegAPreimage, splitANegAAlgHom_apply] <;>
    ring_nf
  all_goals simpa [mul_assoc] using (invOf_two_mul_mul_two (R := R) _)

private theorem splitANegAAlgHom_apply_splitANegAPreimage (a : Rˣ)
    (M : Matrix (Fin 2) (Fin 2) R) :
    splitANegAAlgHom (a : R) (splitANegAPreimage a M) = M := by
  have hunit (z : R) : (a : R) * z * (↑(a⁻¹) : R) = z := by
    calc
      (a : R) * z * (↑(a⁻¹) : R) = ((a : R) * (↑(a⁻¹) : R)) * z := by ring
      _ = z := by rw [a.mul_inv, one_mul]
  have hhalf (z : R) : ⅟ (2 : R) * z + ⅟ (2 : R) * z = z := by
    calc
      ⅟ (2 : R) * z + ⅟ (2 : R) * z = (⅟ (2 : R) + ⅟ (2 : R)) * z := by ring
      _ = z := by rw [invOf_two_add_invOf_two, one_mul]
  rw [splitANegAAlgHom_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitANegAPreimage] <;> ring_nf
  all_goals first
    | simpa [mul_assoc] using (invOf_two_mul_mul_two (R := R) _)
    | simp [hunit, hhalf]
  simpa only [mul_assoc] using (invOf_two_mul_mul_two (R := R) (M 0 1))

/-- The explicit splitting `ℍ[R,a,-a] ≃ₐ[R] M₂(R)` for a unit `a`, over a commutative
ring in which `2` is invertible. -/
noncomputable def aNegAEquivMatrix (a : Rˣ) :
    ℍ[R,(a : R),-(a : R)] ≃ₐ[R] Matrix (Fin 2) (Fin 2) R :=
  AlgEquiv.ofBijective (splitANegAAlgHom (a : R)) ⟨
    Function.LeftInverse.injective (splitANegAPreimage_apply_splitANegAAlgHom a),
    Function.RightInverse.surjective (splitANegAAlgHom_apply_splitANegAPreimage a)⟩

/-- The splitting equivalence is the standard matrix representation. -/
theorem aNegAEquivMatrix_apply (a : Rˣ) (x : ℍ[R,(a : R),-(a : R)]) :
    aNegAEquivMatrix a x =
      !![x.re + (a : R) * x.imK, (a : R) * (x.imI - x.imJ);
         x.imI + x.imJ, x.re - (a : R) * x.imK] := by
  exact (AlgEquiv.ofBijective_apply _ _ x).trans (splitANegAAlgHom_apply (a : R) x)

/-- The inverse of the splitting equivalence, in matrix coordinates. -/
theorem aNegAEquivMatrix_symm_apply (a : Rˣ) (M : Matrix (Fin 2) (Fin 2) R) :
    (aNegAEquivMatrix a).symm M =
      ⟨⅟ (2 : R) * (M 0 0 + M 1 1),
        ⅟ (2 : R) * (M 1 0 + (↑(a⁻¹) : R) * M 0 1),
        ⅟ (2 : R) * (M 1 0 - (↑(a⁻¹) : R) * M 0 1),
        ⅟ (2 : R) * ((↑(a⁻¹) : R) * (M 0 0 - M 1 1))⟩ := by
  apply (aNegAEquivMatrix a).symm_apply_eq.mpr
  exact ((AlgEquiv.ofBijective_apply _ _ _).trans
    (splitANegAAlgHom_apply_splitANegAPreimage a M)).symm

/-- The first quaternion generator maps to `!![0, a; 1, 0]`. -/
@[simp]
theorem aNegAEquivMatrix_apply_i (a : Rˣ) :
    aNegAEquivMatrix a ⟨0, 1, 0, 0⟩ = !![0, (a : R); 1, 0] := by
  rw [aNegAEquivMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The second quaternion generator maps to `!![0, -a; 1, 0]`. -/
@[simp]
theorem aNegAEquivMatrix_apply_j (a : Rˣ) :
    aNegAEquivMatrix a ⟨0, 0, 1, 0⟩ = !![0, -(a : R); 1, 0] := by
  rw [aNegAEquivMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The product of the two quaternion generators maps to `!![a, 0; 0, -a]`. -/
@[simp]
theorem aNegAEquivMatrix_apply_k (a : Rˣ) :
    aNegAEquivMatrix a ⟨0, 0, 0, 1⟩ = !![(a : R), 0; 0, -(a : R)] := by
  rw [aNegAEquivMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end ANegA

end QuaternionAlgebra

end TauCeti
