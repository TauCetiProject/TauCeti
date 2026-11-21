/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Resolvent.Basic
public import TauCeti.LinearAlgebra.Matrix.SchurComplement

/-!
# Leave-one-out formula for Hermitian resolvents

For a Hermitian matrix `A` and an index `i`, write `A⁽ⁱ⁾` for the principal submatrix of `A` on the
indices other than `i` and `aᵢ` for the `i`-th column of `A` with the entry `A i i` removed. With
the sign convention `R(z) = (A - z • 1)⁻¹`, the diagonal resolvent entry satisfies
`R(z) i i = (A i i - z - aᵢᴴ (A⁽ⁱ⁾ - z • 1)⁻¹ aᵢ)⁻¹` at every non-real `z`. Both shifted matrices
are invertible there, so no invertibility hypothesis is needed. The formula is the specialization of
the Schur complement identity `Matrix.inv_inv_apply_self_eq_sub`; the determinant lemma is already
Mathlib's `Matrix.det_add_replicateCol_mul_replicateRow`.

## Main results

* `Matrix.IsHermitian.inv_sub_smul_one_apply_self_eq`: the leave-one-out formula for the diagonal
  entries of the resolvent of a Hermitian matrix.
* `Matrix.IsHermitian.inv_inv_sub_smul_one_apply_self`: the equivalent formula for the reciprocal.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An introduction to random matrices*, Cambridge
  University Press, 2010, Appendix A and §2.4.
-/

public section

noncomputable section

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {𝕜 n : Type*} [Fintype n] [DecidableEq n]

section

variable [CommRing 𝕜]

/-- The resolvent of the principal submatrix obtained by deleting row and column `i`.
The inverse is totalized: the result is zero if the shifted minor has nonunit determinant. -/
def minorResolvent (A : Matrix n n 𝕜) (i : n) (z : 𝕜) :
    Matrix {j // j ≠ i} {j // j ≠ i} 𝕜 :=
  (A.submatrix (↑) (↑) - z • 1)⁻¹

/-- The minor resolvent is the totalized inverse of the shifted principal submatrix,
which is zero when its determinant is not a unit. -/
theorem minorResolvent_def (A : Matrix n n 𝕜) (i : n) (z : 𝕜) :
    A.minorResolvent i z = (A.submatrix (↑) (↑) - z • 1)⁻¹ := by rw [minorResolvent]

end

end Matrix

namespace Matrix.IsHermitian

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
  {A : Matrix n n 𝕜} (hA : A.IsHermitian)

include hA

/-- At a nonreal parameter, the shifted Hermitian principal submatrix times its resolvent
is the identity. -/
@[simp]
theorem submatrix_sub_smul_one_mul_minorResolvent {z : 𝕜} (hz : RCLike.im z ≠ 0) (i : n) :
    (A.submatrix (↑) (↑) - z • 1) * A.minorResolvent i z = 1 := by
  rw [minorResolvent_def]
  exact mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp
    ((hA.submatrix (Subtype.val : {j // j ≠ i} → n)).isUnit_sub_smul_one_of_im_ne_zero hz))

/-- At a nonreal parameter, the Hermitian minor resolvent times the shifted principal submatrix
is the identity. -/
@[simp]
theorem minorResolvent_mul_submatrix_sub_smul_one {z : 𝕜} (hz : RCLike.im z ≠ 0) (i : n) :
    A.minorResolvent i z * (A.submatrix (↑) (↑) - z • 1) = 1 := by
  rw [minorResolvent_def]
  exact nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp
    ((hA.submatrix (Subtype.val : {j // j ≠ i} → n)).isUnit_sub_smul_one_of_im_ne_zero hz))

/-- The Euclidean operator norm of a Hermitian principal-minor resolvent is at most
the reciprocal of the absolute imaginary part of the nonreal parameter. -/
theorem l2_opNorm_minorResolvent_le {z : 𝕜} (hz : RCLike.im z ≠ 0) (i : n) :
    ‖A.minorResolvent i z‖ ≤ |RCLike.im z|⁻¹ := by
  rw [minorResolvent_def]
  exact (hA.submatrix (Subtype.val : {j // j ≠ i} → n)).l2_opNorm_inv_sub_smul_one_le hz

/-- **Leave-one-out formula.** The reciprocal of a diagonal entry of the resolvent of a Hermitian
matrix at a non-real point is the diagonal entry of `A - z • 1` minus the quadratic form of the
resolvent of the principal submatrix away from `i` in the `i`-th column. -/
theorem inv_inv_sub_smul_one_apply_self {z : 𝕜} (hz : RCLike.im z ≠ 0) (i : n) :
    ((A - z • 1)⁻¹ i i)⁻¹ =
      A i i - z - star (fun a : {a // a ≠ i} ↦ A a i) ⬝ᵥ
        (A.minorResolvent i z *ᵥ fun a : {a // a ≠ i} ↦ A a i) := by
  have hB : (A.submatrix (↑) (↑) : Matrix {a // a ≠ i} {a // a ≠ i} 𝕜).IsHermitian :=
    hA.submatrix _
  have hsub : ((A - z • 1).submatrix (↑) (↑) : Matrix {a // a ≠ i} {a // a ≠ i} 𝕜) =
      A.submatrix (↑) (↑) - z • 1 := by
    ext a b
    simp [Matrix.one_apply, Subtype.ext_iff]
  have h := (A - z • 1).inv_inv_apply_self_eq_sub i (by
    rw [hsub, ← isUnit_iff_isUnit_det]
    exact hB.isUnit_sub_smul_one_of_im_ne_zero hz)
  rw [h, hsub]
  have hrow : (fun a : {a // a ≠ i} ↦ (A - z • 1) i a) = star fun a : {a // a ≠ i} ↦ A a i := by
    ext a
    simp [a.property.symm, ← hA.apply i a]
  have hcol : (fun a : {a // a ≠ i} ↦ (A - z • 1) a i) = fun a : {a // a ≠ i} ↦ A a i := by
    ext a
    simp [a.property]
  rw [hrow, hcol, minorResolvent_def]
  simp

/-- **Leave-one-out formula.** The diagonal entry `R(z) i i` of the resolvent of a Hermitian matrix
at a non-real point equals `(A i i - z - aᵢᴴ (A⁽ⁱ⁾ - z • 1)⁻¹ aᵢ)⁻¹`. -/
theorem inv_sub_smul_one_apply_self_eq {z : 𝕜} (hz : RCLike.im z ≠ 0) (i : n) :
    (A - z • 1)⁻¹ i i =
      (A i i - z - star (fun a : {a // a ≠ i} ↦ A a i) ⬝ᵥ
        (A.minorResolvent i z *ᵥ fun a : {a // a ≠ i} ↦ A a i))⁻¹ := by
  rw [← hA.inv_inv_sub_smul_one_apply_self hz i, inv_inv]

end Matrix.IsHermitian
