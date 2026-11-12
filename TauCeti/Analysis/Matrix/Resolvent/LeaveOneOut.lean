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

namespace Matrix.IsHermitian

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
  {A : Matrix n n 𝕜} (hA : A.IsHermitian)

include hA

/-- **Leave-one-out formula.** The reciprocal of a diagonal entry of the resolvent of a Hermitian
matrix at a non-real point is the diagonal entry of `A - z • 1` minus the quadratic form of the
resolvent of the principal submatrix away from `i` in the `i`-th column. -/
theorem inv_inv_sub_smul_one_apply_self {z : 𝕜} (hz : RCLike.im z ≠ 0) (i : n) :
    ((A - z • 1)⁻¹ i i)⁻¹ =
      A i i - z - star (fun a : {a // a ≠ i} ↦ A a i) ⬝ᵥ
        (((A.submatrix (↑) (↑) : Matrix {a // a ≠ i} {a // a ≠ i} 𝕜) - z • 1)⁻¹ *ᵥ
          fun a : {a // a ≠ i} ↦ A a i) := by
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
    simp [a.2.symm, ← hA.apply i a]
  have hcol : (fun a : {a // a ≠ i} ↦ (A - z • 1) a i) = fun a : {a // a ≠ i} ↦ A a i := by
    ext a
    simp [a.2]
  rw [hrow, hcol]
  simp

/-- **Leave-one-out formula.** The diagonal entry `R(z) i i` of the resolvent of a Hermitian matrix
at a non-real point equals `(A i i - z - aᵢᴴ (A⁽ⁱ⁾ - z • 1)⁻¹ aᵢ)⁻¹`. -/
theorem inv_sub_smul_one_apply_self_eq {z : 𝕜} (hz : RCLike.im z ≠ 0) (i : n) :
    (A - z • 1)⁻¹ i i =
      (A i i - z - star (fun a : {a // a ≠ i} ↦ A a i) ⬝ᵥ
        (((A.submatrix (↑) (↑) : Matrix {a // a ≠ i} {a // a ≠ i} 𝕜) - z • 1)⁻¹ *ᵥ
          fun a : {a // a ≠ i} ↦ A a i))⁻¹ := by
  rw [← hA.inv_inv_sub_smul_one_apply_self hz i, inv_inv]

end Matrix.IsHermitian
