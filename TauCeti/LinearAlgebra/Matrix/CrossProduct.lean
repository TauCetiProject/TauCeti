/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Trace
public import TauCeti.LinearAlgebra.UnitaryGroup

/-!
# How a matrix interacts with the cross product

A `3 × 3` matrix `M` acts on `R³`, and the cross product is a bilinear map `R³ × R³ → R³`, so one
may ask how the two compose. The answer is the Cauchy--Binet identity
`(M u) ⨯₃ (M w) = (adj M)ᵀ (u ⨯₃ w)`. For an orthogonal matrix `adj M = det M • Mᵀ`, so rotations
preserve the cross product and reflections reverse it. Replacing `M` by `1 + ε M` and reading off
the linear term in `ε` gives the infinitesimal form

`(M u) ⨯₃ w + u ⨯₃ (M w) = (tr M) • (u ⨯₃ w) - Mᵀ (u ⨯₃ w)`.

So the cross product is *not* preserved by an arbitrary matrix, but a trace-zero matrix acts on it
as a derivation with `-Mᵀ` in the target slot, which is the form the identity is used in.

The **hat map** `u ↦ û` (`TauCeti.crossProductMatrix`) sends `u` to the matrix of the linear map
`v ↦ u ⨯₃ v`. The matrix `û` is skew-symmetric, and the commutator of two such matrices is the
matrix of the cross product of their vectors: `[û, v̂] = (u ⨯₃ v)^`.

## Main definitions

* `TauCeti.crossProductMatrix R`: the hat map `u ↦ û`, the matrix of `v ↦ u ⨯₃ v`.

## Main results

* `Matrix.mulVec_cross_mulVec`: the Cauchy--Binet identity.
* `Matrix.mulVec_cross_mulVec_of_mem_orthogonalGroup`: orthogonal matrices preserve the cross
  product up to their determinant.
* `Matrix.mulVec_cross_mulVec_of_mem_specialOrthogonalGroup`: rotations preserve the cross
  product.
* `Matrix.mulVec_cross_add_cross_mulVec`: its infinitesimal form.
* `Matrix.mulVec_cross_add_cross_mulVec_of_trace_eq_zero`: its trace-zero case.
* `Matrix.det_eq_one_of_mulVec_cross`: a matrix preserving the cross product with unit
  determinant has determinant one.
* `TauCeti.transpose_crossProductMatrix`: the matrix `û` is skew-symmetric.
* `TauCeti.mul_crossProductMatrix_mul_transpose_of_mem_orthogonalGroup`: `M û Mᵀ = det M • (M u)^`
  for an orthogonal matrix `M`.
* `TauCeti.crossProductMatrix_cross`: `(u ⨯₃ v)^ = û v̂ - v̂ û`.
* `TauCeti.mul_crossProductMatrix_mul_transpose`: a rotation `M` conjugates `û` to `(M u)^`.
-/

public section

open Matrix

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- **The Cauchy--Binet identity for the cross product.** A matrix `M` sends the cross product of
`u` and `w` to the cross product of their images up to the transposed adjugate of `M`:
`(M u) ⨯₃ (M w) = (adj M)ᵀ (u ⨯₃ w)`. -/
theorem _root_.Matrix.mulVec_cross_mulVec (M : Matrix (Fin 3) (Fin 3) R) (u w : Fin 3 → R) :
    (M *ᵥ u) ⨯₃ (M *ᵥ w) = M.adjugateᵀ *ᵥ (u ⨯₃ w) := by
  ext i
  fin_cases i <;>
    simp [cross_apply, Matrix.mulVec, vec3_dotProduct, Matrix.adjugate_fin_three,
      Matrix.vecHead, Matrix.vecTail] <;>
    ring

/-- **Orthogonal matrices preserve the cross product up to their determinant**:
`(M u) ⨯₃ (M w) = det M • M (u ⨯₃ w)` for `M ∈ O(3)`. The adjugate of an orthogonal matrix is its
determinant times its transpose. A reflection, of determinant `-1`, reverses the cross product. -/
theorem _root_.Matrix.mulVec_cross_mulVec_of_mem_orthogonalGroup
    {M : Matrix (Fin 3) (Fin 3) R} (hM : M ∈ orthogonalGroup (Fin 3) R) (u w : Fin 3 → R) :
    (M *ᵥ u) ⨯₃ (M *ᵥ w) = M.det • M *ᵥ (u ⨯₃ w) := by
  rw [Matrix.mulVec_cross_mulVec,
    adjugate_eq_det_smul_of_mul_eq_one ((mem_orthogonalGroup_iff _ _).1 hM), transpose_smul,
    transpose_transpose, smul_mulVec]

/-- **Rotations preserve the cross product**: `(M u) ⨯₃ (M w) = M (u ⨯₃ w)` for `M ∈ SO(3)`, the
case `det M = 1` of `Matrix.mulVec_cross_mulVec_of_mem_orthogonalGroup`. The converse direction is
`Matrix.det_eq_one_of_mulVec_cross`. -/
theorem _root_.Matrix.mulVec_cross_mulVec_of_mem_specialOrthogonalGroup
    {M : Matrix (Fin 3) (Fin 3) R} (hM : M ∈ specialOrthogonalGroup (Fin 3) R) (u w : Fin 3 → R) :
    (M *ᵥ u) ⨯₃ (M *ᵥ w) = M *ᵥ (u ⨯₃ w) := by
  rw [Matrix.mulVec_cross_mulVec_of_mem_orthogonalGroup (mem_specialOrthogonalGroup_iff.1 hM).1,
    (mem_specialOrthogonalGroup_iff.1 hM).2, one_smul]

/-- **A matrix acting on a cross product.** Applying `M` to one factor at a time and adding gives
the trace of `M` times the cross product, corrected by `-Mᵀ` applied to it. This is the derivative
at the identity of the Cauchy--Binet identity `(M u) ⨯₃ (M w) = (adj M)ᵀ (u ⨯₃ w)`. -/
theorem _root_.Matrix.mulVec_cross_add_cross_mulVec (M : Matrix (Fin 3) (Fin 3) R)
    (u w : Fin 3 → R) :
    (M *ᵥ u) ⨯₃ w + u ⨯₃ (M *ᵥ w) = M.trace • (u ⨯₃ w) - Mᵀ *ᵥ (u ⨯₃ w) := by
  ext i
  fin_cases i <;>
    simp [cross_apply, Matrix.mulVec, vec3_dotProduct, Matrix.transpose_apply,
      Matrix.trace_fin_three, Matrix.vecHead, Matrix.vecTail] <;>
    ring

/-- **A trace-zero matrix acts on the cross product as a derivation**, with the transpose acting on
the target: `(M u) ⨯₃ w + u ⨯₃ (M w) = -(Mᵀ (u ⨯₃ w))`. -/
theorem _root_.Matrix.mulVec_cross_add_cross_mulVec_of_trace_eq_zero
    (M : Matrix (Fin 3) (Fin 3) R) (hM : M.trace = 0) (u w : Fin 3 → R) :
    (M *ᵥ u) ⨯₃ w + u ⨯₃ (M *ᵥ w) = -(Mᵀ *ᵥ (u ⨯₃ w)) := by
  rw [Matrix.mulVec_cross_add_cross_mulVec, hM, zero_smul, zero_sub]

/-- **A matrix preserving the cross product with unit determinant has determinant one**: if
`M (x ⨯₃ y) = (M x) ⨯₃ (M y)` for all `x`, `y` and `det M` is a unit, then `det M = 1`. The unit
hypothesis cannot be dropped, since the zero matrix preserves the cross product. Orthogonal
matrices have unit determinant, so an orthogonal matrix preserving the cross product is a rotation;
this is the converse of `Matrix.mulVec_cross_mulVec_of_mem_specialOrthogonalGroup`. -/
theorem _root_.Matrix.det_eq_one_of_mulVec_cross {M : Matrix (Fin 3) (Fin 3) R}
    (hM : IsUnit M.det) (h : ∀ x y, M *ᵥ (x ⨯₃ y) = (M *ᵥ x) ⨯₃ (M *ᵥ y)) : M.det = 1 := by
  -- By Cauchy--Binet, `M` agrees with `(adj M)ᵀ` on cross products, and each basis vector is a
  -- cross product of basis vectors, so `M = (adj M)ᵀ`. Taking determinants gives
  -- `det M = (det M)²`, and cancelling the unit `det M` gives `det M = 1`.
  have hadj : M = M.adjugateᵀ := by
    refine ext_of_mulVec_single fun i ↦ ?_
    have hi : Pi.single i 1 = Pi.single (i + 1) 1 ⨯₃ Pi.single (i + 2) (1 : R) := by
      fin_cases i <;> ext j <;> fin_cases j <;> simp [cross_apply]
    rw [hi, h, mulVec_cross_mulVec]
  refine hM.mul_eq_left.mp ?_
  conv_rhs => rw [hadj, det_transpose, det_adjugate]
  simp [sq]

/-! ### The hat map -/

variable (R) in
/-- The **hat map** `u ↦ û`, sending `u` to the matrix of the linear map `v ↦ u ⨯₃ v`
(`TauCeti.crossProductMatrix_mulVec`). -/
def crossProductMatrix : (Fin 3 → R) →ₗ[R] Matrix (Fin 3) (Fin 3) R :=
  LinearMap.toMatrix'.toLinearMap ∘ₗ crossProduct

/-- The matrix `û` acts on vectors by the cross product with `u`. -/
@[simp]
theorem crossProductMatrix_mulVec (u v : Fin 3 → R) :
    crossProductMatrix R u *ᵥ v = u ⨯₃ v :=
  LinearMap.toMatrix'_mulVec _ v

/-- The entries of `û`. -/
theorem crossProductMatrix_apply (u : Fin 3 → R) :
    crossProductMatrix R u = !![0, -u 2, u 1; u 2, 0, -u 0; -u 1, u 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossProductMatrix, LinearMap.toMatrix'_apply, cross_apply]

/-- The matrix `û` is skew-symmetric. -/
@[simp]
theorem transpose_crossProductMatrix (u : Fin 3 → R) :
    (crossProductMatrix R u)ᵀ = -crossProductMatrix R u := by
  rw [crossProductMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **Conjugating the hat matrix by an orthogonal matrix**: `M û Mᵀ = det M • (M u)^` for
`M ∈ O(3)`, since `M` preserves the cross product up to its determinant
(`Matrix.mulVec_cross_mulVec_of_mem_orthogonalGroup`) and `det M ^ 2 = 1`. -/
theorem mul_crossProductMatrix_mul_transpose_of_mem_orthogonalGroup
    {M : Matrix (Fin 3) (Fin 3) R} (hM : M ∈ orthogonalGroup (Fin 3) R) (u : Fin 3 → R) :
    M * crossProductMatrix R u * Mᵀ = M.det • crossProductMatrix R (M *ᵥ u) := by
  have hMMt : M * Mᵀ = 1 := (mem_orthogonalGroup_iff _ _).1 hM
  have hdet : M.det * M.det = 1 := by
    simpa [det_transpose] using congrArg det hMMt
  refine Matrix.toLin'.injective (LinearMap.ext fun v ↦ ?_)
  have h := Matrix.mulVec_cross_mulVec_of_mem_orthogonalGroup hM u (Mᵀ *ᵥ v)
  rw [mulVec_mulVec, hMMt, one_mulVec] at h
  simp only [toLin'_apply, ← mulVec_mulVec, crossProductMatrix_mulVec, smul_mulVec, h, smul_smul,
    hdet, one_smul]

/-- **The hat map is a Lie algebra homomorphism.** The matrix of `u ⨯₃ v` is the commutator of the
matrices of `u` and `v`; this is the Jacobi identity of the cross product. -/
theorem crossProductMatrix_cross (u v : Fin 3 → R) :
    crossProductMatrix R (u ⨯₃ v) = crossProductMatrix R u * crossProductMatrix R v -
      crossProductMatrix R v * crossProductMatrix R u := by
  refine Matrix.toLin'.injective (LinearMap.ext fun w ↦ ?_)
  simp only [toLin'_apply, sub_mulVec, ← mulVec_mulVec, crossProductMatrix_mulVec, cross_cross]

/-- **Rotations act on hat matrices by rotating the vector**: `M û Mᵀ = (M u)^` for `M ∈ SO(3)`.
This is the adjoint action of `SO(3)` on `so(3)` in the coordinates of the hat map. -/
theorem mul_crossProductMatrix_mul_transpose {M : Matrix (Fin 3) (Fin 3) R}
    (hM : M ∈ specialOrthogonalGroup (Fin 3) R) (u : Fin 3 → R) :
    M * crossProductMatrix R u * Mᵀ = crossProductMatrix R (M *ᵥ u) := by
  refine ext_of_mulVec_single fun i ↦ ?_
  have hMMt : M * Mᵀ = 1 := (mem_orthogonalGroup_iff _ _).1 hM.1
  simp only [← mulVec_mulVec, crossProductMatrix_mulVec]
  rw [← mulVec_cross_mulVec_of_mem_specialOrthogonalGroup hM]
  simp only [mulVec_mulVec, hMMt, one_mulVec]

end TauCeti
