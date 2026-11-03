/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.StdBasis
public import TauCeti.Algebra.Cellular.Basic

/-!
# The cellular basis of a matrix algebra

The full matrix algebra `Matrix n n R` over a commutative ring is cellular with a single cell:
the cellular basis consists of the matrix units `Matrix.single i j 1`, indexed by pairs of rows
and columns, and the anti-involution is the transpose. Since there is no lower cell, the cellular
axiom `a * single s t 1 = ∑ u, a u s • single u t 1` holds on the nose.

The cell representation of this cellular basis is the identity of `Matrix n n R`, and its Gram
matrix is the identity matrix, because `single s t 1 * single u v 1` is `single s v 1` when
`t = u` and zero otherwise.

## Main definitions

* `TauCeti.CellularBasis.matrix R n`: the cellular basis of `Matrix n n R` by matrix units.

## Main results

* `TauCeti.CellularBasis.cellRep_matrix`: its cell representation is the identity.
* `TauCeti.CellularBasis.gramMatrix_matrix`: its Gram matrix is the identity matrix.

## References

* J. J. Graham and G. I. Lehrer, *Cellular algebras*, Invent. Math. 123 (1996), 1–34,
  Example 1.2.
-/

public section

open Module

namespace TauCeti.CellularBasis

variable (R n : Type*) [CommRing R] [Fintype n] [DecidableEq n]

/-- The cellular basis of the matrix algebra `Matrix n n R`: one cell, the matrix units
`Matrix.single s t 1` as basis, and the transpose as anti-involution. -/
noncomputable def matrix : CellularBasis R (Matrix n n R) (fun _ : Unit => n) where
  basis := (Matrix.stdBasis R n n).reindex
    ((Equiv.sigmaEquivProd Unit (n × n)).trans (Equiv.uniqueProd (n × n) Unit)).symm
  antiInvolution := Matrix.transposeAlgEquiv n R R
  unop_antiInvolution_basis _ s t := by
    simp [Matrix.stdBasis_eq_single, Matrix.transpose_single]
  exists_mul_basis a _ s := ⟨fun u => a u s, fun t => by
    rw [sub_eq_zero.2]
    · exact zero_mem _
    ext i j
    simp [Matrix.stdBasis_eq_single, Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply,
      ite_and]⟩

variable {R n}

@[simp]
theorem matrix_basis (s t : n) : (matrix R n).basis ⟨(), s, t⟩ = Matrix.single s t 1 := by
  simp [matrix, Matrix.stdBasis_eq_single]

/-- The matrix units form a single cell, so there is no lower cell. -/
@[simp]
theorem lowerSpan_matrix : (matrix R n).lowerSpan () = ⊥ := by
  have h : {i : Σ _ : Unit, n × n | i.1 < ()} = ∅ :=
    Set.eq_empty_of_forall_notMem fun _ hi => lt_irrefl () hi
  rw [lowerSpan_def, h, Set.image_empty, Submodule.span_empty]

/-- The cell representation of the matrix units is the identity: the cell module of a matrix
algebra is its defining module. -/
@[simp]
theorem cellRep_matrix (a : Matrix n n R) : (matrix R n).cellRep () a = a := by
  ext u s
  have h := (matrix R n).mul_basis_sub_sum_mem a () s s
  rw [lowerSpan_matrix, Submodule.mem_bot, sub_eq_zero] at h
  simpa [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply] using
    (congrFun (congrFun h u) s).symm

/-- The Gram matrix of the matrix units is the identity matrix. -/
@[simp]
theorem gramMatrix_matrix : (matrix R n).gramMatrix () = 1 := by
  ext t u
  simpa [Matrix.one_apply, Matrix.single_apply] using
    ((matrix R n).cellRep_basis () t t u t).symm

end TauCeti.CellularBasis
