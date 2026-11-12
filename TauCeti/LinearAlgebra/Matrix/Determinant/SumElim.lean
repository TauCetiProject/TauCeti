/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# Determinants of a fixed family followed by a varying one

Let `x` be a family of vectors in `R^ι` indexed by `m`, and let `y` be a family indexed by `n`
whose orthogonal vectors, those `v` with `y k ⬝ᵥ v = 0` for every `k`, all lie in the span of
`x`. Suppose `w` is a family indexed by `n` pairing with `y` to the standard basis, so
`y k ⬝ᵥ w j` is `1` if `j = k` and `0` otherwise. Then, for a family `z` indexed by `n`, the
determinant of the square matrix whose rows are `x` followed by `z` factors as the determinant of
the pairings `y k ⬝ᵥ z j` times the same determinant at `z = w`.

The proof writes each `z j` as a combination of the `x i` plus `∑ k, (y k ⬝ᵥ z j) • w k`, which
expresses the matrix of `x` followed by `z` as a block lower triangular matrix times the matrix of
`x` followed by `w`.

This is the linear algebra behind complementary minors: taking `z` to be standard basis vectors
compares the Plücker coordinates of a subspace with those of its orthogonal complement.

Fixing the rows `x` placed along `e : t ≃ ι ⊕ κ`, the determinant is an alternating map of the
remaining rows. The exterior product of two such maps gives the Plücker relations among minors.

## Main definitions

* `Matrix.detRowAlternatingSumElim e x`: the determinant of the square matrix with the fixed
  rows `x` inserted along `e : t ≃ ι ⊕ κ`, as an alternating map of the remaining rows.

## Main results

* `TauCeti.Matrix.det_sumElim_eq_det_mul`: the determinant of `x` followed by `z` is
  `det (y * zᵀ)` times the determinant of `x` followed by `w`.
-/

public section

open scoped Matrix

namespace TauCeti.Matrix

variable {R m n ι : Type*} [CommRing R] [Fintype m] [Fintype n] [Fintype ι] [DecidableEq m]
  [DecidableEq n]

/-- Let `x` span every vector orthogonal to all `y k`, and let `w j` pair with `y` to the standard
basis vector at `j`. Then, as a function of `z`, the determinant of `x` followed by `z` (against an
identification `e` of the index types) is the determinant of the pairings of `y` with `z`, times
its value at `w`. -/
theorem det_sumElim_eq_det_mul (e : m ⊕ n ≃ ι) {x : m → ι → R} {y w : n → ι → R}
    (hx : LinearMap.ker (Matrix.of y).mulVecLin ≤ Submodule.span R (Set.range x))
    (hw : ∀ j, Matrix.of y *ᵥ w j = Pi.single j 1) (z : n → ι → R) :
    (Matrix.of fun a b ↦ Sum.elim x z a (e b)).det =
      (Matrix.of y * (Matrix.of z).transpose).det *
        (Matrix.of fun a b ↦ Sum.elim x w a (e b)).det := by
  -- Write `z j = ∑ i, B j i • x i + ∑ k, A j k • w k`, with `A j k = y k ⬝ᵥ z j`.
  set A : Matrix n n R := Matrix.of fun j k ↦ y k ⬝ᵥ z j with hA
  have hu : ∀ j, z j - ∑ k, A j k • w k ∈ Submodule.span R (Set.range x) := fun j ↦ hx <| by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, Matrix.mulVec_sum]
    simp_rw [Matrix.mulVec_smul, hw]
    ext k
    simp [hA, Matrix.mulVec, Pi.single_apply]
  choose B hB using fun j ↦ (Submodule.mem_span_range_iff_exists_fun R).1 (hu j)
  have hz : ∀ j, z j = ∑ i, B j i • x i + ∑ k, A j k • w k := fun j ↦ by
    rw [hB j, sub_add_cancel]
  have hM : (Matrix.of fun a b ↦ Sum.elim x z a (e b)) =
      Matrix.fromBlocks 1 0 (Matrix.of B) A * Matrix.of fun a b ↦ Sum.elim x w a (e b) := by
    ext a b
    rcases a with i | j
    · simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    · simp [Matrix.mul_apply, Fintype.sum_sum_type, hz j, Finset.sum_apply]
  have hAt : Aᵀ = Matrix.of y * (Matrix.of z)ᵀ := by
    ext k j
    simp [hA, Matrix.mul_apply, dotProduct]
  rw [hM, Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul, ← hAt,
    Matrix.det_transpose]

end TauCeti.Matrix

namespace Matrix

variable {R : Type*} [CommRing R] {t ι κ : Type*} [Fintype t] [DecidableEq t]

/-- The determinant of the square matrix whose row at `k` is `x i` if `e k = inl i` and `v j` if
`e k = inr j`, as an alternating map of the rows `v`. -/
noncomputable def detRowAlternatingSumElim (e : t ≃ ι ⊕ κ) (x : ι → t → R) :
    (t → R) [⋀^κ]→ₗ[R] R where
  toMultilinearMap :=
    ((detRowAlternating : (t → R) [⋀^t]→ₗ[R] R).toMultilinearMap.domDomCongr e).currySum x
  map_eq_zero_of_eq' v i j hv hij :=
    (detRowAlternating : (t → R) [⋀^t]→ₗ[R] R).map_eq_zero_of_eq _
      (i := e.symm (.inr i)) (j := e.symm (.inr j)) (by simpa using hv) (by simpa using hij)

/-- `Matrix.detRowAlternatingSumElim e x` is the determinant with the rows `x` inserted along
`e`. -/
@[simp]
theorem detRowAlternatingSumElim_apply (e : t ≃ ι ⊕ κ) (x : ι → t → R) (v : κ → t → R) :
    detRowAlternatingSumElim e x v = (of fun k => Sum.elim x v (e k)).det :=
  -- `Matrix.det` is defined as `Matrix.detRowAlternating`.
  (rfl)

end Matrix
