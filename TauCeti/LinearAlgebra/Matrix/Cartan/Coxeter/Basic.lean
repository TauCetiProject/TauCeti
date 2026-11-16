/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-!
# Coxeter elements of Cartan matrices: the matrix layer

In the basis of simple roots, the simple reflection `sᵢ` acts by `sᵢ αⱼ = αⱼ - A j i • αᵢ`, where
`A` is the Cartan matrix in Mathlib's convention `b.cartanMatrix i j = ⟨αᵢ, αⱼ^∨⟩`. The Coxeter
element is `c = s₁ s₂ ⋯ sᵣ`.

Both definitions expose their bodies, because the order and the annihilating polynomial of a Coxeter
element of an exceptional type are computed by the kernel on explicit integer matrices.

A realization of a Cartan matrix `A = Pᵀ * Q` by roots, the columns of `P`, and coroots, the
columns of `Q`, in a lattice `ℤ ^ m` turns each simple reflection into the ambient reflection
`1 - vecMulVec (P.col i) (Q.col i)`, and `P` intertwines the ambient reflections with the
simple-reflection matrices. When `P` is square with nonzero determinant, the Coxeter element is
therefore similar over `ℚ` to the product of the ambient reflections, which is how its order and
characteristic polynomial are computed for the classical types.

## Main definitions

* `Matrix.reflMatrix`: the matrix of a simple reflection on the simple roots.
* `Matrix.coxeterElement`: the product of the simple reflections in the numbering order.

## Main results

* `Matrix.one_sub_vecMulVec_mul_eq_mul_reflMatrix`: `P` intertwines the ambient reflection in the
  `i`-th root with `reflMatrix (Pᵀ * Q) i`.
* `Matrix.prod_map_one_sub_vecMulVec_mul_eq_mul_coxeterElement`: `P` intertwines the product of
  the ambient reflections with the Coxeter element of `Pᵀ * Q`.
-/

public section

namespace Matrix

/-- The simple reflection `sᵢ` in the simple-root basis: `sᵢ αⱼ = αⱼ - A j i • αᵢ`. -/
@[expose] def reflMatrix {κ : Type*} [DecidableEq κ] (A : Matrix κ κ ℤ) (i : κ) : Matrix κ κ ℤ :=
  Matrix.of fun k j => (if k = j then 1 else 0) - (if k = i then A j i else 0)

/-- The entries of the simple reflection `sᵢ` in the simple-root basis. -/
@[simp]
theorem reflMatrix_apply {κ : Type*} [DecidableEq κ] (A : Matrix κ κ ℤ) (i k j : κ) :
    reflMatrix A i k j = (if k = j then 1 else 0) - (if k = i then A j i else 0) :=
  (rfl)

/-- Relabelling a Cartan matrix relabels its simple-reflection matrices. -/
theorem reflMatrix_submatrix {κ : Type*} [DecidableEq κ] {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (e : κ ≃ Fin n) (i : κ) :
    reflMatrix (A.submatrix e e) i = (reflMatrix A (e i)).submatrix e e := by
  ext k j
  simp [reflMatrix, e.injective.eq_iff]

/-- The Coxeter element `s₁ s₂ ⋯ sₙ` of a Cartan matrix, in the simple-root basis. -/
@[expose] def coxeterElement {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  ((List.finRange n).map (reflMatrix A)).prod

/-- **Ambient reflections realize the simple reflections.** If the Cartan matrix is `Pᵀ * Q`, with
the roots as the columns of `P` and the coroots as the columns of `Q`, then `P` intertwines the
reflection `x ↦ x - ⟨x, Q.col i⟩ • P.col i` of the ambient lattice with `reflMatrix (Pᵀ * Q) i`. -/
theorem one_sub_vecMulVec_mul_eq_mul_reflMatrix {m κ : Type*} [Fintype m] [DecidableEq m]
    [Fintype κ] [DecidableEq κ] (P Q : Matrix m κ ℤ) (i : κ) :
    (1 - vecMulVec (P.col i) (Q.col i)) * P = P * reflMatrix (Pᵀ * Q) i := by
  rw [Matrix.sub_mul, Matrix.one_mul, vecMulVec_mul]
  ext k j
  simp only [Matrix.sub_apply, vecMulVec_apply, col_apply, Matrix.mul_apply, reflMatrix_apply,
    transpose_apply, vecMul, dotProduct, mul_sub, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.mul_sum]
  exact congrArg _ (Finset.sum_congr rfl fun _ _ => by ring)

/-- Products of ambient reflections realize the corresponding words in the simple reflections. -/
theorem prod_map_one_sub_vecMulVec_mul_eq_mul_prod_map_reflMatrix {m κ : Type*} [Fintype m]
    [DecidableEq m] [Fintype κ] [DecidableEq κ] (P Q : Matrix m κ ℤ) (l : List κ) :
    (l.map fun i => 1 - vecMulVec (P.col i) (Q.col i)).prod * P =
      P * (l.map (reflMatrix (Pᵀ * Q))).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, Matrix.mul_assoc, ih, ← Matrix.mul_assoc,
      one_sub_vecMulVec_mul_eq_mul_reflMatrix, Matrix.mul_assoc, List.map_cons, List.prod_cons]

/-- **The Coxeter element is realized by the product of the ambient reflections**: `P`
intertwines `∏ᵢ (1 - vecMulVec (P.col i) (Q.col i))`, in the numbering order, with the Coxeter
element of the Cartan matrix `Pᵀ * Q`. -/
theorem prod_map_one_sub_vecMulVec_mul_eq_mul_coxeterElement {m : Type*} [Fintype m]
    [DecidableEq m] {n : ℕ}
    (P Q : Matrix m (Fin n) ℤ) :
    ((List.finRange n).map fun i => 1 - vecMulVec (P.col i) (Q.col i)).prod * P =
      P * coxeterElement (Pᵀ * Q) :=
  prod_map_one_sub_vecMulVec_mul_eq_mul_prod_map_reflMatrix P Q _

end Matrix

end
