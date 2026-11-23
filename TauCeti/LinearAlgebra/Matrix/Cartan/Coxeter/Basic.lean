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

## Main definitions & results

* `Matrix.reflMatrix`: the matrix of a simple reflection on the simple roots.
* `Matrix.coxeterElement`: the product of the simple reflections in the numbering order.
* `Matrix.mul_reflMatrix_apply`: entrywise formula for right-multiplying by a simple reflection.
* `Matrix.mul_coxeterElement`: intertwining `coxeterElement A` with a product of matrices `S i`.
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

/-- Right-multiplying `P` by `reflMatrix A i` subtracts `A j i` times column `i` from column
`j`. -/
theorem mul_reflMatrix_apply {κ : Type*} {n : ℕ} (P : Matrix κ (Fin n) ℤ)
    (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) (r : κ) (j : Fin n) :
    (P * reflMatrix A i) r j = P r j - P r i * A j i := by
  rw [Matrix.mul_apply]
  simp only [reflMatrix_apply, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- The Coxeter element `s₁ s₂ ⋯ sₙ` of a Cartan matrix, in the simple-root basis. -/
@[expose] def coxeterElement {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  ((List.finRange n).map (reflMatrix A)).prod

/-- `P` intertwines `coxeterElement A` with `(List.finRange n).map S |>.prod` when it intertwines
each simple reflection `reflMatrix A i` with `S i`. -/
theorem mul_coxeterElement {κ : Type*} [Fintype κ] [DecidableEq κ] {n : ℕ}
    (P : Matrix κ (Fin n) ℤ) (A : Matrix (Fin n) (Fin n) ℤ) (S : Fin n → Matrix κ κ ℤ)
    (hS : ∀ i, P * reflMatrix A i = S i * P) :
    P * coxeterElement A = ((List.finRange n).map S).prod * P := by
  refine List.rel_prod (R := fun X Y => P * X = Y * P) (by simp)
    (fun X₁ Y₁ h₁ X₂ Y₂ h₂ => ?_)
    (List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr
      (List.forall₂_same.mpr fun i _ => hS i)))
  dsimp only at h₁ h₂ ⊢
  rw [← Matrix.mul_assoc, h₁, Matrix.mul_assoc, h₂, ← Matrix.mul_assoc]

end Matrix

end
