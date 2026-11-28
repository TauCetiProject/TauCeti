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

## Main definitions

* `Matrix.reflMatrix`: the matrix of a simple reflection on the simple roots.
* `Matrix.prod_map_reflMatrix_apply_of_orthogonal`: entry formula for the product of reflection
  matrices over a duplicate-free list of pairwise orthogonal letters.
* `Matrix.coxeterElement`: the product of the simple reflections in the numbering order.
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

/-- Right-multiplying `M` by `reflMatrix A i` subtracts `A q i` times column `i` of `M` from
column `q`. -/
theorem mul_reflMatrix_apply {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : Matrix ι κ ℤ) (A : Matrix κ κ ℤ) (i : κ) (p : ι) (q : κ) :
    (M * reflMatrix A i) p q = M p q - M p i * A q i := by
  simp [Matrix.mul_apply, reflMatrix_apply, mul_sub, mul_ite]

/-- Relabelling a Cartan matrix relabels its simple-reflection matrices. -/
theorem reflMatrix_submatrix {κ : Type*} [DecidableEq κ] {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (e : κ ≃ Fin n) (i : κ) :
    reflMatrix (A.submatrix e e) i = (reflMatrix A (e i)).submatrix e e := by
  ext k j
  simp [reflMatrix, e.injective.eq_iff]

/-- Entry formula for a product of reflection matrices over a duplicate-free list of pairwise
orthogonal letters (`A p q = 0` for distinct `p, q ∈ l`). -/
theorem prod_map_reflMatrix_apply_of_orthogonal {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) {l : List κ} (hl : l.Nodup)
    (horth : ∀ p ∈ l, ∀ q ∈ l, p ≠ q → A p q = 0) (k j : κ) :
    (l.map (reflMatrix A)).prod k j =
      (if k = j then 1 else 0) - if k ∈ l then A j k else 0 := by
  induction l generalizing k j with
  | nil => simp [Matrix.one_apply]
  | cons p l ih =>
    rw [List.nodup_cons] at hl
    have hrow (M : Matrix κ κ ℤ) :
        (reflMatrix A p * M) k j = M k j - if k = p then ∑ m, A m p * M m j else 0 := by
      simp only [Matrix.mul_apply, reflMatrix_apply, sub_mul, Finset.sum_sub_distrib, ite_mul,
        one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      by_cases hkp : k = p <;> simp [hkp]
    rw [List.map_cons, List.prod_cons, hrow]
    simp only [ih hl.2 fun a ha b hb ↦ horth a (.tail p ha) b (.tail p hb)]
    rcases eq_or_ne k p with rfl | hkp
    · simp only [↓reduceIte, hl.1, sub_zero, List.mem_cons, true_or, mul_sub, mul_ite, mul_one,
        mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ]
      rw [Finset.sum_eq_zero fun m _ ↦ by
        split_ifs with hm <;> [rw [horth m (.tail k hm) k List.mem_cons_self
          (ne_of_mem_of_not_mem hm hl.1), zero_mul]; rfl], sub_zero]
    · simp [hkp, List.mem_cons]

/-- The Coxeter element `s₁ s₂ ⋯ sₙ` of a Cartan matrix, in the simple-root basis. -/
@[expose] def coxeterElement {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  ((List.finRange n).map (reflMatrix A)).prod

end Matrix

end
