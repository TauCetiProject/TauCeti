/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic

/-!
# Products with the matrix of a partial map on indices

A partial map on basis indices, given by a map `σ : n → m` defined on the indices satisfying a
predicate `p`, has the `0`/`1` matrix `X` with `X a b = if p b ∧ a = σ b then 1 else 0`: column
`b` is the standard basis vector at `σ b` when `p b` holds, and zero otherwise. Raising and
lowering matrices of a weight basis have this shape, with `σ` a reflection of the indices.

The lemmas here evaluate the matrix products with such an `X` entrywise. Multiplying by `X` on the
right selects a column; multiplying on the left selects a row once `σ` is an involution, so that
`a = σ b` exactly when `b = σ a`; and the combination `∑ d, X d c • N d` of a family of matrices
selects the member at `σ c`.

Mathlib's `PEquiv.toMatrix_mul_apply` and `PEquiv.mul_toMatrix_apply` are the corresponding
statements for the matrix of a bundled partial equivalence; the lemmas here take the entries of
`X` as a hypothesis instead, as they arise from explicit raising and lowering matrices.

## Main results

* `Matrix.mul_apply_of_apply_eq_ite_left`: the entries of `X * N` for an involution `σ`.
* `Matrix.mul_apply_of_apply_eq_ite_right`: the entries of `N * X`.
* `Matrix.sum_smul_apply_of_apply_eq_ite`: the entries of `∑ d, X d c • N d`.
-/

public section

namespace Matrix

variable {l m n o α : Type*} [NonAssocSemiring α] {p : n → Prop} [DecidablePred p]

/-- Multiplying on the left by the matrix of an involutive partial map `σ` on indices picks out
row `σ a`, provided `σ a` lies in the domain. -/
theorem mul_apply_of_apply_eq_ite_left [Fintype n] [DecidableEq n] {X : Matrix n n α}
    {σ : n → n} (hσ : Function.Involutive σ) (hX : ∀ a b, X a b = if p b ∧ a = σ b then 1 else 0)
    (N : Matrix n o α) (a : n) (b : o) : (X * N) a b = if p (σ a) then N (σ a) b else 0 := by
  rw [mul_apply, Finset.sum_eq_single (σ a)]
  · simp [hX, hσ a]
  · intro k _ hk
    rw [hX]
    split_ifs with h
    · exact absurd (by rw [h.2, hσ]) hk
    · exact zero_mul _
  · simp

/-- Multiplying on the right by the matrix of a partial map `σ` on indices picks out column `σ b`,
provided `b` lies in the domain. -/
theorem mul_apply_of_apply_eq_ite_right [Fintype m] [DecidableEq m] {X : Matrix m n α} {σ : n → m}
    (hX : ∀ a b, X a b = if p b ∧ a = σ b then 1 else 0) (N : Matrix l m α) (a : l) (b : n) :
    (N * X) a b = if p b then N a (σ b) else 0 := by
  rw [mul_apply, Finset.sum_eq_single (σ b)]
  · simp [hX]
  · intro k _ hk
    rw [hX]
    split_ifs with h
    · exact absurd h.2 hk
    · exact mul_zero _
  · simp

/-- Combining a family of matrices with the coefficients of column `c` of the matrix of a partial
map `σ` on indices picks out the member at `σ c`, provided `c` lies in the domain. -/
theorem sum_smul_apply_of_apply_eq_ite [Fintype m] [DecidableEq m] {X : Matrix m n α} {σ : n → m}
    (hX : ∀ a b, X a b = if p b ∧ a = σ b then 1 else 0) (N : m → Matrix l o α) (c : n) (a : l)
    (b : o) : (∑ d, X d c • N d) a b = if p c then N (σ c) a b else 0 := by
  rw [Matrix.sum_apply, Finset.sum_eq_single (σ c)]
  · simp [hX]
  · intro d _ hd
    rw [smul_apply, hX]
    split_ifs with h
    · exact absurd h.2 hd
    · exact zero_smul _ _
  · simp

end Matrix
