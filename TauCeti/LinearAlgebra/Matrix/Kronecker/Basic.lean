/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Diagonal matrices constant on blocks, acting on Kronecker products with matrix units

A function `ε` on the block indices `l` gives the diagonal matrix `diagonal (fun p ↦ ε p.1)` on
`l × m`, which is `ε a` times the identity on the block of `a`. It acts on a matrix
`single a b c ⊗ₖ X` supported in the single block `(a, b)` by the scalar `ε a` on the left and
`ε b` on the right.

## Main results

* `TauCeti.diagonal_mul_single_kronecker`: the left action, by `ε a`.
* `TauCeti.single_kronecker_mul_diagonal`: the right action, by `ε b`.
-/

public section

open Matrix
open scoped Kronecker

namespace TauCeti

variable {l m n p α : Type*} [DecidableEq l] [DecidableEq n]

/-- A diagonal matrix constant on the blocks of `l × m` acts on the left of a matrix supported in
the block row of `a` by its value `ε a` on that block. -/
theorem diagonal_mul_single_kronecker [Fintype l] [Fintype m] [DecidableEq m] [Semiring α]
    (ε : l → α) (a : l) (b : n) (c : α) (X : Matrix m p α) :
    diagonal (fun x : l × m ↦ ε x.1) * (single a b c ⊗ₖ X) = ε a • (single a b c ⊗ₖ X) := by
  ext ⟨i, r⟩ ⟨j, s⟩
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · simp [h]

/-- A diagonal matrix constant on the blocks of `n × p` acts on the right of a matrix supported in
the block column of `b` by its value `ε b` on that block. -/
theorem single_kronecker_mul_diagonal [Fintype n] [Fintype p] [DecidableEq p]
    [CommSemiring α] (ε : n → α) (a : l) (b : n) (c : α) (X : Matrix m p α) :
    (single a b c ⊗ₖ X) * diagonal (fun x : n × p ↦ ε x.1) = ε b • (single a b c ⊗ₖ X) := by
  ext ⟨i, r⟩ ⟨j, s⟩
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    simp [mul_comm]
  · simp [h]

end TauCeti
