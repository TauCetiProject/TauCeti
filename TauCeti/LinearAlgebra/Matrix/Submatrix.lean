/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Matrix.submatrix` and `Matrix.submatrix_submatrix` occur in the statements and proofs below.
public import Mathlib.LinearAlgebra.Matrix.Defs
-- `Matrix.submatrix_mul` is used by `Matrix.submatrix_one_mul_submatrix_one`.
public import Mathlib.Data.Matrix.Mul
-- `Subgroup` and the group structure on `Equiv.Perm` are used by `TauCeti.matrixSymmetryGroup`.
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.GroupTheory.Perm.Basic

/-!
# Permutations preserving a square matrix

A permutation `σ` of the index set of a square matrix `M` *preserves* `M` when
`M.submatrix σ σ = M`. This file records the three closure properties
`TauCeti.submatrix_perm_refl`, `TauCeti.submatrix_perm_trans` and `TauCeti.submatrix_perm_symm`,
and packages them as the subgroup `TauCeti.matrixSymmetryGroup` of `Equiv.Perm`. It also reads
off the entries of a reindexed matrix: `A.reindex eₘ eₙ = A'` gives `A' (eₘ a) (eₙ b) = A a b`
(`Matrix.apply_apply_of_reindex_eq`), and shows that the `n × m` matrix of an injection
`f : m ↪ n` has a left inverse, its transpose (`Matrix.submatrix_one_mul_submatrix_one`). It also
gives the corank-one left-kernel criterion `Matrix.vecMul_eq_zero_iff_of_null` for a matrix
indexed by `Option α` whose `some × some` submatrix has trivial left kernel.

For the Cartan matrix of a Dynkin diagram these permutations are the diagram symmetries.

## Main definitions

* `TauCeti.matrixSymmetryGroup`: the group of permutations preserving a given square matrix.
-/

public section

namespace TauCeti

variable {B α : Type*} {M : Matrix B B α} {σ τ : Equiv.Perm B}

/-- The identity permutation preserves every square matrix.

This is Mathlib's `Matrix.submatrix_id_id` with the reindexing spelled as `Equiv.refl` rather than
as `id`. The two are equal only by unfolding the coercion `⇑(Equiv.refl B) = id`, which `rw` and
`simp` do not do: a statement carrying `Matrix.submatrix_id_id` where a proof about
`⇑(Equiv.refl B)` is expected is not type-correct at their `implicit` transparency, so no such
statement can be rewritten with. -/
theorem submatrix_perm_refl (M : Matrix B B α) :
    M.submatrix (Equiv.refl B) (Equiv.refl B) = M := by
  rw [Equiv.coe_refl, Matrix.submatrix_id_id]

/-- If `σ` and `τ` preserve a square matrix then so does `σ.trans τ`. -/
theorem submatrix_perm_trans (hσ : M.submatrix σ σ = M) (hτ : M.submatrix τ τ = M) :
    M.submatrix (σ.trans τ) (σ.trans τ) = M := by
  rw [Equiv.coe_trans, ← Matrix.submatrix_submatrix, hτ, hσ]

/-- If `σ` preserves a square matrix then so does `σ.symm`. -/
theorem submatrix_perm_symm (hσ : M.submatrix σ σ = M) : M.submatrix σ.symm σ.symm = M :=
  calc M.submatrix ⇑σ.symm ⇑σ.symm
      = (M.submatrix ⇑σ ⇑σ).submatrix ⇑σ.symm ⇑σ.symm := by rw [hσ]
    _ = M := by rw [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]

/-- **The symmetry group of a square matrix**: the permutations of its index type which leave it
unchanged when both axes are reindexed along them. -/
def matrixSymmetryGroup (M : Matrix B B α) : Subgroup (Equiv.Perm B) where
  carrier := {σ | M.submatrix σ σ = M}
  one_mem' := submatrix_perm_refl M
  mul_mem' hσ hτ := submatrix_perm_trans hτ hσ
  inv_mem' hσ := submatrix_perm_symm hσ

theorem mem_matrixSymmetryGroup_iff : σ ∈ matrixSymmetryGroup M ↔ M.submatrix σ σ = M :=
  Iff.rfl

end TauCeti

namespace Matrix

/-- If `A.reindex eₘ eₙ = A'`, then `A'` has the entry `A a b` at `(eₘ a, eₙ b)`. For a
permutation `σ` with `A.reindex σ σ = A`, this says `A (σ a) (σ b) = A a b`. -/
theorem apply_apply_of_reindex_eq {l m n o α : Type*} {A : Matrix m n α} {A' : Matrix l o α}
    {eₘ : m ≃ l} {eₙ : n ≃ o} (h : A.reindex eₘ eₙ = A') (a : m) (b : n) :
    A' (eₘ a) (eₙ b) = A a b := by
  subst h
  simp

/-- The `n × m` matrix of an injection `f : m ↪ n` and its transpose compose to the identity of
`m`: the columns of the first are distinct standard basis vectors. -/
theorem submatrix_one_mul_submatrix_one {m n α : Type*} [Fintype n] [DecidableEq m]
    [DecidableEq n] [NonAssocSemiring α] (f : m ↪ n) :
    (1 : Matrix n n α).submatrix f id * (1 : Matrix n n α).submatrix id f = 1 := by
  rw [← submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.one_mul, submatrix_one_embedding]

/-- A left null vector `v` of an `Option α`-indexed matrix `A` is `v none • n` whenever `n` is a
left null vector with `n none = 1` and `A.submatrix some some` has trivial left kernel. -/
theorem vecMul_eq_zero_iff_of_null {α R : Type*} [Fintype α] [Ring R]
    {A : Matrix (Option α) (Option α) R} {n v : Option α → R}
    (hsub : ∀ u : α → R, u ᵥ* A.submatrix some some = 0 → u = 0)
    (hn0 : n none = 1) (hnA : n ᵥ* A = 0) :
    v ᵥ* A = 0 ↔ v = v none • n := by
  refine ⟨fun hv ↦ ?_, fun hv ↦ by rw [hv, smul_vecMul, hnA, smul_zero]⟩
  set w := v - v none • n with hw
  have hw0 : w none = 0 := by simp [hw, hn0]
  have hwA : w ᵥ* A = 0 := by rw [hw, sub_vecMul, smul_vecMul, hnA, hv, smul_zero, sub_zero]
  have hfin : (w ∘ some) ᵥ* A.submatrix some some = 0 := by
    ext j
    have := congrFun hwA (some j)
    simpa [vecMul, dotProduct, Fintype.sum_option, hw0] using this
  have hsome := hsub _ hfin
  rw [← sub_eq_zero]
  ext k
  rcases k with _ | i
  · exact hw0
  · exact congrFun hsome i

end Matrix
