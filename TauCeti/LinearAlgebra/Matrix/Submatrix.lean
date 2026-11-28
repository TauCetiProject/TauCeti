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
`f : m ↪ n` has a left inverse, its transpose (`Matrix.submatrix_one_mul_submatrix_one`).

Selecting rows or columns of a product selects them in one factor (`Matrix.mul_submatrix_id`,
`Matrix.submatrix_id_mul`, and `Matrix.transpose_map_submatrix_mul` and
`Matrix.transpose_map_submatrix_mul_mul_submatrix` for an entrywise twisted transpose), and a
product with a vector vanishing at the indices `e (β)` of a splitting `e : β ⊕ α ≃ ν` only sees the
columns `e (α)` (`Matrix.mulVec_eq_mulVec_comp_of_comp_eq_zero`).

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

section SelectRowsColumns

variable {l m n p α : Type*} [Fintype m] [Mul α] [AddCommMonoid α]

/-- Selecting the columns `f` of a product selects them in the right factor. -/
theorem mul_submatrix_id (M : Matrix l m α) (N : Matrix m n α) (f : p → n) :
    M * N.submatrix id f = (M * N).submatrix id f := by
  rw [submatrix_mul _ _ _ id _ Function.bijective_id, submatrix_id_id]

/-- Selecting the rows `f` of a product selects them in the left factor. -/
theorem submatrix_id_mul (M : Matrix l m α) (N : Matrix m n α) (f : p → l) :
    M.submatrix f id * N = (M * N).submatrix f id := by
  rw [submatrix_mul _ _ _ id _ Function.bijective_id, submatrix_id_id]

/-- The rows `f` of `(g ^ σ)ᵀ J` are `((g_{·, f}) ^ σ)ᵀ J`, where `^ σ` applies `σ` to every
entry. -/
theorem transpose_map_submatrix_mul {F : Type*} [FunLike F α α] {σ : F} (g : Matrix m l α)
    (J : Matrix m n α) (f : p → l) :
    ((g.submatrix id f).map σ)ᵀ * J = ((g.map σ)ᵀ * J).submatrix f id := by
  rw [← submatrix_id_mul, ← submatrix_map, transpose_submatrix]

/-- With `^ σ` applying `σ` to every entry, `((g_{·, f}) ^ σ)ᵀ J N_{·, h}` is the block `(f, h)` of
`(g ^ σ)ᵀ J N`. -/
theorem transpose_map_submatrix_mul_mul_submatrix {o q : Type*} [Fintype n] {F : Type*}
    [FunLike F α α] {σ : F} (g : Matrix m l α) (J : Matrix m n α) (N : Matrix n o α) (f : p → l)
    (h : q → o) :
    ((g.submatrix id f).map σ)ᵀ * J * N.submatrix id h = ((g.map σ)ᵀ * J * N).submatrix f h := by
  rw [transpose_map_submatrix_mul, ← submatrix_mul _ _ _ _ _ Function.bijective_id]

end SelectRowsColumns

/-- A product `H *ᵥ x`, where `x` vanishes at the indices `e (β)` of a splitting `e : β ⊕ α ≃ ν`,
only involves the columns `e (α)` of `H` and the entries `e (α)` of `x`: `x` is the zero extension
of its entries at `e (α)` (`Matrix.mulVec_extend_zero`). -/
theorem mulVec_eq_mulVec_comp_of_comp_eq_zero {A ν β α m : Type*} [NonUnitalNonAssocSemiring A]
    [Fintype ν] [Fintype α] {H : Matrix m ν A} {x : ν → A} (e : β ⊕ α ≃ ν)
    (hx : x ∘ e ∘ Sum.inl = 0) :
    H *ᵥ x = H.submatrix id (e ∘ Sum.inr) *ᵥ (x ∘ e ∘ Sum.inr) := by
  have hinj : Function.Injective (e ∘ Sum.inr) := e.injective.comp Sum.inr_injective
  have hext : (e ∘ Sum.inr).extend (x ∘ e ∘ Sum.inr) 0 = x := by
    funext j
    obtain ⟨b | a, rfl⟩ := e.surjective j
    · rw [Function.extend_apply' _ _ _ fun ⟨a, ha⟩ ↦ Sum.inr_ne_inl (e.injective ha)]
      exact (congrFun hx b).symm
    · exact hinj.extend_apply _ _ a
  rw [← mulVec_extend_zero hinj, hext]

/-- The `n × m` matrix of an injection `f : m ↪ n` and its transpose compose to the identity of
`m`: the columns of the first are distinct standard basis vectors. -/
theorem submatrix_one_mul_submatrix_one {m n α : Type*} [Fintype n] [DecidableEq m]
    [DecidableEq n] [NonAssocSemiring α] (f : m ↪ n) :
    (1 : Matrix n n α).submatrix f id * (1 : Matrix n n α).submatrix id f = 1 := by
  rw [← submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.one_mul, submatrix_one_embedding]

end Matrix
