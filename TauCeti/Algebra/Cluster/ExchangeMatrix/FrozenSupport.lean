/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Mutation

/-!
# Finite support of frozen exchange-matrix columns

Each column may have finite frozen support even when the frozen index type is infinite.
Mutation preserves this condition and leaves every initially zero frozen row zero.
For finitely many mutable directions, all mutation words remain supported in one finite set.
-/

public section

namespace TauCeti.ExchangeMatrix

variable {K K' J J' : Type*}

/-- Each frozen column has finite support. A single finite set supporting all frozen columns
is not required or guaranteed. -/
def HasFiniteFrozenSupport (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)) : Prop :=
  ∀ k, (Function.support fun j ↦ B.matrix (Sum.inr j) k).Finite

/-- Finite frozen support is the columnwise finite-support condition. -/
theorem hasFiniteFrozenSupport_iff
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)) :
    B.HasFiniteFrozenSupport ↔
      ∀ k, (Function.support fun j ↦ B.matrix (Sum.inr j) k).Finite := by rfl

/-- A finite frozen index type makes every frozen column finitely supported. -/
theorem hasFiniteFrozenSupport_of_finite [Finite J]
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)) :
    B.HasFiniteFrozenSupport :=
  fun _ ↦ Set.toFinite _

/-- Read a frozen column as a finitely supported exponent vector. -/
noncomputable def frozenColumn (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J))
    (h : B.HasFiniteFrozenSupport) (k : K) : J →₀ ℤ :=
  Finsupp.ofSupportFinite (fun j ↦ B.matrix (Sum.inr j) k) (h k)

@[simp]
theorem frozenColumn_apply (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J))
    (h : B.HasFiniteFrozenSupport) (k : K) (j : J) :
    B.frozenColumn h k j = B.matrix (Sum.inr j) k :=
  (rfl)

/-- Every entry in a mutated frozen column is supported on the union of that column's
old support and the mutation column's old support. -/
theorem support_mutation_frozen_subset [DecidableEq K] [DecidableEq J]
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)) (k l : K) :
    (Function.support fun j ↦ (B.mutation k).matrix (Sum.inr j) l) ⊆
      (Function.support fun j ↦ B.matrix (Sum.inr j) l) ∪
        Function.support fun j ↦ B.matrix (Sum.inr j) k := by
  intro j hj
  by_contra h
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
  exact hj (by simp [mutation_matrix, matrixMutation_apply, h.1, h.2])

/-- Matrix mutation preserves finite support of every frozen column. -/
theorem HasFiniteFrozenSupport.mutation [DecidableEq K] [DecidableEq J]
    {B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)}
    (h : B.HasFiniteFrozenSupport) (k : K) : (B.mutation k).HasFiniteFrozenSupport :=
  fun l ↦ ((h l).union (h k)).subset (B.support_mutation_frozen_subset k l)

/-- An initially zero frozen row is fixed by mutation. -/
theorem mutation_frozen_row_eq_zero [DecidableEq K] [DecidableEq J]
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)) {j : J}
    (h : ∀ l, B.matrix (Sum.inr j) l = 0) (k l : K) :
    (B.mutation k).matrix (Sum.inr j) l = 0 := by
  simp [mutation_matrix, matrixMutation_apply, h]

/-- Simultaneous mutable and frozen relabelling preserves finite frozen support. -/
theorem hasFiniteFrozenSupport_reindex_iff (eK : K ≃ K') (eJ : J ≃ J')
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)) :
    (reindex (row' := Function.Embedding.inl) (Equiv.sumCongr eK eJ) eK
      (fun _ ↦ by
        simp only [Function.Embedding.inl_apply, Equiv.sumCongr_apply, Sum.map_inl])
      B).HasFiniteFrozenSupport ↔ B.HasFiniteFrozenSupport := by
  constructor
  · intro h k
    have hf := (h (eK k)).preimage eJ.injective.injOn
    simpa only [Function.support, Set.preimage_ofPred_eq, reindex_matrix,
      Matrix.submatrix_apply, Equiv.sumCongr_symm,
      Equiv.sumCongr_apply, Sum.map_inr, Equiv.symm_apply_apply] using hf
  · intro h k
    simpa only [Function.support, Set.preimage_ofPred_eq, reindex_matrix,
      Matrix.submatrix_apply, Equiv.sumCongr_symm,
      Equiv.sumCongr_apply, Sum.map_inr] using
      (h (eK.symm k)).preimage eJ.symm.injective.injOn

/-- A specified initially zero frozen row stays zero after any finite sequence of actual
matrix mutations. This requires no finiteness of either index type. -/
theorem foldl_mutation_frozen_row_eq_zero [DecidableEq K] [DecidableEq J]
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)) {j : J}
    (h : ∀ l, B.matrix (Sum.inr j) l = 0) (w : List K) (l : K) :
    (w.foldl (fun C k ↦ C.mutation k) B).matrix (Sum.inr j) l = 0 := by
  induction w generalizing B with
  | nil => exact h l
  | cons k _w ih => exact ih (B.mutation k) (B.mutation_frozen_row_eq_zero h k)

/-- For finitely many mutable directions, one finite set of initially active frozen rows
contains every active frozen row after any finite sequence of mutations. -/
theorem exists_finset_frozen_support_foldl [Finite K] [DecidableEq K] [DecidableEq J]
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J))
    (h : B.HasFiniteFrozenSupport) :
    ∃ S : Finset J, ∀ w : List K, ∀ j ∉ S, ∀ l,
      (w.foldl (fun C k ↦ C.mutation k) B).matrix (Sum.inr j) l = 0 := by
  classical
  have hf : (⋃ k, Function.support fun j ↦ B.matrix (Sum.inr j) k).Finite :=
    Set.finite_iUnion h
  refine ⟨hf.toFinset, fun w j hj l ↦ ?_⟩
  apply B.foldl_mutation_frozen_row_eq_zero _ w l
  have hnot : j ∉ ⋃ k, Function.support fun j ↦ B.matrix (Sum.inr j) k := by
    simpa using hj
  simpa only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] using hnot

end TauCeti.ExchangeMatrix
