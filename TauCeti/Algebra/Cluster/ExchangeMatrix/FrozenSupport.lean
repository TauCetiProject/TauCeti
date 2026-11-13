/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Mutation
public import Mathlib.Data.Finsupp.Basic

/-!
# Finite support of frozen exchange-matrix columns

Extended matrices have rows `K ⊕ J` and mutable columns `K`, along
`Function.Embedding.inl : K ↪ K ⊕ J`. The frozen column at `k : K` means the frozen-row
entries `j ↦ B.matrix (Sum.inr j) k`. Columnwise finite support encodes tropical coefficients
over a possibly infinite frozen set `J`. Mutation preserves this condition and the vanishing
of each frozen row. With `HasFiniteFrozenSupport` and finitely many mutable directions,
some finite subset of `J` contains all nonzero frozen rows throughout any mutation sequence.
-/

public section

namespace TauCeti.ExchangeMatrix

variable {K K' K'' J J' J'' : Type*}

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
@[simp]
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
        Function.support fun j ↦ B.matrix (Sum.inr j) k :=
  fun _ hj ↦ by
    simpa only [Set.mem_union, Function.mem_support] using
      support_matrixMutation_subset Function.Embedding.inl B.matrix k l
        (by simpa only [Function.mem_support, mutation_matrix] using hj)

/-- Matrix mutation preserves finite support of every frozen column. -/
theorem HasFiniteFrozenSupport.mutation [DecidableEq K] [DecidableEq J]
    {B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)}
    (h : B.HasFiniteFrozenSupport) (k : K) : (B.mutation k).HasFiniteFrozenSupport :=
  fun l ↦ ((h l).union (h k)).subset (B.support_mutation_frozen_subset k l)

/-- Mutation preserves and reflects columnwise finite frozen support. -/
@[simp]
theorem hasFiniteFrozenSupport_mutation_iff [DecidableEq K] [DecidableEq J]
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)) (k : K) :
    (B.mutation k).HasFiniteFrozenSupport ↔ B.HasFiniteFrozenSupport :=
  ⟨fun h ↦ by simpa using h.mutation k, fun h ↦ h.mutation k⟩

/-- Mutation negates the frozen exponent vector in its own direction, independently of
which finiteness proofs are supplied. -/
@[simp]
theorem frozenColumn_mutation_self [DecidableEq K] [DecidableEq J]
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)) (k : K)
    (h : (B.mutation k).HasFiniteFrozenSupport) :
    (B.mutation k).frozenColumn h k =
      -B.frozenColumn ((B.hasFiniteFrozenSupport_mutation_iff k).mp h) k := by
  ext j
  simp

/-- Injectively restricting frozen rows, and arbitrarily restricting or relabelling mutable
columns, preserves columnwise finite frozen support. -/
theorem HasFiniteFrozenSupport.submatrix
    {B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)}
    (h : B.HasFiniteFrozenSupport) (g : K' → K) {fJ : J' → J}
    (hfJ : Function.Injective fJ)
    (hcompat : ∀ k, Sum.map g fJ (Function.Embedding.inl k) = Function.Embedding.inl (g k)) :
    (B.submatrix (Sum.map g fJ) g hcompat).HasFiniteFrozenSupport := by
  intro k
  simpa only [Function.support, Set.preimage_ofPred_eq, submatrix_matrix,
    Matrix.submatrix_apply, Sum.map_inr] using (h (g k)).preimage hfJ.injOn

/-- Simultaneous mutable and frozen relabelling preserves finite frozen support. -/
@[simp]
theorem hasFiniteFrozenSupport_reindex_iff (eK : K ≃ K') (eJ : J ≃ J')
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)) :
    (reindex (row' := Function.Embedding.inl) (Equiv.sumCongr eK eJ) eK
      (fun _ ↦ by
        simp only [Function.Embedding.inl_apply, Equiv.sumCongr_apply, Sum.map_inl])
      B).HasFiniteFrozenSupport ↔ B.HasFiniteFrozenSupport := by
  let C : ExchangeMatrix (Function.Embedding.inl : K' ↪ K' ⊕ J') :=
    reindex (Equiv.sumCongr eK eJ) eK (fun _ ↦ by simp) B
  change C.HasFiniteFrozenSupport ↔ B.HasFiniteFrozenSupport
  have hCm : C.matrix = B.matrix.submatrix (Equiv.sumCongr eK eJ).symm eK.symm :=
    B.reindex_matrix _ _ _
  constructor
  · intro h k
    have hs := (h.submatrix eK eJ.injective (fun _ ↦ rfl)) k
    rw [C.submatrix_matrix (Sum.map eK eJ) eK (fun _ ↦ rfl), hCm] at hs
    simpa only [Matrix.submatrix_apply, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
      Sum.map_inr, Equiv.symm_apply_apply] using hs
  · intro h k
    rw [hCm]
    have hs := (h.submatrix eK.symm eJ.symm.injective (fun _ ↦ rfl)) k
    rw [B.submatrix_matrix (Sum.map eK.symm eJ.symm) eK.symm (fun _ ↦ rfl)] at hs
    simpa only [Matrix.submatrix_apply, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
      Sum.map_inr] using hs

/-- Every finite mutation sequence preserves and reflects finite frozen support. -/
@[simp]
theorem hasFiniteFrozenSupport_foldl_mutation_iff [DecidableEq K] [DecidableEq J]
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)) (w : List K) :
    (w.foldl (fun C k ↦ C.mutation k) B).HasFiniteFrozenSupport ↔ B.HasFiniteFrozenSupport := by
  induction w generalizing B with
  | nil => rfl
  | cons k w ih =>
    simpa only [List.foldl_cons] using (ih (B.mutation k)).trans
      (B.hasFiniteFrozenSupport_mutation_iff k)

/-- Frozen exponent vectors reindex by relabelling their frozen coordinates, while their
mutable column is pulled back. The reindexed matrix's finiteness proof is arbitrary. -/
@[simp]
theorem frozenColumn_reindex (eK : K ≃ K') (eJ : J ≃ J')
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J))
    (h' : (reindex (row' := Function.Embedding.inl) (Equiv.sumCongr eK eJ) eK
      (fun _ ↦ by simp) B).HasFiniteFrozenSupport) (k : K') :
    (reindex (row' := Function.Embedding.inl) (Equiv.sumCongr eK eJ) eK
      (fun _ ↦ by simp) B).frozenColumn h' k =
      Finsupp.equivMapDomain eJ
        (B.frozenColumn ((B.hasFiniteFrozenSupport_reindex_iff eK eJ).mp h') (eK.symm k)) := by
  ext j
  simp [Finsupp.equivMapDomain_apply]

/-- Relabelling equivalence on finite-support extended matrices. It restricts the existing
exchange-matrix reindexing equivalence, without changing its action. -/
noncomputable def reindexFiniteFrozen (eK : K ≃ K') (eJ : J ≃ J') :
    {B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J) // B.HasFiniteFrozenSupport} ≃
      {B : ExchangeMatrix (Function.Embedding.inl : K' ↪ K' ⊕ J') //
        B.HasFiniteFrozenSupport} :=
  (reindex (row' := Function.Embedding.inl) (Equiv.sumCongr eK eJ) eK
    (fun _ ↦ by
        simp only [Function.Embedding.inl_apply, Equiv.sumCongr_apply, Sum.map_inl])).subtypeEquiv
    fun B ↦ (B.hasFiniteFrozenSupport_reindex_iff eK eJ).symm

@[simp]
theorem reindexFiniteFrozen_val (eK : K ≃ K') (eJ : J ≃ J')
    (B : {B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J) //
      B.HasFiniteFrozenSupport}) :
    (reindexFiniteFrozen eK eJ B).val =
      reindex (row' := Function.Embedding.inl) (Equiv.sumCongr eK eJ) eK
        (fun _ ↦ by
        simp only [Function.Embedding.inl_apply, Equiv.sumCongr_apply, Sum.map_inl]) B.val :=
  (rfl)

@[simp]
theorem reindexFiniteFrozen_refl :
    reindexFiniteFrozen (Equiv.refl K) (Equiv.refl J) =
      Equiv.refl {B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J) //
        B.HasFiniteFrozenSupport} := by
  apply Equiv.ext
  intro B
  apply Subtype.ext
  ext : 1
  · ext i k
    cases i <;> simp
  · simp

/-- Relabellings of finite-support matrices compose as the corresponding index equivalences. -/
theorem reindexFiniteFrozen_trans (eK : K ≃ K') (eJ : J ≃ J')
    (eK' : K' ≃ K'') (eJ' : J' ≃ J'') :
    (reindexFiniteFrozen eK eJ).trans (reindexFiniteFrozen eK' eJ') =
      reindexFiniteFrozen (eK.trans eK') (eJ.trans eJ') := by
  apply Equiv.ext
  intro B
  apply Subtype.ext
  ext : 1
  · ext i k
    cases i <;> simp
  · simp [Function.comp_assoc]

@[simp]
theorem reindexFiniteFrozen_symm (eK : K ≃ K') (eJ : J ≃ J') :
    (reindexFiniteFrozen eK eJ).symm = reindexFiniteFrozen eK.symm eJ.symm := by
  apply Equiv.ext
  intro B
  apply Subtype.ext
  ext : 1
  · ext i k
    cases i <;> simp [reindexFiniteFrozen]
  · simp [reindexFiniteFrozen]

/-- The finite set of initially nonzero frozen rows, for finitely many mutable directions.
Its coercion to a type supplies the finite frozen carrier of the geometric coefficient reduction. -/
noncomputable def frozenSupport [Finite K]
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J))
    (h : B.HasFiniteFrozenSupport) : Finset J :=
  (Set.finite_iUnion h).toFinset

@[simp]
theorem mem_frozenSupport_iff [Finite K]
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J))
    (h : B.HasFiniteFrozenSupport) (j : J) :
    j ∈ B.frozenSupport h ↔ ∃ k, B.matrix (Sum.inr j) k ≠ 0 := by
  simp [frozenSupport, Function.mem_support]

/-- The finite set of nonzero frozen rows is invariant under mutation, independently of the
finiteness proof supplied after mutation. -/
@[simp]
theorem frozenSupport_mutation [Finite K] [DecidableEq K] [DecidableEq J]
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)) (k : K)
    (h : (B.mutation k).HasFiniteFrozenSupport) :
    (B.mutation k).frozenSupport h =
      B.frozenSupport ((B.hasFiniteFrozenSupport_mutation_iff k).mp h) := by
  ext j
  simpa only [mem_frozenSupport_iff, not_forall] using
    not_congr (B.mutation_row_eq_zero_iff k (Sum.inr j))

/-- A finite mutation sequence retains precisely the initial set of nonzero frozen rows. -/
@[simp]
theorem frozenSupport_foldl_mutation [Finite K] [DecidableEq K] [DecidableEq J]
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)) (w : List K)
    (h : (w.foldl (fun C k ↦ C.mutation k) B).HasFiniteFrozenSupport) :
    (w.foldl (fun C k ↦ C.mutation k) B).frozenSupport h =
      B.frozenSupport ((B.hasFiniteFrozenSupport_foldl_mutation_iff w).mp h) := by
  ext j
  simpa only [mem_frozenSupport_iff, not_forall] using
    not_congr (B.foldl_mutation_row_eq_zero_iff w (Sum.inr j))

/-- Every entry outside the canonical finite set of initially nonzero frozen rows vanishes. -/
theorem matrix_inr_eq_zero_of_not_mem_frozenSupport [Finite K]
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J))
    (h : B.HasFiniteFrozenSupport) {j : J} (hj : j ∉ B.frozenSupport h) (k : K) :
    B.matrix (Sum.inr j) k = 0 := by
  have hz : ∀ k, B.matrix (Sum.inr j) k = 0 := by
    simpa only [mem_frozenSupport_iff, not_exists, not_not] using hj
  exact hz k

/-- Frozen rows outside the canonical finite carrier remain zero through every mutation word. -/
theorem foldl_mutation_frozen_row_eq_zero_of_not_mem_frozenSupport
    [Finite K] [DecidableEq K] [DecidableEq J]
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J))
    (h : B.HasFiniteFrozenSupport) (w : List K) {j : J} (hj : j ∉ B.frozenSupport h) :
    ∀ l, (w.foldl (fun C k ↦ C.mutation k) B).matrix (Sum.inr j) l = 0 :=
  (B.foldl_mutation_row_eq_zero_iff w (Sum.inr j)).2
    (B.matrix_inr_eq_zero_of_not_mem_frozenSupport h hj)

end TauCeti.ExchangeMatrix
