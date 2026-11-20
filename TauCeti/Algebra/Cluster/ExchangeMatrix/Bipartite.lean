/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.CartanCompanion
public import TauCeti.Algebra.Cluster.ExchangeMatrix.Mutation
public import TauCeti.LinearAlgebra.Matrix.Cartan.Symmetrizable
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram

/-!
# Bipartite exchange matrices from Cartan data

A two-colouring of a symmetrizable Cartan diagram orients every edge from one colour to the
other. Its signed Cartan entries form a bipartite exchange matrix, with the original Cartan
matrix as companion and the original positive integer symmetrizer. No connectedness or finite
rank is required. In particular, isolated vertices and the empty diagram are admitted.

The row-product definition of bipartite is the one used in the finite-type classification:
all entries of each row have the same weak sign. Mutation at a source or sink only reverses
its incident entries, and therefore leaves the Cartan companion unchanged. These constructions
provide the bipartite matrix representatives needed in ClusterAlgebras §4.1; they do not assume
or prove the classification of finite cluster-variable sets.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras II: Finite type classification*,
  Inventiones Mathematicae 154 (2003), §§1 and 9.
-/

public section

namespace Matrix

/-- An integer matrix is bipartite when each row has a single weak sign. -/
def IsBipartite {I : Type*} (B : Matrix I I ℤ) : Prop :=
  ∀ i j k, 0 ≤ B i j * B i k

/-- The row-product characterization of a bipartite matrix. -/
theorem isBipartite_iff {I : Type*} (B : Matrix I I ℤ) :
    B.IsBipartite ↔ ∀ i j k, 0 ≤ B i j * B i k := by rfl

/-- The row-product condition is equivalent to every row having one weak sign. -/
theorem isBipartite_iff_forall_nonneg_or_nonpos {I : Type*} (B : Matrix I I ℤ) :
    B.IsBipartite ↔ ∀ i, (∀ j, 0 ≤ B i j) ∨ ∀ j, B i j ≤ 0 := by
  classical
  constructor
  · intro h i
    by_cases hi : ∀ j, 0 ≤ B i j
    · exact Or.inl hi
    · obtain ⟨j, hj⟩ := not_forall.mp hi
      refine Or.inr fun k ↦ ?_
      rcases mul_nonneg_iff.mp (h i j k) with h | h
      · exact False.elim (hj h.1)
      · exact h.2
  · intro h i j k
    rcases h i with hi | hi
    · exact mul_nonneg (hi j) (hi k)
    · exact mul_nonneg_of_nonpos_of_nonpos (hi j) (hi k)

namespace IsSkewSymmetrizer

variable {I : Type*} [DecidableEq I] {B : Matrix I I ℤ} {s : I → ℤ}

/-- Away from its incident row and column, mutation at a nonnegative row fixes entries. -/
theorem matrixMutation_apply_of_row_nonneg (h : B.IsSkewSymmetrizer s) {k i j : I}
    (hk : ∀ l, 0 ≤ B k l) (hi : i ≠ k) (hj : j ≠ k) :
    TauCeti.matrixMutation (Function.Embedding.refl I) B k i j = B i j := by
  have hcol : B i k ≤ 0 := by
    exact le_of_not_gt fun hi ↦ (not_lt_of_ge (hk i)) (h.apply_pos_iff.mp hi)
  rw [TauCeti.matrixMutation_apply_of_ne hi hj]
  simp [posPart_eq_zero.mpr hcol, negPart_eq_zero.mpr (hk j)]

/-- Source or sink mutation only reverses the incident entries. -/
theorem matrixMutation_apply_of_row_nonneg_or_nonpos (h : B.IsSkewSymmetrizer s) (k i j : I)
    (hk : (∀ l, 0 ≤ B k l) ∨ ∀ l, B k l ≤ 0) :
    TauCeti.matrixMutation (Function.Embedding.refl I) B k i j =
      if i = k ∨ j = k then -B i j else B i j := by
  split_ifs with hij
  · simp [TauCeti.matrixMutation_apply, hij]
  · obtain ⟨hi, hj⟩ := not_or.mp hij
    rcases hk with hk | hk
    · exact h.matrixMutation_apply_of_row_nonneg hk hi hj
    · have hneg : ∀ l, 0 ≤ (-B) k l := fun l ↦ neg_nonneg.mpr (hk l)
      have heq := h.neg.matrixMutation_apply_of_row_nonneg hneg hi hj
      simpa only [TauCeti.matrixMutation_neg, Matrix.neg_apply, neg_inj] using heq

/-- A source or sink mutation preserves the Cartan companion. -/
theorem cartanCompanion_matrixMutation_of_row_nonneg_or_nonpos
    (h : B.IsSkewSymmetrizer s) (k : I)
    (hk : (∀ l, 0 ≤ B k l) ∨ ∀ l, B k l ≤ 0) :
    (TauCeti.matrixMutation (Function.Embedding.refl I) B k).cartanCompanion =
      B.cartanCompanion := by
  ext i j
  simp only [cartanCompanion_apply]
  split_ifs with hij
  · rfl
  · rw [h.matrixMutation_apply_of_row_nonneg_or_nonpos k i j hk]
    split_ifs <;> simp

end IsSkewSymmetrizer
end Matrix

namespace TauCeti.SymmetrizableDatum

variable {I : Type*} [DecidableEq I] (A : SymmetrizableDatum I)
    (c : (diagramGraph A.cartan).Coloring Bool)

/-- The exchange matrix obtained by orienting a Cartan diagram from true to false. -/
def bipartiteMatrix : Matrix I I ℤ :=
  Matrix.of fun i j ↦ if i = j then 0 else if c i then -A.cartan i j else A.cartan i j

/-- The characteristic entries of the signed Cartan matrix. -/
theorem bipartiteMatrix_apply (i j : I) :
    A.bipartiteMatrix c i j =
      if i = j then 0 else if c i then -A.cartan i j else A.cartan i j := by rfl

/-- The signed Cartan matrix has zero diagonal. -/
@[simp]
theorem bipartiteMatrix_apply_self (i : I) : A.bipartiteMatrix c i i = 0 := by
  simp [bipartiteMatrix_apply]

/-- Off the diagonal, a signed Cartan entry only depends on its row's colour. -/
theorem bipartiteMatrix_apply_of_ne {i j : I} (hij : i ≠ j) :
    A.bipartiteMatrix c i j = if c i then -A.cartan i j else A.cartan i j := by
  simp [bipartiteMatrix_apply, hij]

omit [DecidableEq I] in
/-- Two distinct vertices of the same colour have zero Cartan entry. -/
theorem cartan_apply_eq_zero_of_color_eq {i j : I} (hij : i ≠ j) (hc : c i = c j) :
    A.cartan i j = 0 := by
  by_contra h
  have hji : A.cartan j i ≠ 0 := fun hji ↦ h ((A.zero_comm i j).mpr hji)
  exact c.valid (diagramGraph_adj.mpr ⟨hij, h, hji⟩) hc

/-- No entry joins two vertices in one colour class. -/
theorem bipartiteMatrix_apply_eq_zero_of_color_eq {i j : I} (hc : c i = c j) :
    A.bipartiteMatrix c i j = 0 := by
  by_cases hij : i = j
  · subst j
    simp
  · simp [A.bipartiteMatrix_apply_of_ne c hij, A.cartan_apply_eq_zero_of_color_eq c hij hc]

/-- The original positive integer symmetrizer skew-symmetrizes the signed Cartan matrix. -/
theorem isSkewSymmetrizer_bipartiteMatrix :
    (A.bipartiteMatrix c).IsSkewSymmetrizer (fun i ↦ (A.symmetrizer i : ℤ)) where
  pos i := by exact_mod_cast A.symmetrizer_pos i
  mul_apply i j := by
    by_cases hij : i = j
    · subst j
      simp
    by_cases hc : c i = c j
    · simp [A.bipartiteMatrix_apply_eq_zero_of_color_eq c hc,
        A.bipartiteMatrix_apply_eq_zero_of_color_eq c hc.symm]
    · rw [A.bipartiteMatrix_apply_of_ne c hij,
        A.bipartiteMatrix_apply_of_ne c (Ne.symm hij)]
      have hsymm := A.symmetrizes i j
      cases hci : c i <;> cases hcj : c j <;> simp_all

/-- Forgetting the orientation recovers the original Cartan matrix exactly. -/
@[simp]
theorem cartanCompanion_bipartiteMatrix : (A.bipartiteMatrix c).cartanCompanion = A.cartan := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · rw [Matrix.cartanCompanion_apply_of_ne _ hij, A.bipartiteMatrix_apply_of_ne c hij]
    have hnonpos := A.offDiag_nonpos i j hij
    cases c i <;> simp [abs_of_nonpos hnonpos]

/-- A true-coloured row consists of nonnegative entries. -/
theorem bipartiteMatrix_nonneg {i : I} (hc : c i = true) (j : I) :
    0 ≤ A.bipartiteMatrix c i j := by
  by_cases hij : i = j
  · subst j
    simp
  · simp [A.bipartiteMatrix_apply_of_ne c hij, hc, A.offDiag_nonpos i j hij]

/-- A false-coloured row consists of nonpositive entries. -/
theorem bipartiteMatrix_nonpos {i : I} (hc : c i = false) (j : I) :
    A.bipartiteMatrix c i j ≤ 0 := by
  by_cases hij : i = j
  · subst j
    simp
  · simp [A.bipartiteMatrix_apply_of_ne c hij, hc, A.offDiag_nonpos i j hij]

/-- Every two-coloured symmetrizable Cartan datum yields a bipartite exchange matrix. -/
theorem isBipartite_bipartiteMatrix : (A.bipartiteMatrix c).IsBipartite := by
  intro i j k
  cases hc : c i
  · exact mul_nonneg_of_nonpos_of_nonpos (A.bipartiteMatrix_nonpos c hc j)
      (A.bipartiteMatrix_nonpos c hc k)
  · exact mul_nonneg (A.bipartiteMatrix_nonneg c hc j) (A.bipartiteMatrix_nonneg c hc k)

/-- Mutation at any vertex of the bipartite orientation only reverses incident entries. -/
theorem matrixMutation_bipartiteMatrix_apply (k i j : I) :
    matrixMutation (Function.Embedding.refl I) (A.bipartiteMatrix c) k i j =
      if i = k ∨ j = k then -A.bipartiteMatrix c i j else A.bipartiteMatrix c i j := by
  apply (A.isSkewSymmetrizer_bipartiteMatrix c).matrixMutation_apply_of_row_nonneg_or_nonpos
  cases hc : c k
  · exact Or.inr (A.bipartiteMatrix_nonpos c hc)
  · exact Or.inl (A.bipartiteMatrix_nonneg c hc)

/-- Every initial source or sink mutation preserves the given Cartan companion. -/
theorem cartanCompanion_matrixMutation_bipartiteMatrix (k : I) :
    (matrixMutation (Function.Embedding.refl I) (A.bipartiteMatrix c) k).cartanCompanion =
      A.cartan := by
  have h := (A.isSkewSymmetrizer_bipartiteMatrix c)
  rw [h.cartanCompanion_matrixMutation_of_row_nonneg_or_nonpos k,
    A.cartanCompanion_bipartiteMatrix c]
  cases hc : c k
  · exact Or.inr (A.bipartiteMatrix_nonpos c hc)
  · exact Or.inl (A.bipartiteMatrix_nonneg c hc)

end TauCeti.SymmetrizableDatum
