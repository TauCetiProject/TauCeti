/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.PartialCorrelation.Powers
public import TauCeti.Data.Fintype.Fiber

/-!
# Powers of partial-correlation Gram entries

A monomial in entries of the partial-correlation Gram matrix expands into a finite sum of
monomials in entries of its lower-triangular Cholesky factor. The expansion is indexed by choosing
one admissible Cholesky column for every occurrence of every Gram entry. Its Cholesky multi-index
is the occurrence count of the two row-column factors selected by each choice.
-/

public section

noncomputable section

open scoped BigOperators

namespace TauCeti

variable {p : ℕ}

/-- A choice of a Cholesky column for every occurrence in a Gram-entry monomial. -/
abbrev partialCorrelationGramExpansionChoice (n : Fin p × Fin p → ℕ) :=
  (ij : Fin p × Fin p) → Fin (n ij) → Finset.Iic ij.2

/-- The Cholesky entry selected by one side of one occurrence in a Gram expansion. -/
def partialCorrelationGramExpansionFactor {n : Fin p × Fin p → ℕ}
    (c : partialCorrelationGramExpansionChoice n)
    (a : (Σ ij, Fin (n ij)) × Fin 2) : Fin p × Fin p :=
  (if a.2 = 0 then a.1.1.1 else a.1.1.2, c a.1.1 a.1.2)

/-- The Cholesky multi-index of a term in the Gram-entry monomial expansion. -/
def partialCorrelationGramExpansionPower {n : Fin p × Fin p → ℕ}
    (c : partialCorrelationGramExpansionChoice n) (q : Fin p × Fin p) : ℕ :=
  Function.occCount (partialCorrelationGramExpansionFactor c) q

/-- A selected Gram-expansion term, written first as paired factors and then as a Cholesky
monomial, has the multi-index given by `partialCorrelationGramExpansionPower`. -/
theorem prod_selected_partialCorrelationCholesky_eq_prod_pow
    (z : strictLowerTriangle p → ℝ) (n : Fin p × Fin p → ℕ)
    (c : partialCorrelationGramExpansionChoice n) :
    (∏ a : Σ ij, Fin (n ij),
      partialCorrelationCholesky z a.1.1 (c a.1 a.2) *
        partialCorrelationCholesky z a.1.2 (c a.1 a.2)) =
      ∏ q, partialCorrelationCholesky z q.1 q.2 ^
        partialCorrelationGramExpansionPower c q := by
  classical
  unfold partialCorrelationGramExpansionPower
  rw [Function.prod_occCount_pow (T := Finset.univ) _ (fun _ ↦ Finset.mem_univ _)]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro ij _
  rw [Fin.prod_univ_two]
  rfl

/-- A monomial in partial-correlation Gram entries is the finite sum of the Cholesky monomials
obtained by choosing one admissible column for each occurrence of each Gram entry. -/
theorem prod_pow_partialCorrelationGram_eq_sum
    (z : strictLowerTriangle p → ℝ) (n : Fin p × Fin p → ℕ) :
    (∏ ij, partialCorrelationGram z ij.1 ij.2 ^ n ij) =
      ∑ c : partialCorrelationGramExpansionChoice n,
        ∏ q, partialCorrelationCholesky z q.1 q.2 ^
          partialCorrelationGramExpansionPower c q := by
  classical
  have hentry (ij : Fin p × Fin p) :
      partialCorrelationGram z ij.1 ij.2 ^ n ij =
        ∑ c : Fin (n ij) → Finset.Iic ij.2, ∏ r,
          partialCorrelationCholesky z ij.1 (c r) *
            partialCorrelationCholesky z ij.2 (c r) := by
    rw [partialCorrelationGram_apply_eq_sum_Iic, ← Finset.sum_coe_sort, Fintype.sum_pow]
  simp_rw [hentry]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [← prod_selected_partialCorrelationCholesky_eq_prod_pow z n c]
  rw [Fintype.prod_sigma]

end TauCeti
