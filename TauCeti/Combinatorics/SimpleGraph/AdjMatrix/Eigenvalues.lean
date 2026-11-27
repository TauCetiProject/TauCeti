/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import TauCeti.Analysis.Matrix.Eigenvalues.Basic
import TauCeti.Analysis.Matrix.Eigenvalues.Interlacing

/-!
# The adjacency spectrum of a finite simple graph

`SimpleGraph.adjEigenvalues` lists the eigenvalues of the real adjacency matrix in nonincreasing
order, with multiplicity. On a nonempty vertex type, `SimpleGraph.largestEigenvalue` and
`SimpleGraph.smallestEigenvalue` are the endpoints of this list.

The eigenvalues sum to zero and their squares sum to twice the number of edges. Consequently the
spectrum vanishes exactly for the edgeless graph, and any edge forces both a positive and a negative
eigenvalue. The extreme eigenvalues bound the adjacency quadratic form, with equality
characterizing membership in the corresponding eigenspace. The spectrum of an induced subgraph
interlaces the full spectrum by Cauchy interlacing for principal submatrices.

## References

* A. E. Brouwer and W. H. Haemers, *Spectra of Graphs*, Springer Universitext (2012),
  Propositions 1.3.1, 1.3.2 and 3.2.1, and Proposition 3.1.2 for the use of Rayleigh bounds.
-/

public section

open Finset Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The eigenvalues of the real adjacency matrix, listed in nonincreasing order with
multiplicity. -/
noncomputable def adjEigenvalues : Fin (Fintype.card V) → ℝ :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues₀

/-- The sorted adjacency spectrum is the sorted spectrum of the real adjacency matrix. -/
theorem adjEigenvalues_def :
    G.adjEigenvalues = (G.isHermitian_adjMatrix ℝ).eigenvalues₀ := (rfl)

/-- The adjacency eigenvalues are listed in nonincreasing order. -/
theorem adjEigenvalues_antitone : Antitone G.adjEigenvalues :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues₀_antitone

/-- The largest adjacency eigenvalue of a simple graph on a nonempty vertex type, at index
`0`. -/
noncomputable def largestEigenvalue [Nonempty V] : ℝ :=
  G.adjEigenvalues ⟨0, Fintype.card_pos⟩

/-- The largest adjacency eigenvalue is the first entry in the sorted list. -/
theorem largestEigenvalue_def [Nonempty V] :
    G.largestEigenvalue = G.adjEigenvalues ⟨0, Fintype.card_pos⟩ := (rfl)

/-- The smallest adjacency eigenvalue of a simple graph on a nonempty vertex type, at index
`Fintype.card V - 1`. -/
noncomputable def smallestEigenvalue [Nonempty V] : ℝ :=
  G.adjEigenvalues ⟨Fintype.card V - 1, Nat.sub_lt Fintype.card_pos Nat.one_pos⟩

/-- The smallest adjacency eigenvalue is the last entry in the sorted list. -/
theorem smallestEigenvalue_def [Nonempty V] :
    G.smallestEigenvalue =
      G.adjEigenvalues ⟨Fintype.card V - 1, Nat.sub_lt Fintype.card_pos Nat.one_pos⟩ := (rfl)

/-- Every adjacency eigenvalue is at most the largest one. -/
theorem adjEigenvalues_le_largestEigenvalue [Nonempty V] (i : Fin (Fintype.card V)) :
    G.adjEigenvalues i ≤ G.largestEigenvalue :=
  G.adjEigenvalues_antitone (Fin.mk_le_mk.mpr (Nat.zero_le i))

/-- Every adjacency eigenvalue is at least the smallest one. -/
theorem smallestEigenvalue_le_adjEigenvalues [Nonempty V] (i : Fin (Fintype.card V)) :
    G.smallestEigenvalue ≤ G.adjEigenvalues i :=
  G.adjEigenvalues_antitone (Fin.mk_le_mk.mpr (Nat.le_pred_of_lt i.isLt))

/-! ### Spectral moments and signs -/

/-- The sum of the adjacency eigenvalues is zero. -/
@[simp]
theorem sum_adjEigenvalues : ∑ i, G.adjEigenvalues i = 0 := by
  rw [G.adjEigenvalues_def, (G.isHermitian_adjMatrix ℝ).sum_eigenvalues₀_eq_re_trace,
    G.trace_adjMatrix ℝ, map_zero]

/-- The sum of squared adjacency eigenvalues is twice the number of edges. -/
theorem sum_adjEigenvalues_sq : ∑ i, G.adjEigenvalues i ^ 2 = 2 * (#G.edgeFinset : ℝ) := by
  rw [G.adjEigenvalues_def, (G.isHermitian_adjMatrix ℝ).sum_eigenvalues₀_pow_eq_re_trace_pow,
    RCLike.re_to_real, pow_two, Matrix.trace]
  simp only [Matrix.diag_apply, G.adjMatrix_mul_self_apply_self, ← Nat.cast_sum]
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

/-- All adjacency eigenvalues vanish exactly when the graph has no edges. -/
@[simp]
theorem adjEigenvalues_eq_zero_iff : G.adjEigenvalues = 0 ↔ G = ⊥ := by
  constructor
  · intro h
    simpa [h] using G.sum_adjEigenvalues_sq.symm
  · intro h
    have hc := Finset.card_eq_zero.mpr (edgeFinset_eq_empty.mpr h)
    have hs := G.sum_adjEigenvalues_sq
    rw [hc, Nat.cast_zero, mul_zero] at hs
    ext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg (G.adjEigenvalues j))).mp
      hs i (mem_univ i)
    simpa using hi

/-- The adjacency spectrum of the edgeless graph is zero. -/
@[simp]
theorem adjEigenvalues_bot [DecidableRel (⊥ : SimpleGraph V).Adj] :
    (⊥ : SimpleGraph V).adjEigenvalues = 0 :=
  (adjEigenvalues_eq_zero_iff _).mpr rfl

/-- The largest adjacency eigenvalue of an edgeless graph is zero. -/
@[simp]
theorem largestEigenvalue_bot [Nonempty V] [DecidableRel (⊥ : SimpleGraph V).Adj] :
    (⊥ : SimpleGraph V).largestEigenvalue = 0 := by
  simp [largestEigenvalue_def]

/-- The smallest adjacency eigenvalue of an edgeless graph is zero. -/
@[simp]
theorem smallestEigenvalue_bot [Nonempty V] [DecidableRel (⊥ : SimpleGraph V).Adj] :
    (⊥ : SimpleGraph V).smallestEigenvalue = 0 := by
  simp [smallestEigenvalue_def]

private theorem exists_adjEigenvalues_ne_zero_of_ne_bot (h : G ≠ ⊥) :
    ∃ i ∈ (univ : Finset (Fin (Fintype.card V))), G.adjEigenvalues i ≠ 0 := by
  simpa [funext_iff] using mt G.adjEigenvalues_eq_zero_iff.mp h

/-- The largest adjacency eigenvalue is positive exactly when the graph has an edge. -/
theorem largestEigenvalue_pos_iff [Nonempty V] : 0 < G.largestEigenvalue ↔ G ≠ ⊥ := by
  constructor
  · rintro h rfl
    simp at h
  · intro h
    obtain ⟨i, -, hi⟩ := exists_pos_of_sum_zero_of_exists_nonzero _ G.sum_adjEigenvalues
      (G.exists_adjEigenvalues_ne_zero_of_ne_bot h)
    exact hi.trans_le (G.adjEigenvalues_le_largestEigenvalue i)

/-- The smallest adjacency eigenvalue is negative exactly when the graph has an edge. -/
theorem smallestEigenvalue_neg_iff [Nonempty V] : G.smallestEigenvalue < 0 ↔ G ≠ ⊥ := by
  constructor
  · rintro h rfl
    simp at h
  · intro h
    obtain ⟨i, -, hi⟩ := exists_neg_of_sum_zero_of_exists_nonzero _ G.sum_adjEigenvalues
      (G.exists_adjEigenvalues_ne_zero_of_ne_bot h)
    exact (G.smallestEigenvalue_le_adjEigenvalues i).trans_lt hi

/-- The largest adjacency eigenvalue is nonnegative. -/
theorem largestEigenvalue_nonneg [Nonempty V] : 0 ≤ G.largestEigenvalue := by
  rcases eq_or_ne G ⊥ with rfl | h
  · simp
  · exact (G.largestEigenvalue_pos_iff.mpr h).le

/-- The smallest adjacency eigenvalue is nonpositive. -/
theorem smallestEigenvalue_nonpos [Nonempty V] : G.smallestEigenvalue ≤ 0 := by
  rcases eq_or_ne G ⊥ with rfl | h
  · simp
  · exact (G.smallestEigenvalue_neg_iff.mpr h).le

/-! ### Rayleigh bounds -/

/-- The adjacency quadratic form is bounded above by the largest eigenvalue times the squared
Euclidean norm. -/
theorem dotProduct_mulVec_adjMatrix_le [Nonempty V] (x : V → ℝ) :
    x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) ≤ G.largestEigenvalue * (x ⬝ᵥ x) := by
  simpa only [G.largestEigenvalue_def, G.adjEigenvalues_def, star_trivial, RCLike.re_to_real]
    using ((G.isHermitian_adjMatrix ℝ).re_star_dotProduct_mulVec_mem_Icc x).2

/-- The adjacency quadratic form is bounded below by the smallest eigenvalue times the squared
Euclidean norm. -/
theorem le_dotProduct_mulVec_adjMatrix [Nonempty V] (x : V → ℝ) :
    G.smallestEigenvalue * (x ⬝ᵥ x) ≤ x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) := by
  simpa only [G.smallestEigenvalue_def, G.adjEigenvalues_def, star_trivial, RCLike.re_to_real]
    using ((G.isHermitian_adjMatrix ℝ).re_star_dotProduct_mulVec_mem_Icc x).1

/-- Equality in the upper Rayleigh bound is equivalent to membership in the largest
adjacency eigenspace. -/
theorem dotProduct_mulVec_adjMatrix_eq_largestEigenvalue_mul_iff [Nonempty V] (x : V → ℝ) :
    x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) = G.largestEigenvalue * (x ⬝ᵥ x) ↔
      G.adjMatrix ℝ *ᵥ x = G.largestEigenvalue • x := by
  simpa only [star_trivial, RCLike.re_to_real] using
    (G.isHermitian_adjMatrix ℝ).re_star_dotProduct_mulVec_eq_mul_iff_of_forall_le
      (by simpa only [star_trivial, RCLike.re_to_real] using G.dotProduct_mulVec_adjMatrix_le) x

/-- Equality in the lower Rayleigh bound is equivalent to membership in the smallest
adjacency eigenspace. -/
theorem dotProduct_mulVec_adjMatrix_eq_smallestEigenvalue_mul_iff [Nonempty V] (x : V → ℝ) :
    x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) = G.smallestEigenvalue * (x ⬝ᵥ x) ↔
      G.adjMatrix ℝ *ᵥ x = G.smallestEigenvalue • x := by
  simpa only [star_trivial, RCLike.re_to_real] using
    (G.isHermitian_adjMatrix ℝ).re_star_dotProduct_mulVec_eq_mul_iff_of_forall_ge
      (by simpa only [star_trivial, RCLike.re_to_real] using G.le_dotProduct_mulVec_adjMatrix) x

/-! ### Interlacing for induced subgraphs -/

variable {G} {W : Type*} [Fintype W] [DecidableEq W] {H : SimpleGraph W} [DecidableRel H.Adj]

/-- The `i`-th largest adjacency eigenvalue of an induced subgraph is at most the `i`-th
largest adjacency eigenvalue of the ambient graph. -/
theorem Embedding.adjEigenvalues_le (f : H ↪g G) (i : Fin (Fintype.card W)) :
    H.adjEigenvalues i ≤
      G.adjEigenvalues (Fin.castLE (Fintype.card_le_of_embedding f.toEmbedding) i) := by
  have hG := G.isHermitian_adjMatrix ℝ
  rw [H.adjEigenvalues_def, G.adjEigenvalues_def,
    ← IsHermitian.eigenvalues₀_congr (f.submatrix_adjMatrix ℝ) (hG.submatrix f.toEmbedding)
      (H.isHermitian_adjMatrix ℝ)]
  exact hG.eigenvalues₀_submatrix_le f.toEmbedding i

/-- The `i`-th largest adjacency eigenvalue of an induced subgraph is at least the eigenvalue
of index `i + (|V| - |W|)` in the ambient graph's decreasing list. -/
theorem Embedding.le_adjEigenvalues (f : H ↪g G) (i : Fin (Fintype.card W)) :
    G.adjEigenvalues (Fin.cast (Nat.add_sub_of_le (Fintype.card_le_of_embedding f.toEmbedding))
        (i.addNat (Fintype.card V - Fintype.card W))) ≤ H.adjEigenvalues i := by
  have hG := G.isHermitian_adjMatrix ℝ
  rw [H.adjEigenvalues_def, G.adjEigenvalues_def,
    ← IsHermitian.eigenvalues₀_congr (f.submatrix_adjMatrix ℝ) (hG.submatrix f.toEmbedding)
      (H.isHermitian_adjMatrix ℝ)]
  exact hG.eigenvalues₀_le_eigenvalues₀_submatrix f.toEmbedding i

end SimpleGraph
