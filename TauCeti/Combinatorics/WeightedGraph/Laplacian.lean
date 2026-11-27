/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# Weighted graphs and their Laplacians

A weighted graph on a finite vertex type `V` is a real matrix `W : Matrix V V ℝ` that is
symmetric with nonnegative entries (`TauCeti.IsWeightedGraph`). Loops, `0 < W i i`, are allowed;
a loop counts once in the degree. This file defines the weighted degree and the three Laplacians
of a weight matrix, together with the simple graph of its positive weights, and identifies the
combinatorial Laplacian of the adjacency matrix of a simple graph with Mathlib's
`SimpleGraph.lapMatrix`.

## Main definitions

* `TauCeti.IsWeightedGraph W`: `W` is symmetric with nonnegative entries.
* `TauCeti.WeightedGraph.degree W i = ∑ j, W i j`, the weighted degree.
* `TauCeti.WeightedGraph.laplacian W = D - W`, the combinatorial Laplacian, where `D` is the
  diagonal matrix of the degrees.
* `TauCeti.WeightedGraph.normalizedLaplacian W = D^{-1/2} L D^{-1/2}`, with the convention
  `(√0)⁻¹ = 0`, so a vertex of degree `0` gives a zero row and column.
* `TauCeti.WeightedGraph.randomWalkLaplacian W = D⁻¹ L`, again with `0⁻¹ = 0`.
* `TauCeti.WeightedGraph.positiveGraph W`: the simple graph with an edge between distinct `i` and
  `j` when `0 < W i j` or `0 < W j i`; loops are dropped.

## Main results

* `TauCeti.WeightedGraph.laplacian_adjMatrix`: for a simple graph `G`, the Laplacian of its
  adjacency matrix is Mathlib's `G.lapMatrix ℝ`.
* `TauCeti.WeightedGraph.laplacian_mulVec_apply`: `(L f) i = ∑ j, W i j * (f i - f j)`, and hence
  `TauCeti.WeightedGraph.laplacian_mulVec_one`: the constants lie in the kernel of `L`.
* `SimpleGraph.isWeightedGraph_adjMatrix`, `SimpleGraph.degree_adjMatrix`: the adjacency matrix
  of `G` is a weighted graph, whose weighted degrees are the degrees of `G`.
* `SimpleGraph.positiveGraph_adjMatrix`: the graph of positive weights of the adjacency matrix of
  `G` is `G`.

## Implementation notes

The predicate `TauCeti.IsWeightedGraph` and its lemmas live in the namespace `TauCeti`; the other
declarations live in `TauCeti.WeightedGraph`, since `TauCeti.degree` is already the mapping
degree of a map of manifolds. The lemmas `isWeightedGraph_adjMatrix`, `degree_adjMatrix` and
`positiveGraph_adjMatrix`, whose first explicit argument is a simple graph, live in the namespace
`SimpleGraph`.

The file was written from scratch, with AI assistance (Claude).

## References

* F. R. K. Chung, *Spectral Graph Theory*, CBMS Regional Conference Series in Mathematics 92,
  American Mathematical Society, 1997, §§1.2 and 1.4.
* M. Fiedler, *Matrices and Graphs in Geometry*, Encyclopedia of Mathematics and its
  Applications 139, Cambridge University Press, 2011, §6.1.
-/

public section

open Finset Matrix

namespace TauCeti

variable {V : Type*}

/-- A weighted graph on `V`: a real matrix that is symmetric with nonnegative entries. Loops,
`0 < W i i`, are allowed. -/
structure IsWeightedGraph (W : Matrix V V ℝ) : Prop where
  /-- The weight matrix is symmetric. -/
  symm : W.IsSymm
  /-- Every weight is nonnegative. -/
  nonneg : ∀ i j, 0 ≤ W i j

/-- A matrix is a weighted graph when it is symmetric with nonnegative entries. -/
theorem isWeightedGraph_iff {W : Matrix V V ℝ} :
    IsWeightedGraph W ↔ W.IsSymm ∧ ∀ i j, 0 ≤ W i j :=
  ⟨fun hW ↦ ⟨hW.symm, hW.nonneg⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- The weights of a weighted graph are symmetric. -/
theorem IsWeightedGraph.apply_comm {W : Matrix V V ℝ} (hW : IsWeightedGraph W) (i j : V) :
    W i j = W j i :=
  hW.symm.apply j i

/-- The zero matrix is a weighted graph, with no edges. -/
@[simp] theorem isWeightedGraph_zero : IsWeightedGraph (0 : Matrix V V ℝ) :=
  ⟨isSymm_zero, fun _ _ ↦ le_rfl⟩

namespace WeightedGraph

section Fintype

variable [Fintype V]

/-- The weighted degree `dᵢ = ∑ⱼ Wᵢⱼ` of the vertex `i`; a loop counts once. -/
def degree (W : Matrix V V ℝ) (i : V) : ℝ := ∑ j, W i j

/-- The defining formula of the weighted degree. -/
theorem degree_def (W : Matrix V V ℝ) (i : V) : degree W i = ∑ j, W i j := (rfl)

/-- The degrees of the zero matrix vanish. -/
@[simp] theorem degree_zero : degree (0 : Matrix V V ℝ) = 0 := by
  ext i
  simp [degree_def]

/-- If the weights `W i j` at the vertex `i` are nonnegative, so is its degree. This applies
to every vertex of a weighted graph. -/
theorem degree_nonneg {W : Matrix V V ℝ} {i : V} (h : ∀ j, 0 ≤ W i j) : 0 ≤ degree W i :=
  sum_nonneg fun j _ ↦ h j

variable [DecidableEq V]

/-- The combinatorial Laplacian `L = D - W` of a weight matrix, where `D` is the diagonal matrix
of the degrees. -/
def laplacian (W : Matrix V V ℝ) : Matrix V V ℝ := diagonal (degree W) - W

/-- The defining formula of the combinatorial Laplacian. -/
theorem laplacian_def (W : Matrix V V ℝ) : laplacian W = diagonal (degree W) - W := (rfl)

/-- The diagonal entries of the Laplacian: a loop does not contribute. -/
@[simp] theorem laplacian_apply_self (W : Matrix V V ℝ) (i : V) :
    laplacian W i i = degree W i - W i i := by
  simp [laplacian_def]

/-- The off-diagonal entries of the Laplacian are the negated weights. -/
@[simp] theorem laplacian_apply_of_ne (W : Matrix V V ℝ) {i j : V} (h : i ≠ j) :
    laplacian W i j = -W i j := by
  simp [laplacian_def, diagonal_apply_ne _ h]

/-- The Laplacian of the zero matrix is zero. -/
@[simp] theorem laplacian_zero : laplacian (0 : Matrix V V ℝ) = 0 := by
  simp [laplacian_def]

/-- The Laplacian applied to a function: `(L f) i = ∑ⱼ Wᵢⱼ (fᵢ - fⱼ)`. -/
theorem laplacian_mulVec_apply (W : Matrix V V ℝ) (f : V → ℝ) (i : V) :
    (laplacian W *ᵥ f) i = ∑ j, W i j * (f i - f j) := by
  rw [laplacian_def, sub_mulVec, Pi.sub_apply, mulVec_diagonal, degree_def, sum_mul]
  simp only [mulVec, dotProduct, mul_sub, sum_sub_distrib]

/-- The constant functions lie in the kernel of the Laplacian. -/
@[simp] theorem laplacian_mulVec_one (W : Matrix V V ℝ) : laplacian W *ᵥ 1 = 0 := by
  ext i
  simp [laplacian_mulVec_apply]

/-- The Laplacian of a symmetric weight matrix is symmetric. -/
theorem isSymm_laplacian {W : Matrix V V ℝ} (hW : W.IsSymm) : (laplacian W).IsSymm :=
  (isSymm_diagonal _).sub hW

/-- The normalized Laplacian `𝓛 = D^{-1/2} L D^{-1/2}`, with the convention `(√0)⁻¹ = 0`: a
vertex of degree `0` gives a zero row and column. -/
noncomputable def normalizedLaplacian (W : Matrix V V ℝ) : Matrix V V ℝ :=
  diagonal (fun i ↦ (√(degree W i))⁻¹) * laplacian W * diagonal (fun i ↦ (√(degree W i))⁻¹)

/-- The defining formula of the normalized Laplacian. -/
theorem normalizedLaplacian_def (W : Matrix V V ℝ) :
    normalizedLaplacian W =
      diagonal (fun i ↦ (√(degree W i))⁻¹) * laplacian W *
        diagonal (fun i ↦ (√(degree W i))⁻¹) := (rfl)

/-- The entries of the normalized Laplacian: `𝓛ᵢⱼ = Lᵢⱼ / (√dᵢ √dⱼ)`, read with `(√0)⁻¹ = 0`. -/
theorem normalizedLaplacian_apply (W : Matrix V V ℝ) (i j : V) :
    normalizedLaplacian W i j = (√(degree W i))⁻¹ * laplacian W i j * (√(degree W j))⁻¹ := by
  simp [normalizedLaplacian_def, diagonal_mul, mul_diagonal]

/-- The random-walk Laplacian `L_rw = D⁻¹ L`, with the convention `0⁻¹ = 0`: a vertex of degree `0`
gives a zero row. When every degree is nonzero, `L_rw = I - D⁻¹ W`; at a vertex of degree `0` the
row of `I - D⁻¹ W` is that of `I`, not zero. -/
noncomputable def randomWalkLaplacian (W : Matrix V V ℝ) : Matrix V V ℝ :=
  diagonal (fun i ↦ (degree W i)⁻¹) * laplacian W

/-- The defining formula of the random-walk Laplacian. -/
theorem randomWalkLaplacian_def (W : Matrix V V ℝ) :
    randomWalkLaplacian W = diagonal (fun i ↦ (degree W i)⁻¹) * laplacian W := (rfl)

/-- The entries of the random-walk Laplacian: `(L_rw)ᵢⱼ = Lᵢⱼ / dᵢ`, read with `0⁻¹ = 0`. -/
theorem randomWalkLaplacian_apply (W : Matrix V V ℝ) (i j : V) :
    randomWalkLaplacian W i j = (degree W i)⁻¹ * laplacian W i j := by
  simp [randomWalkLaplacian_def, diagonal_mul]

end Fintype

/-- The simple graph of the positive weights of `W`: distinct vertices `i` and `j` are adjacent
when `0 < W i j` or `0 < W j i`. Loops are dropped. -/
def positiveGraph (W : Matrix V V ℝ) : SimpleGraph V :=
  SimpleGraph.fromRel fun i j ↦ 0 < W i j

/-- Adjacency in the graph of positive weights. -/
@[simp] theorem positiveGraph_adj {W : Matrix V V ℝ} {i j : V} :
    (positiveGraph W).Adj i j ↔ i ≠ j ∧ (0 < W i j ∨ 0 < W j i) :=
  SimpleGraph.fromRel_adj _ i j

/-- For a symmetric weight matrix, distinct vertices are adjacent in the graph of positive
weights exactly when their weight is positive. -/
theorem positiveGraph_adj_of_isSymm {W : Matrix V V ℝ} (hW : W.IsSymm) {i j : V} :
    (positiveGraph W).Adj i j ↔ i ≠ j ∧ 0 < W i j := by
  rw [positiveGraph_adj, hW.apply i j, or_self]

/-- The graph of positive weights of the zero matrix has no edges. -/
@[simp] theorem positiveGraph_zero : positiveGraph (0 : Matrix V V ℝ) = ⊥ := by
  ext i j
  simp

end WeightedGraph

end TauCeti

namespace SimpleGraph

variable {V : Type*}

/-- The adjacency matrix of a simple graph is a weighted graph. -/
@[simp] theorem isWeightedGraph_adjMatrix (G : SimpleGraph V) [DecidableRel G.Adj] :
    TauCeti.IsWeightedGraph (G.adjMatrix ℝ) where
  symm := G.isSymm_adjMatrix
  nonneg i j := by
    rw [adjMatrix_apply]
    split_ifs <;> norm_num

section Fintype

variable [Fintype V]

/-- The weighted degree of the adjacency matrix of a simple graph is the degree of the graph. -/
@[simp] theorem degree_adjMatrix (G : SimpleGraph V) [DecidableRel G.Adj] (i : V) :
    TauCeti.WeightedGraph.degree (G.adjMatrix ℝ) i = G.degree i := by
  simp [TauCeti.WeightedGraph.degree_def, adjMatrix_apply, G.degree_eq_sum_if_adj (R := ℝ) i]

end Fintype

/-- The graph of positive weights of the adjacency matrix of a simple graph is the graph. -/
@[simp] theorem positiveGraph_adjMatrix (G : SimpleGraph V) [DecidableRel G.Adj] :
    TauCeti.WeightedGraph.positiveGraph (G.adjMatrix ℝ) = G := by
  ext i j
  simp only [TauCeti.WeightedGraph.positiveGraph_adj_of_isSymm G.isSymm_adjMatrix, adjMatrix_apply]
  by_cases h : G.Adj i j
  · simp [h, h.ne]
  · simp [h]

end SimpleGraph

namespace TauCeti.WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- For a simple graph, the weighted Laplacian of its adjacency matrix is Mathlib's
`SimpleGraph.lapMatrix`. -/
@[simp] theorem laplacian_adjMatrix (G : SimpleGraph V) [DecidableRel G.Adj] :
    laplacian (G.adjMatrix ℝ) = G.lapMatrix ℝ := by
  have h : degree (G.adjMatrix ℝ) = fun i ↦ (G.degree i : ℝ) := funext G.degree_adjMatrix
  rw [laplacian_def, h, SimpleGraph.lapMatrix, SimpleGraph.degMatrix]

end TauCeti.WeightedGraph
