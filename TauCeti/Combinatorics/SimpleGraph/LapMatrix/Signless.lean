/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.IncMatrix
public import TauCeti.Combinatorics.SimpleGraph.LapMatrix.QuadraticForm

/-!
# The signless Laplacian of a graph

The signless Laplacian of a finite simple graph is `Q = D + A`, the sum of the degree matrix and
the adjacency matrix. Its entries are `Q_{ii} = d(i)` and `Q_{ij} = A_{ij}` for `i ≠ j`, and its
quadratic form is `uᵀ Q u = ∑_{xy ∈ E} (u_x + u_y)²`. Hence `Q` is positive semidefinite, and
`Q u = 0` exactly when `u_x + u_y = 0` along every edge.

With the unsigned incidence matrix `U` (the columns of Mathlib's `incMatrix` at the edges),
`Q = U Uᵀ`. For a proper `2`-colouring with sign matrix `S = diag(±1)`, `S L S = Q`, where `L` is
the Laplacian; so the Laplacian and the signless Laplacian of a bipartite graph are similar.

## Main definitions

* `SimpleGraph.signlessLapMatrix`: the signless Laplacian `Q = D + A`.
* `SimpleGraph.unsignedIncMatrix`: the vertex-edge incidence matrix with columns indexed by the
  edges.

## Main results

* `SimpleGraph.signlessLapMatrix_apply_self`, `SimpleGraph.signlessLapMatrix_apply_of_ne`: the
  entries of `Q`.
* `SimpleGraph.isSymm_signlessLapMatrix`, `SimpleGraph.isHermitian_signlessLapMatrix`: `Q` is
  symmetric.
* `SimpleGraph.signlessLapMatrix_mulVec_one`: `Q 𝟙 = 2 d`.
* `SimpleGraph.dotProduct_mulVec_signlessLapMatrix_self`: `uᵀ Q u = ∑_{xy ∈ E} (u_x + u_y)²`.
* `SimpleGraph.posSemidef_signlessLapMatrix`: `Q` is positive semidefinite.
* `SimpleGraph.signlessLapMatrix_mulVec_eq_zero_iff`: `Q u = 0` if and only if
  `u_x + u_y = 0` for every edge `xy`.
* `SimpleGraph.unsignedIncMatrix_mul_transpose`: `U Uᵀ = Q`.
* `SimpleGraph.signDiagonal_mul_lapMatrix_mul_signDiagonal`: `S L S = Q` for the sign matrix `S`
  of a proper `2`-colouring.

## References

* A. E. Brouwer and W. H. Haemers, *Spectra of Graphs*, Springer Universitext (2012), §1.1 and
  the proof of Proposition 1.3.10.
* D. Cvetković, P. Rowlinson and S. Simić, *An Introduction to the Theory of Graph Spectra*,
  Cambridge University Press (2010), §7.8.
-/

public section

open Finset Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The signless Laplacian `Q = D + A` of a simple graph: the sum of the degree matrix and the
adjacency matrix. -/
def signlessLapMatrix (R : Type*) [AddMonoidWithOne R] : Matrix V V R :=
  G.degMatrix R + G.adjMatrix R

/-- The signless Laplacian is the degree matrix plus the adjacency matrix. -/
theorem signlessLapMatrix_def (R : Type*) [AddMonoidWithOne R] :
    G.signlessLapMatrix R = G.degMatrix R + G.adjMatrix R :=
  (rfl)

/-- The diagonal of the signless Laplacian is the degree sequence. -/
@[simp]
theorem signlessLapMatrix_apply_self {R : Type*} [AddMonoidWithOne R] (i : V) :
    G.signlessLapMatrix R i i = G.degree i := by
  simp [signlessLapMatrix, degMatrix]

/-- Off the diagonal, the signless Laplacian agrees with the adjacency matrix. -/
theorem signlessLapMatrix_apply_of_ne {R : Type*} [AddMonoidWithOne R] {i j : V} (h : i ≠ j) :
    G.signlessLapMatrix R i j = G.adjMatrix R i j := by
  simp [signlessLapMatrix, degMatrix, h]

/-- The signless Laplacian is symmetric. -/
theorem isSymm_signlessLapMatrix (R : Type*) [AddMonoidWithOne R] :
    (G.signlessLapMatrix R).IsSymm :=
  (G.isSymm_degMatrix R).add G.isSymm_adjMatrix

/-- The signless Laplacian is Hermitian. -/
theorem isHermitian_signlessLapMatrix (R : Type*) [NonAssocSemiring R] [StarRing R] :
    (G.signlessLapMatrix R).IsHermitian :=
  (G.isHermitian_degMatrix R).add (G.isHermitian_adjMatrix R)

/-- The `i`-th entry of `Q u` is the sum of `u i + u j` over the neighbours `j` of `i`. -/
theorem signlessLapMatrix_mulVec_apply {R : Type*} [NonAssocSemiring R] (u : V → R) (i : V) :
    (G.signlessLapMatrix R *ᵥ u) i = ∑ j ∈ G.neighborFinset i, (u i + u j) := by
  rw [signlessLapMatrix, add_mulVec, Pi.add_apply, degMatrix_mulVec_apply,
    adjMatrix_mulVec_apply, sum_add_distrib, sum_const, card_neighborFinset_eq_degree,
    nsmul_eq_mul]

/-- The row sums of the signless Laplacian are twice the degrees: `Q 𝟙 = 2 d`. -/
theorem signlessLapMatrix_mulVec_one {R : Type*} [NonAssocSemiring R] :
    G.signlessLapMatrix R *ᵥ (fun _ ↦ 1) = fun i ↦ 2 * (G.degree i : R) := by
  ext i
  simp [signlessLapMatrix, add_mulVec, degMatrix_mulVec_apply, two_mul]

/-- The quadratic form of the signless Laplacian: `uᵀ Q u = ∑_{xy ∈ E} (u_x + u_y)²`. -/
theorem dotProduct_mulVec_signlessLapMatrix_self {R : Type*} [Semiring R] (u : V → R) :
    u ⬝ᵥ (G.signlessLapMatrix R *ᵥ u) =
      ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun x y ↦ (u x + u y) ^ 2,
        fun _ _ ↦ by dsimp only; rw [add_comm]⟩ e := by
  rw [signlessLapMatrix, add_mulVec, dotProduct_add, dotProduct_mulVec_degMatrix_self,
    dotProduct_mulVec_adjMatrix, sum_sum_ite_adj_eq_sum_edgeFinset, ← sum_add_distrib]
  refine sum_congr rfl fun e _ ↦ ?_
  induction e using Sym2.ind with | _ x y => simp only [Sym2.lift_mk]; noncomm_ring

omit [Fintype V] [DecidableEq V] in
/-- Each term `(u_x + u_y)²` of the quadratic form of the signless Laplacian is nonnegative. -/
private theorem lift_add_sq_nonneg {R : Type*} [Ring R] [LinearOrder R]
    [IsOrderedRing R] (u : V → R) (e : Sym2 V) :
    0 ≤ Sym2.lift ⟨fun x y ↦ (u x + u y) ^ 2, fun _ _ ↦ by dsimp only; rw [add_comm]⟩ e := by
  induction e using Sym2.ind with | _ x y => exact sq_nonneg _

/-- The signless Laplacian is positive semidefinite. -/
theorem posSemidef_signlessLapMatrix (R : Type*) [Ring R] [LinearOrder R] [IsOrderedRing R]
    [StarRing R] [TrivialStar R] : (G.signlessLapMatrix R).PosSemidef := by
  refine .of_dotProduct_mulVec_nonneg (G.isHermitian_signlessLapMatrix R) fun u ↦ ?_
  rw [star_trivial, dotProduct_mulVec_signlessLapMatrix_self]
  exact sum_nonneg fun e _ ↦ lift_add_sq_nonneg u e

/-- `Q u = 0` exactly when `u_x + u_y = 0` along every edge `xy`. -/
theorem signlessLapMatrix_mulVec_eq_zero_iff {R : Type*} [Ring R] [LinearOrder R]
    [IsStrictOrderedRing R] (u : V → R) :
    G.signlessLapMatrix R *ᵥ u = 0 ↔ ∀ ⦃x y⦄, G.Adj x y → u x + u y = 0 := by
  refine ⟨fun h x y hxy ↦ ?_, fun h ↦ ?_⟩
  · have h0 := congrArg (u ⬝ᵥ ·) h
    simp only [dotProduct_zero, dotProduct_mulVec_signlessLapMatrix_self] at h0
    have := (sum_eq_zero_iff_of_nonneg fun e _ ↦ lift_add_sq_nonneg u e).1 h0 s(x, y)
      (mem_edgeFinset.2 hxy)
    simpa using this
  · ext i
    rw [signlessLapMatrix_mulVec_apply, Pi.zero_apply]
    exact sum_eq_zero fun j hj ↦ h ((mem_neighborFinset _ _ _).1 hj)

omit [Fintype V] in
/-- The unsigned incidence matrix of `G`: Mathlib's vertex-edge incidence matrix `incMatrix`
with its columns restricted to the edges of `G`. -/
def unsignedIncMatrix (R : Type*) [Zero R] [One R] : Matrix V G.edgeSet R :=
  fun x e ↦ G.incMatrix R x e

omit [Fintype V] in
/-- The entries of the unsigned incidence matrix are those of `incMatrix`. -/
@[simp]
theorem unsignedIncMatrix_apply {R : Type*} [Zero R] [One R] (x : V) (e : G.edgeSet) :
    G.unsignedIncMatrix R x e = G.incMatrix R x e :=
  (rfl)

/-- The unsigned incidence matrix `U` satisfies `U Uᵀ = Q`. -/
theorem unsignedIncMatrix_mul_transpose (R : Type*) [Semiring R] :
    G.unsignedIncMatrix R * (G.unsignedIncMatrix R)ᵀ = G.signlessLapMatrix R := by
  ext i j
  have key := congrFun₂ (G.incMatrix_mul_transpose (R := R)) i j
  rw [Matrix.mul_apply] at key ⊢
  simp only [transpose_apply, unsignedIncMatrix_apply] at key ⊢
  rw [← sum_subtype G.edgeFinset (fun _ ↦ mem_edgeFinset)
    (fun e ↦ G.incMatrix R i e * G.incMatrix R j e), sum_subset (subset_univ _) fun e _ he ↦ ?_,
    key]
  · rcases eq_or_ne i j with rfl | hij
    · simp
    · simp [signlessLapMatrix_apply_of_ne _ hij, hij, adjMatrix_apply]
  · rw [incMatrix_of_notMem_incidenceSet, zero_mul]
    exact fun h ↦ he (mem_edgeFinset.2 h.1)

/-- **Sign conjugation.** For a proper `2`-colouring `c` with sign matrix
`S = diag(if c x then -1 else 1)`, the conjugate `S L S` of the Laplacian is the signless
Laplacian. -/
theorem signDiagonal_mul_lapMatrix_mul_signDiagonal (R : Type*) [NonAssocRing R]
    (c : G.Coloring Bool) :
    diagonal (fun x ↦ if c x then (-1 : R) else 1) * G.lapMatrix R *
      diagonal (fun x ↦ if c x then (-1 : R) else 1) = G.signlessLapMatrix R := by
  ext i j
  rw [mul_diagonal, diagonal_mul]
  rcases eq_or_ne i j with rfl | hij
  · have hL : G.lapMatrix R i i = G.degree i := by simp [lapMatrix, degMatrix]
    rw [hL, signlessLapMatrix_apply_self]
    cases c i <;> simp
  · have hL : G.lapMatrix R i j = -G.adjMatrix R i j := by simp [lapMatrix, degMatrix, hij]
    rw [hL, signlessLapMatrix_apply_of_ne _ hij]
    by_cases ha : G.Adj i j
    · have hc := c.valid ha
      simp only [adjMatrix_apply, ha, ↓reduceIte]
      revert hc
      cases c i <;> cases c j <;> simp
    · simp [adjMatrix_apply, ha]

end SimpleGraph
