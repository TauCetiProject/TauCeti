/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Order.SymmDiff
import TauCeti.Combinatorics.SimpleGraph.Basic
import TauCeti.Combinatorics.SimpleGraph.Bipartite

/-!
# The Seidel matrix and Seidel switching

The Seidel matrix `G.seidelMatrix R` of a simple graph `G` has `0` on the diagonal, `-1` at a
pair of adjacent vertices and `1` at a pair of distinct nonadjacent vertices. It equals
`J - I - 2A`, where `J` is the all-one matrix and `A` the adjacency matrix. For a family of unit
vectors on equiangular lines, the Gram matrix is `I + α S` with `S` the Seidel matrix of the
graph of negative inner products.

For a set `U` of vertices, the switch `G.switch U` keeps the adjacency of `G` between two vertices
on the same side of the partition `{U, Uᶜ}` and interchanges adjacency and nonadjacency between
two vertices on different sides. When no inner product between two distinct vectors vanishes,
changing the signs of the vectors indexed by `U` switches the graph of negative inner products.
Two graphs are switching equivalent when one is a switch of the
other; since two switches compose to the switch with respect to the symmetric difference, this is
an equivalence relation. Switching conjugates the Seidel matrix by a diagonal sign matrix, so
switching equivalent graphs have the same Seidel spectrum.

## Main definitions

* `SimpleGraph.switch`: the switch of `G` with respect to a set `U` of vertices.
* `SimpleGraph.seidelMatrix`: the Seidel matrix of a graph.

## Main results

* `SimpleGraph.switch_eq_symmDiff_between`: switching with respect to `U` toggles the pairs across
  the cut `(U, Uᶜ)`.
* `SimpleGraph.switch_compl`, `SimpleGraph.switch_switch`, `SimpleGraph.compl_switch`: switching
  with respect to `U` and to `Uᶜ` agree, two switches compose to the switch with respect to the
  symmetric difference, and switching commutes with the complement.
* `SimpleGraph.seidelMatrix_eq_of_one_sub_one_sub_two_nsmul_adjMatrix`: `S = J - I - 2A`.
* `SimpleGraph.isSymm_seidelMatrix`, `SimpleGraph.seidelMatrix_apply_self`,
  `SimpleGraph.seidelMatrix_apply_mul_self_of_ne`: the Seidel matrix is symmetric with zero
  diagonal, and its entries off the diagonal have square `1`.
* `SimpleGraph.seidelMatrix_compl`: the Seidel matrix of the complement is `-S`.
* `SimpleGraph.IsRegularOfDegree.seidelMatrix_mulVec_const`: for a `k`-regular graph on `n`
  vertices the all-one vector is a Seidel eigenvector with eigenvalue `n - 1 - 2k`.
* `SimpleGraph.seidelMatrix_mulVec_eq_smul_of_adjMatrix_mulVec_eq_smul`: an eigenvector of the
  adjacency matrix with eigenvalue `θ` and coordinate sum `0` is a Seidel eigenvector with
  eigenvalue `-1 - 2θ`.
* `SimpleGraph.seidelMatrix_switch`: the Seidel matrix of `G.switch U` is `D S D`, where `D` is
  diagonal with `-1` at the vertices of `U` and `1` elsewhere.
* `SimpleGraph.charpoly_seidelMatrix_switch`: switching does not change the characteristic
  polynomial of the Seidel matrix.

## References

* A. E. Brouwer, W. H. Haemers, *Spectra of graphs*, Springer, 2012, §1.8.2.
-/

public section

open Matrix

open scoped symmDiff

namespace SimpleGraph

variable {V : Type*}

/-! ### Seidel switching -/

section Switching

/-- The Seidel switch of `G` with respect to a set `U` of vertices: two distinct vertices on the
same side of the partition `{U, Uᶜ}` are adjacent exactly when they are adjacent in `G`, and two
vertices on different sides are adjacent exactly when they are not adjacent in `G`. -/
def switch (G : SimpleGraph V) (U : Set V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (G.Adj u v ↔ (u ∈ U ↔ v ∈ U))
  symm.symm u v h := ⟨h.1.symm, by rw [G.adj_comm, h.2]; exact Iff.comm⟩
  loopless.irrefl u h := h.1 rfl

/-- Adjacency in a switched graph is decidable when adjacency in the original graph, equality of
vertices and membership in the switching set are. -/
instance instDecidableRelSwitch [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Set V) [DecidablePred (· ∈ U)] : DecidableRel (G.switch U).Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧ (G.Adj u v ↔ (u ∈ U ↔ v ∈ U))))

variable (G : SimpleGraph V) (U W : Set V)

/-- Two vertices are adjacent in `G.switch U` when they are distinct and they are adjacent in `G`
exactly when they lie on the same side of `{U, Uᶜ}`. -/
@[simp]
theorem switch_adj {u v : V} : (G.switch U).Adj u v ↔ u ≠ v ∧ (G.Adj u v ↔ (u ∈ U ↔ v ∈ U)) :=
  Iff.rfl

/-- Switching with respect to the empty set does not change the graph. -/
@[simp]
theorem switch_empty : G.switch ∅ = G := by
  ext u v
  simpa using G.ne_of_adj

/-- Switching with respect to all vertices does not change the graph. -/
@[simp]
theorem switch_univ : G.switch Set.univ = G := by
  ext u v
  simpa using G.ne_of_adj

/-- Switching with respect to the complement of `U` gives the same graph as switching with
respect to `U`. -/
@[simp]
theorem switch_compl : G.switch Uᶜ = G.switch U := by
  ext u v
  simp [Set.mem_compl_iff, not_iff_not]

/-- Switching with respect to `U` is the symmetric difference with the complete bipartite graph
between `U` and `Uᶜ`: it toggles exactly the pairs of vertices across the cut `(U, Uᶜ)`. -/
theorem switch_eq_symmDiff_between : G.switch U = G ∆ (⊤ : SimpleGraph V).between U Uᶜ := by
  ext u v
  by_cases huv : u = v
  · subst huv
    simp
  · simp only [symmDiff_top_between_compl_adj, switch_adj, Xor]
    tauto

/-- Switching with respect to `U` and then with respect to `W` is switching with respect to the
symmetric difference `U ∆ W`. -/
theorem switch_switch : (G.switch U).switch W = G.switch (U ∆ W) := by
  rw [switch_eq_symmDiff_between, switch_eq_symmDiff_between, switch_eq_symmDiff_between,
    top_between_symmDiff, symmDiff_assoc]

/-- Switching twice with respect to the same set gives back the original graph. -/
@[simp]
theorem switch_switch_self : (G.switch U).switch U = G := by
  rw [switch_switch, symmDiff_self, Set.bot_eq_empty, switch_empty]

/-- The complement of a switch is the switch of the complement. -/
theorem compl_switch : (G.switch U)ᶜ = Gᶜ.switch U := by
  ext u v
  simp only [compl_adj, switch_adj]
  tauto

end Switching

/-! ### The Seidel matrix -/

variable (R : Type*) (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]

/-- The Seidel matrix of a graph: `0` on the diagonal, `-1` at a pair of adjacent vertices and
`1` at a pair of distinct nonadjacent vertices. -/
def seidelMatrix [Zero R] [One R] [Neg R] : Matrix V V R :=
  of fun u v => if u = v then 0 else if G.Adj u v then -1 else 1

section Entries

variable [Zero R] [One R] [Neg R]

/-- The entries of the Seidel matrix. -/
theorem seidelMatrix_apply (u v : V) :
    G.seidelMatrix R u v = if u = v then 0 else if G.Adj u v then -1 else 1 :=
  (rfl)

/-- The diagonal entries of the Seidel matrix are `0`. -/
@[simp]
theorem seidelMatrix_apply_self (v : V) : G.seidelMatrix R v v = 0 := by
  simp [seidelMatrix_apply]

/-- The entry of the Seidel matrix at a pair of adjacent vertices is `-1`. -/
@[simp]
theorem seidelMatrix_apply_of_adj {u v : V} (h : G.Adj u v) : G.seidelMatrix R u v = -1 := by
  simp [seidelMatrix_apply, h, h.ne]

/-- The entry of the Seidel matrix at a pair of distinct nonadjacent vertices is `1`. -/
@[simp]
theorem seidelMatrix_apply_of_ne_of_not_adj {u v : V} (hne : u ≠ v) (h : ¬G.Adj u v) :
    G.seidelMatrix R u v = 1 := by
  simp [seidelMatrix_apply, h, hne]

/-- The diagonal of the Seidel matrix is `0`. -/
@[simp]
theorem diag_seidelMatrix : (G.seidelMatrix R).diag = 0 := by
  ext v
  simp

/-- The Seidel matrix is symmetric. -/
theorem isSymm_seidelMatrix : (G.seidelMatrix R).IsSymm := by
  ext u v
  simp [seidelMatrix_apply, eq_comm, G.adj_comm]

/-- The Seidel matrix is equal to its transpose. -/
@[simp]
theorem transpose_seidelMatrix : (G.seidelMatrix R)ᵀ = G.seidelMatrix R :=
  G.isSymm_seidelMatrix R

/-- The Seidel matrix of the graph without edges is `J - I`. -/
theorem seidelMatrix_bot : (⊥ : SimpleGraph V).seidelMatrix R =
    of fun u v => if u = v then 0 else 1 := by
  ext u v
  simp [seidelMatrix_apply]

/-- The Seidel matrix of the complete graph is `I - J`. -/
theorem seidelMatrix_top : (⊤ : SimpleGraph V).seidelMatrix R =
    of fun u v => if u = v then 0 else -1 := by
  ext u v
  by_cases huv : u = v <;> simp [huv]

end Entries

/-- The trace of the Seidel matrix is `0`. -/
@[simp]
theorem trace_seidelMatrix [Fintype V] [AddCommMonoid R] [One R] [Neg R] :
    (G.seidelMatrix R).trace = 0 := by
  simp [trace]

/-- The entries of the Seidel matrix off the diagonal have square `1`. -/
theorem seidelMatrix_apply_mul_self_of_ne [NonAssocRing R] {u v : V} (h : u ≠ v) :
    G.seidelMatrix R u v * G.seidelMatrix R u v = 1 := by
  by_cases hG : G.Adj u v <;> simp [hG, h]

/-- The entries of the Seidel matrix off the diagonal are units. -/
theorem isUnit_seidelMatrix_apply_of_ne [Ring R] {u v : V} (h : u ≠ v) :
    IsUnit (G.seidelMatrix R u v) :=
  ⟨⟨_, _, G.seidelMatrix_apply_mul_self_of_ne R h, G.seidelMatrix_apply_mul_self_of_ne R h⟩, rfl⟩

/-- The Seidel matrix of a graph is `A(Gᶜ) - A(G)`, the difference of the adjacency matrices of
the complement and of the graph. -/
theorem seidelMatrix_eq_adjMatrix_compl_sub_adjMatrix [AddGroup R] [One R] :
    G.seidelMatrix R = Gᶜ.adjMatrix R - G.adjMatrix R := by
  ext u v
  by_cases huv : u = v
  · simp [huv]
  · by_cases hG : G.Adj u v <;> simp [huv, hG]

/-- The Seidel matrix is `J - I - 2A`, where `J` is the all-one matrix and `A` the adjacency
matrix. -/
theorem seidelMatrix_eq_of_one_sub_one_sub_two_nsmul_adjMatrix [AddGroup R] [One R] :
    G.seidelMatrix R = of 1 - 1 - 2 • G.adjMatrix R := by
  ext u v
  by_cases huv : u = v
  · simp [huv]
  · by_cases hG : G.Adj u v <;> simp [huv, hG, one_apply_ne huv, two_nsmul]

/-- The Seidel matrix of the complement graph is the negative of the Seidel matrix. -/
@[simp]
theorem seidelMatrix_compl [SubtractionMonoid R] [One R] :
    Gᶜ.seidelMatrix R = -G.seidelMatrix R := by
  ext u v
  by_cases huv : u = v
  · simp [huv]
  · by_cases hG : G.Adj u v <;> simp [huv, hG]

section Eigenvectors

variable [Fintype V] [NonAssocRing R] {G}

/-- The product of the Seidel matrix with a vector `x` whose coordinates sum to `0` is
`-x - 2 A x`. -/
theorem seidelMatrix_mulVec_of_sum_eq_zero {x : V → R} (hx : ∑ v, x v = 0) :
    G.seidelMatrix R *ᵥ x = -x - 2 • (G.adjMatrix R *ᵥ x) := by
  rw [seidelMatrix_eq_of_one_sub_one_sub_two_nsmul_adjMatrix, sub_mulVec, sub_mulVec,
    one_mulVec, smul_mulVec]
  ext v
  simp [mulVec, dotProduct, hx]

/-- If `x` is an eigenvector of the adjacency matrix with eigenvalue `θ` and the coordinates of `x`
sum to `0`, then `x` is an eigenvector of the Seidel matrix with eigenvalue `-1 - 2θ`. -/
theorem seidelMatrix_mulVec_eq_smul_of_adjMatrix_mulVec_eq_smul {x : V → R} {θ : R}
    (hθ : G.adjMatrix R *ᵥ x = θ • x) (hx : ∑ v, x v = 0) :
    G.seidelMatrix R *ᵥ x = (-1 - 2 * θ) • x := by
  rw [seidelMatrix_mulVec_of_sum_eq_zero R hx, hθ]
  ext v
  simp [sub_mul, two_mul, add_mul]

/-- For a `k`-regular graph on `n` vertices, the Seidel matrix maps the constant vector with
value `a` to the constant vector with value `(n - 1 - 2k) a`. In particular the all-one vector is
a Seidel eigenvector with eigenvalue `n - 1 - 2k`. -/
theorem IsRegularOfDegree.seidelMatrix_mulVec_const {k : ℕ} (hG : G.IsRegularOfDegree k)
    (a : R) :
    G.seidelMatrix R *ᵥ Function.const V a =
      Function.const V (((Fintype.card V : R) - 1 - 2 * k) * a) := by
  rw [seidelMatrix_eq_of_one_sub_one_sub_two_nsmul_adjMatrix, sub_mulVec, sub_mulVec,
    one_mulVec, smul_mulVec]
  ext v
  rw [Pi.sub_apply, Pi.sub_apply, Pi.smul_apply, adjMatrix_mulVec_const_apply_of_regular hG]
  simp [mulVec, dotProduct, sub_mul, two_mul, add_mul, nsmul_eq_mul]

end Eigenvectors

section SeidelSwitch

variable [Fintype V] (U : Set V) [DecidablePred (· ∈ U)]

/-- Switching with respect to `U` conjugates the Seidel matrix by the diagonal matrix with `-1` at
the vertices of `U` and `1` elsewhere. -/
theorem seidelMatrix_switch [NonAssocRing R] :
    (G.switch U).seidelMatrix R =
      diagonal (fun v => if v ∈ U then (-1 : R) else 1) * G.seidelMatrix R *
        diagonal (fun v => if v ∈ U then (-1 : R) else 1) := by
  ext u v
  rw [mul_diagonal, diagonal_mul]
  by_cases huv : u = v
  · simp [huv]
  · by_cases hG : G.Adj u v <;> by_cases hu : u ∈ U <;> by_cases hv : v ∈ U <;>
      simp [huv, hG, hu, hv]

/-- Switching does not change the characteristic polynomial of the Seidel matrix: the Seidel
matrices of switching equivalent graphs have the same characteristic polynomial. -/
@[simp]
theorem charpoly_seidelMatrix_switch [CommRing R] :
    ((G.switch U).seidelMatrix R).charpoly = (G.seidelMatrix R).charpoly := by
  have hD : diagonal (fun v => if v ∈ U then (-1 : R) else 1) *
      diagonal (fun v => if v ∈ U then (-1 : R) else 1) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext v
    split_ifs <;> simp
  rw [seidelMatrix_switch, charpoly_mul_comm, ← mul_assoc, hD, one_mul]

end SeidelSwitch

end SimpleGraph
