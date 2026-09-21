/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Basic
public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Coordinates

/-!
# The adjacency array of a graph and the graph of an array

A graph on `ℕ` is read as a `Bool`-valued array through its edge coordinates: the adjacency array
`SimpleGraph.adjArray G` is `graphCoordEquiv G` placed on the off-diagonal pairs, with `false` on
the diagonal, so it is `true` exactly on edges. An array is read back as a graph by
`graphOfArray`, the `SimpleGraph.fromRel` of the array: `i` and `j` are adjacent when they are
distinct and the array is `true` at `(i, j)` or at `(j, i)`. The two are measurable, mutually
inverse on the symmetric arrays with `false` diagonal, and intertwine relabelling of the graph
with the diagonal relabelling of the array.

## Main results

* `SimpleGraph.adjArray`, `SimpleGraph.adjArray_apply`, `SimpleGraph.measurable_adjArray`,
  `SimpleGraph.adjArray_mem_symmetricArraysWithDiag`, `SimpleGraph.adjArray_comap`.
* `TauCeti.DenseGraphLimits.graphOfArray`, `graphOfArray_adj`, `measurable_graphOfArray`,
  `graphOfArray_pairReindex`.
* `SimpleGraph.graphOfArray_adjArray`, `TauCeti.DenseGraphLimits.adjArray_graphOfArray` — the
  two round trips.
-/

public section

open MeasureTheory Set TauCeti.Probability SimpleGraph

namespace TauCeti

namespace DenseGraphLimits

/-- Edge coordinates read as an array: `false` on the diagonal, the coordinate at `s(i, j)`
elsewhere. -/
noncomputable def edgeCoordToArray (f : EdgeIndex → Bool) : ℕ × ℕ → Bool := fun p =>
  if h : s(p.1, p.2).IsDiag then false else f ⟨s(p.1, p.2), h⟩

/-- Off the diagonal, edge coordinates read as an array are the coordinates. -/
theorem edgeCoordToArray_apply_of_not_isDiag (f : EdgeIndex → Bool) {i j : ℕ}
    (h : ¬ s(i, j).IsDiag) : edgeCoordToArray f (i, j) = f ⟨s(i, j), h⟩ := by
  simp [edgeCoordToArray, h]

/-- On the diagonal, edge coordinates read as an array are `false`. -/
@[simp]
theorem edgeCoordToArray_diag (f : EdgeIndex → Bool) (i : ℕ) :
    edgeCoordToArray f (i, i) = false := by
  simp [edgeCoordToArray]

/-- Edge coordinates read as an array land in the symmetric arrays with `false` diagonal. -/
theorem edgeCoordToArray_mem_symmetricArraysWithDiag (f : EdgeIndex → Bool) :
    edgeCoordToArray f ∈ symmetricArraysWithDiag Bool false :=
  mem_symmetricArraysWithDiag_iff.2
    ⟨fun i j => by simp only [edgeCoordToArray, Sym2.eq_swap], fun i => edgeCoordToArray_diag f i⟩

/-- The adjacency array of a graph on `ℕ`, through its edge coordinates. -/
noncomputable def _root_.SimpleGraph.adjArray (G : SimpleGraph ℕ) : ℕ × ℕ → Bool :=
  edgeCoordToArray (graphCoordEquiv G)

open Classical in
/-- The adjacency array is `true` exactly on edges. -/
@[simp]
theorem _root_.SimpleGraph.adjArray_apply (G : SimpleGraph ℕ) (i j : ℕ) :
    G.adjArray (i, j) = decide (G.Adj i j) := by
  simp only [SimpleGraph.adjArray, edgeCoordToArray]
  by_cases h : s(i, j).IsDiag
  · have : i = j := Sym2.mk_isDiag_iff.mp h
    subst this; simp [h]
  · simp only [h, dite_false]
    rw [Bool.eq_iff_iff, SimpleGraph.graphCoordEquiv_apply]
    simp [SimpleGraph.mem_edgeSet]

open Classical in
/-- Reading a graph as an array is measurable. -/
theorem _root_.SimpleGraph.measurable_adjArray : Measurable SimpleGraph.adjArray := by
  refine Measurable.of_eval fun p => ?_
  obtain ⟨i, j⟩ := p
  simp only [SimpleGraph.adjArray_apply]
  exact (measurable_of_countable (fun q : Prop => decide q)).comp
    (measurable_iff_adj.1 measurable_id i j)

/-- The adjacency array of a graph is symmetric with `false` diagonal. -/
theorem _root_.SimpleGraph.adjArray_mem_symmetricArraysWithDiag (G : SimpleGraph ℕ) :
    G.adjArray ∈ symmetricArraysWithDiag Bool false :=
  edgeCoordToArray_mem_symmetricArraysWithDiag _

/-- Relabelling the graph is relabelling both axes of its adjacency array. -/
theorem _root_.SimpleGraph.adjArray_comap (σ : Equiv.Perm ℕ) (G : SimpleGraph ℕ) :
    (SimpleGraph.comap ⇑σ G).adjArray = pairReindex σ σ G.adjArray := by
  funext ⟨i, j⟩
  simp only [SimpleGraph.adjArray, edgeCoordToArray, pairReindex_apply]
  by_cases h : s(i, j).IsDiag
  · have h' : s(σ i, σ j).IsDiag := by
      simpa [Sym2.mk_isDiag_iff] using congrArg σ (Sym2.mk_isDiag_iff.mp h)
    simp [h, h']
  · have h' : ¬ s(σ i, σ j).IsDiag := fun h' =>
      h (Sym2.mk_isDiag_iff.mpr (σ.injective (Sym2.mk_isDiag_iff.mp h')))
    simp only [h, h', dite_false]
    rw [Equiv.Perm.graphCoordEquiv_comap]
    -- the relabelled edge coordinate is the coordinate of the relabelled pair
    exact congrArg (graphCoordEquiv G)
      (Subtype.ext (by simp only [Equiv.Perm.edgeIndexMap_val, Sym2.map_mk]))

/-- The graph of an array: `i` and `j` are adjacent when they are distinct and the array is
`true` at `(i, j)` or at `(j, i)`, so on a symmetric array at either. -/
def graphOfArray (x : ℕ × ℕ → Bool) : SimpleGraph ℕ :=
  SimpleGraph.fromRel fun i j => x (i, j) = true

/-- Adjacency in the graph of an array. -/
@[simp]
theorem graphOfArray_adj (x : ℕ × ℕ → Bool) (i j : ℕ) :
    (graphOfArray x).Adj i j ↔ i ≠ j ∧ (x (i, j) = true ∨ x (j, i) = true) :=
  SimpleGraph.fromRel_adj _ _ _

/-- Reading an array as a graph is measurable. -/
theorem measurable_graphOfArray : Measurable graphOfArray := by
  refine measurable_iff_adj.2 fun i j => ?_
  simp only [graphOfArray_adj]
  refine measurable_to_prop ?_
  by_cases hij : i = j
  · simp [hij]
  · have : (fun x : ℕ × ℕ → Bool => i ≠ j ∧ (x (i, j) = true ∨ x (j, i) = true)) ⁻¹' {True}
        = (fun x : ℕ × ℕ → Bool => x (i, j)) ⁻¹' {true} ∪
            (fun x : ℕ × ℕ → Bool => x (j, i)) ⁻¹' {true} := by
      ext x; simp [hij]
    rw [this]
    exact ((measurable_pi_apply _) (measurableSet_singleton _)).union
      ((measurable_pi_apply _) (measurableSet_singleton _))

/-- The graph of the adjacency array of a graph is the graph. -/
@[simp]
theorem _root_.SimpleGraph.graphOfArray_adjArray (G : SimpleGraph ℕ) :
    graphOfArray G.adjArray = G := by
  ext i j
  simp only [graphOfArray_adj, SimpleGraph.adjArray_apply, decide_eq_true_eq]
  exact ⟨fun ⟨_, h⟩ => h.elim id G.adj_symm, fun h => ⟨G.ne_of_adj h, Or.inl h⟩⟩

/-- The adjacency array of the graph of a symmetric `false`-diagonal array is the array. -/
@[simp]
theorem adjArray_graphOfArray {x : ℕ × ℕ → Bool} (hx : x ∈ symmetricArraysWithDiag Bool false) :
    (graphOfArray x).adjArray = x := by
  obtain ⟨hs, hd⟩ := mem_symmetricArraysWithDiag_iff.1 hx
  funext ⟨i, j⟩
  rw [SimpleGraph.adjArray_apply]
  by_cases hij : i = j
  · subst hij; simp [hd]
  · simp [graphOfArray_adj, hij, hs i j]

/-- The graph of a relabelled array is the relabelling of its graph. -/
theorem graphOfArray_pairReindex (σ : Equiv.Perm ℕ) (x : ℕ × ℕ → Bool) :
    graphOfArray (pairReindex σ σ x) = SimpleGraph.comap ⇑σ (graphOfArray x) := by
  ext i j
  simp [graphOfArray_adj, pairReindex_apply, σ.injective.ne_iff]

end DenseGraphLimits

end TauCeti
