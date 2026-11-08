/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Orientation.Hakimi

/-!
# Examples of prescribed and bounded indegree orientations

These examples exercise the boundary cases of the prescribed- and bounded-indegree theorems for
finite multigraphs.  A loop contributes one unit of indegree, while parallel edges retain
independent choices of head.  The examples also exhibit unequal feasible bounds, each of the two
possible subset obstructions, failure of the total-balance condition despite all internal-edge
inequalities, and the empty and isolated-vertex cases.

The orientation criteria are due to S. L. Hakimi, *On the degrees of the vertices of a directed
graph*, J. Franklin Inst. 279 (1965), 290--308.
-/

public section

open Finset Set

namespace TauCeti.Examples.IndegreeOrientation

open Graph

/-! ### Loops and parallel edges -/

/-- The finite multigraph with one vertex and one loop used in the orientation examples. -/
abbrev oneLoop : Graph Unit Unit :=
  bouquet () Set.univ

/-- The finite vertex type of `oneLoop`. -/
noncomputable local instance : Fintype V(oneLoop) := Fintype.ofFinite _

/-- The finite edge type of `oneLoop`. -/
noncomputable local instance : Fintype E(oneLoop) := Fintype.ofFinite _

/-- The unique vertex of `oneLoop`. -/
abbrev loopVertex : V(oneLoop) :=
  ⟨(), by simp [oneLoop]⟩

/-- The unique orientation of the one-loop graph. -/
noncomputable def oneLoopOrientation : oneLoop.Orientation :=
  Orientation.ofEdgeEnds oneLoop

/-- A loop contributes one to the indegree of its vertex. -/
theorem oneLoopOrientation_indegree : oneLoopOrientation.indegree loopVertex = 1 := by
  have h := oneLoopOrientation.sum_indegree
  have hsum : ∑ v, oneLoopOrientation.indegree v =
      oneLoopOrientation.indegree loopVertex := by
    apply Finset.sum_eq_single loopVertex
    · intro v _ hv
      exact (hv (Subsingleton.elim v loopVertex)).elim
    · simp
  rw [hsum] at h
  simpa [oneLoop] using h

/-- Two vertices joined by two separately identified parallel edges. -/
abbrev twoParallel : Graph Bool Bool :=
  banana false true Set.univ

/-- The finite vertex type of `twoParallel`. -/
noncomputable local instance : Fintype V(twoParallel) := Fintype.ofFinite _

/-- The finite edge type of `twoParallel`. -/
noncomputable local instance : Fintype E(twoParallel) := Fintype.ofFinite _

/-- A Boolean endpoint as an actual vertex of `twoParallel`. -/
abbrev parallelVertex (b : Bool) : V(twoParallel) :=
  ⟨b, by cases b <;> simp [twoParallel]⟩

/-- Orient the two parallel edges in opposite directions by choosing the edge named `b` to have
head `b`. -/
noncomputable def oppositeParallelOrientation : twoParallel.Orientation :=
  Orientation.ofHead (fun e ↦ parallelVertex e.1) fun e ↦ by
    cases e with
    | mk b hb =>
      cases b <;> simp [twoParallel]

/-- The first of two parallel edges can point towards `false`. -/
example : oppositeParallelOrientation.head ⟨false, by simp [twoParallel]⟩ =
    parallelVertex false := by
  simp [oppositeParallelOrientation]

/-- The second parallel edge can independently point towards `true`. -/
example : oppositeParallelOrientation.head ⟨true, by simp [twoParallel]⟩ =
    parallelVertex true := by
  simp [oppositeParallelOrientation]

/-- Orienting the two parallel edges in opposite directions gives indegree one at every vertex. -/
theorem oppositeParallelOrientation_indegree (v : V(twoParallel)) :
    oppositeParallelOrientation.indegree v = 1 := by
  classical
  rw [Orientation.indegree_def, Finset.card_eq_one]
  refine ⟨⟨v.1, by simp [twoParallel]⟩, ?_⟩
  ext e
  simp [oppositeParallelOrientation, Subtype.ext_iff]

/-! ### Feasible unequal bounds -/

/-- The constant zero lower indegree bound on `twoParallel`. -/
private def parallelLower (_ : V(twoParallel)) : ℕ := 0

/-- The constant one upper indegree bound on `twoParallel`. -/
private def parallelUpper (_ : V(twoParallel)) : ℕ := 1

/-- The bounds zero and one are unequal at both vertices. -/
example (v : V(twoParallel)) : parallelLower v < parallelUpper v :=
  Nat.zero_lt_one

/-- The oppositely oriented parallel edges realize the unequal interval bounds `[0, 1]`. -/
example : ∀ v, oppositeParallelOrientation.indegree v ∈
    Set.Icc (parallelLower v) (parallelUpper v) := by
  intro v
  rw [oppositeParallelOrientation_indegree]
  exact ⟨Nat.zero_le _, le_rfl⟩

/-- The bounded-indegree criterion also detects feasibility of these unequal bounds. -/
example : ∃ o : twoParallel.Orientation,
    ∀ v, o.indegree v ∈ Set.Icc (parallelLower v) (parallelUpper v) := by
  rw [Graph.exists_orientation_indegree_mem_Icc_iff (a := parallelLower) (b := parallelUpper)
    (fun _ ↦ Nat.zero_le _)]
  constructor
  · intro S
    simpa [parallelUpper, oppositeParallelOrientation_indegree] using
      oppositeParallelOrientation.card_internalEdges_le_sum_indegree S
  · intro S
    simp [parallelLower]

/-! ### The two subset obstructions -/

/-- The impossible zero upper indegree bound on the vertex of `oneLoop`. -/
private def loopUpper (_ : V(oneLoop)) : ℕ := 0

/-- The singleton vertex set violates the upper-bound criterion for `loopUpper`. -/
private theorem loopUpper_certificate :
    ∑ v ∈ ({loopVertex} : Finset V(oneLoop)), loopUpper v <
      #(oneLoop.internalEdges {loopVertex}) := by
  classical
  simp only [loopUpper, sum_const_zero]
  apply Finset.card_pos.mpr
  refine ⟨⟨(), by simp [oneLoop]⟩, ?_⟩
  simp [loopVertex, oneLoop]

/-- The singleton vertex set witnesses the upper-bound obstruction: it contains one internal
loop but has total upper bound zero. -/
example : ∑ v ∈ ({loopVertex} : Finset V(oneLoop)), loopUpper v <
    #(oneLoop.internalEdges {loopVertex}) :=
  loopUpper_certificate

/-- Consequently no orientation of the one-loop graph has indegree at most zero. -/
example : ¬∃ o : oneLoop.Orientation, ∀ v, o.indegree v ≤ loopUpper v := by
  rw [exists_orientation_indegree_le_iff]
  push Not
  exact ⟨{loopVertex}, loopUpper_certificate⟩

/-- The finite graph with one isolated vertex. -/
abbrev isolated : Graph Unit Unit :=
  noEdge Set.univ Unit

/-- The finite vertex type of `isolated`. -/
noncomputable local instance : Fintype V(isolated) := Fintype.ofFinite _

/-- The finite edge type of `isolated`. -/
noncomputable local instance : Fintype E(isolated) := Fintype.ofFinite _

/-- The unique vertex of `isolated`. -/
abbrev isolatedVertex : V(isolated) :=
  ⟨(), by simp [isolated]⟩

/-- The impossible positive lower indegree bound on the isolated vertex. -/
private def isolatedLower (_ : V(isolated)) : ℕ := 1

/-- The isolated example's unique vertex is incident to no actual edges. -/
private theorem incidentEdges_isolatedVertex :
    isolated.incidentEdges {isolatedVertex} = ∅ := by
  ext e
  have he : False := by simpa [isolated] using e.2
  exact he.elim

/-- The singleton vertex set violates the lower-bound criterion for `isolatedLower`. -/
private theorem isolatedLower_certificate :
    #(isolated.incidentEdges {isolatedVertex}) <
      ∑ v ∈ ({isolatedVertex} : Finset V(isolated)), isolatedLower v := by
  simp [incidentEdges_isolatedVertex, isolatedLower]

/-- The singleton vertex set witnesses the lower-bound obstruction: its required lower indegree is
one, but it is incident to no edge. -/
example : #(isolated.incidentEdges {isolatedVertex}) <
    ∑ v ∈ ({isolatedVertex} : Finset V(isolated)), isolatedLower v :=
  isolatedLower_certificate

/-- Consequently no orientation can give an isolated vertex positive indegree. -/
example : ¬∃ o : isolated.Orientation, ∀ v, isolatedLower v ≤ o.indegree v := by
  rw [exists_orientation_le_indegree_iff]
  push Not
  exact ⟨{isolatedVertex}, isolatedLower_certificate⟩

/-! ### Prescribed indegrees and total balance -/

/-- The impossible prescription of indegree two on the one-loop graph. -/
private def excessiveLoopIndegree (_ : V(oneLoop)) : ℕ := 2

/-- Prescribing indegree two on the one-loop graph satisfies every internal-edge inequality. -/
example (S : Finset V(oneLoop)) :
    #(oneLoop.internalEdges S) ≤ ∑ v ∈ S, excessiveLoopIndegree v := by
  classical
  refine (oneLoopOrientation.card_internalEdges_le_sum_indegree S).trans ?_
  apply Finset.sum_le_sum
  intro v hv
  have hvl : v = loopVertex := Subsingleton.elim _ _
  norm_num [hvl, excessiveLoopIndegree, oneLoopOrientation_indegree]

/-- The same prescription fails total balance: it asks a single loop to contribute two units. -/
example : (∑ v, excessiveLoopIndegree v) ≠ Fintype.card E(oneLoop) := by
  norm_num [excessiveLoopIndegree, oneLoop]

/-- Thus the internal-edge inequalities alone do not imply existence of a prescribed-indegree
orientation; the total-balance condition in Hakimi's theorem is essential. -/
example : ¬∃ o : oneLoop.Orientation, ∀ v, o.indegree v = excessiveLoopIndegree v := by
  rw [exists_orientation_indegree_eq_iff]
  simp [excessiveLoopIndegree, oneLoop]

/-! ### Empty and isolated graphs -/

/-- Every orientation gives an isolated vertex indegree zero. -/
example (o : isolated.Orientation) : o.indegree isolatedVertex = 0 := by
  classical
  simp [Orientation.indegree_def]

/-- The graph with no actual vertices or edges. -/
abbrev emptyGraph : Graph Empty Unit :=
  noEdge ∅ Unit

/-- The finite vertex type of `emptyGraph`. -/
noncomputable local instance : Fintype V(emptyGraph) := Fintype.ofFinite _

/-- The finite edge type of `emptyGraph`. -/
noncomputable local instance : Fintype E(emptyGraph) := Fintype.ofFinite _

/-- The empty graph admits a vacuous prescribed-indegree orientation. -/
example : ∃ o : emptyGraph.Orientation, ∀ v, o.indegree v = 0 := by
  exact ⟨Orientation.ofEdgeEnds emptyGraph, fun v ↦ v.1.elim⟩

end TauCeti.Examples.IndegreeOrientation
