/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Matching.Hall

/-!
# Examples of multiset capacitated matchings

These examples exercise Kőnig's theorem, the Kőnig–Ore formula and Hall's theorem for multiset
capacitated matchings in bipartite multigraphs.

The first example is a single edge with capacity two at both ends. Its largest multiset
capacitated matching uses that edge twice, so it is not an ordinary matching, and its least
vertex cover is one end, of weight two.

The second example is a star with centre `0` and leaves `1` and `2`, together with an isolated
vertex `3`, with sides `{0, 3}` and `{1, 2}`. The capacity of leaf `1` is zero, so no multiset
capacitated matching uses the edge to it. With capacity two at the centre and one at leaf `2` and
at the isolated vertex, each of `{0}` and `{3}` is an explicit subset of the side `{0, 3}`
violating Hall's condition, the largest deficiency is two and the largest multiset capacitated
matching has size one. Lowering the capacities of the centre and of the isolated vertex to one and
zero restores Hall's condition, and some multiset capacitated matching then saturates every vertex,
including those of capacity zero.
-/

public section

open Finset
open scoped Graph

namespace TauCeti.Examples.CapacitatedMatching

open Graph

/-! ### One edge used twice -/

/-- One edge joining two vertices. -/
abbrev singleEdge : Graph Bool Unit :=
  banana false true Set.univ

/-- The edge type of `singleEdge` is finite. -/
noncomputable local instance : Fintype E(singleEdge) := Fintype.ofFinite _

/-- An end of the edge of `singleEdge`, as an actual vertex. -/
abbrev endpoint (b : Bool) : V(singleEdge) :=
  ⟨b, by cases b <;> simp⟩

/-- The edge of `singleEdge`. -/
abbrev edge : E(singleEdge) :=
  ⟨(), by simp⟩

private theorem univ_edgeSet : (univ : Finset E(singleEdge)) = {edge} := by
  ext; simp [Subsingleton.elim _ edge]

private theorem incidentEdges_singleton (v : V(singleEdge)) :
    singleEdge.incidentEdges {v} = {edge} := by
  obtain ⟨b, hb⟩ := v
  ext e
  simp only [mem_incidentEdges, mem_singleton, exists_eq_left, banana_inc, Set.mem_univ, true_and,
    Subsingleton.elim e edge, iff_true]
  cases b <;> simp

/-- The two ends of `singleEdge` form a bipartition. -/
theorem isBipartition_singleEdge :
    singleEdge.IsBipartition {endpoint false} {endpoint true} where
  disjoint := by simp
  mem_or_mem := by
    rintro ⟨b, hb⟩
    cases b <;> simp
  isLink := by
    rintro e ⟨x, hx⟩ ⟨y, hy⟩ h
    simp only [banana_isLink, Set.mem_univ, true_and] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-- Capacity two at both ends of `singleEdge`. -/
abbrev capTwo : V(singleEdge) → ℕ := fun _ ↦ 2

/-- Using the edge twice is a multiset capacitated matching for capacity two at both ends. -/
theorem isCapacitatedMatching_two : singleEdge.IsCapacitatedMatching capTwo fun _ ↦ 2 :=
  isCapacitatedMatching_def.2 fun v ↦ by simp [incidentEdges_singleton]

/-- With capacity two at both ends, the largest multiset capacitated matching has size two. -/
theorem isGreatest_sum_singleEdge :
    IsGreatest {n | ∃ x, singleEdge.IsCapacitatedMatching capTwo x ∧ ∑ e, x e = n} 2 :=
  ⟨⟨_, isCapacitatedMatching_two, by simp [univ_edgeSet]⟩, fun _ ⟨_, hx, hn⟩ ↦
    hn ▸ (hx.sum_le_sum_of_isVertexCover isBipartition_singleEdge.isVertexCover_left).trans_eq
      (by simp)⟩

/-- With capacity two at both ends, the least weight of a vertex cover is two. -/
theorem isLeast_sum_singleEdge :
    IsLeast {n | ∃ C : Finset V(singleEdge), singleEdge.IsVertexCover (C : Set _) ∧
      ∑ v ∈ C, capTwo v = n} 2 :=
  ⟨⟨_, isBipartition_singleEdge.isVertexCover_left, by simp⟩, fun _ ⟨_, hC, hn⟩ ↦
    hn ▸ (by simp [univ_edgeSet] : 2 = ∑ e, (fun _ ↦ 2) e).trans_le
      (isCapacitatedMatching_two.sum_le_sum_of_isVertexCover hC)⟩

/-- The only largest multiset capacitated matching uses the edge twice. -/
theorem setOf_sum_eq_two :
    {x | singleEdge.IsCapacitatedMatching capTwo x ∧ ∑ e, x e = 2} = {fun _ ↦ 2} := by
  ext x
  refine ⟨fun ⟨_, hx⟩ ↦ funext fun e ↦ ?_, fun hx ↦ ?_⟩
  · rw [Subsingleton.elim e edge]
    simpa [univ_edgeSet] using hx
  · rw [Set.mem_singleton_iff.1 hx]
    exact ⟨isCapacitatedMatching_two, by simp [univ_edgeSet]⟩

/-- Kőnig's theorem produces a matching and a cover of common value two. -/
example : ∃ (x : E(singleEdge) → ℕ) (C : Finset V(singleEdge)),
    singleEdge.IsCapacitatedMatching capTwo x ∧ singleEdge.IsVertexCover (C : Set _) ∧
      ∑ e, x e = 2 ∧ ∑ v ∈ C, capTwo v = 2 := by
  obtain ⟨x, C, hx, hC, hxC⟩ :=
    isBipartition_singleEdge.exists_isCapacitatedMatching_isVertexCover_sum_eq capTwo
  have h₁ := isGreatest_sum_singleEdge.2 ⟨x, hx, rfl⟩
  have h₂ := isLeast_sum_singleEdge.2 ⟨C, hC, rfl⟩
  exact ⟨x, C, hx, hC, by omega, by omega⟩

/-! ### Zero capacities, an isolated vertex and Hall obstructions -/

/-- The leaves `1` and `2` reached by the edges `0` and `1` of `star`. -/
def starEnd : Fin 2 → Fin 4
  | 0 => 1
  | 1 => 2

/-- Edge `0` of `star` ends at leaf `1`. -/
@[simp]
theorem starEnd_zero : starEnd 0 = 1 :=
  by simp [starEnd]

/-- Edge `1` of `star` ends at leaf `2`. -/
@[simp]
theorem starEnd_one : starEnd 1 = 2 :=
  by simp [starEnd]

/-- The star with centre `0`, joined to leaf `1` by edge `0` and to leaf `2` by edge `1`, together
with an isolated vertex `3`. -/
def star : Graph (Fin 4) (Fin 2) where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink e x y := s(x, y) = s(0, starEnd e)
  isLink_symm _ _ := ⟨fun _ _ h ↦ Sym2.eq_swap.trans h⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := by
    have := h.trans h'.symm
    rw [Sym2.eq_iff] at this
    tauto
  edge_mem_iff_exists_isLink e := ⟨fun _ ↦ ⟨0, starEnd e, rfl⟩, fun _ ↦ trivial⟩
  left_mem_of_isLink := by simp

/-- Every vertex of `Fin 4` is an actual vertex of `star`. -/
theorem vertexSet_star : V(star) = Set.univ :=
  by simp [star]

/-- Every edge identity of `Fin 2` is an actual edge of `star`. -/
theorem edgeSet_star : E(star) = Set.univ :=
  by simp [star]

/-- The edge type of `star` is finite. -/
noncomputable local instance : Fintype E(star) := Fintype.ofFinite _

/-- A vertex of `star`, as an actual vertex. -/
abbrev vtx (i : Fin 4) : V(star) :=
  ⟨i, vertexSet_star ▸ Set.mem_univ i⟩

/-- An edge of `star`, as an actual edge. -/
abbrev edg (i : Fin 2) : E(star) :=
  ⟨i, edgeSet_star ▸ Set.mem_univ i⟩

/-- An edge of `star` links its centre to the leaf selected by its identity. -/
@[simp]
theorem star_isLink {e : Fin 2} {x y : Fin 4} :
    star.IsLink e x y ↔ s(x, y) = s(0, starEnd e) :=
  by simp [star]

@[simp]
private theorem star_inc {e : Fin 2} {x : Fin 4} : star.Inc e x ↔ x = 0 ∨ x = starEnd e := by
  simp only [Inc, star_isLink, Sym2.eq_iff]
  constructor
  · rintro ⟨y, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ <;> simp
  · rintro (rfl | rfl)
    exacts [⟨starEnd e, by simp⟩, ⟨0, by simp⟩]

private theorem univ_edgeSet_star : (univ : Finset E(star)) = {edg 0, edg 1} := by
  ext ⟨e, he⟩
  fin_cases e <;> simp

private theorem incidentEdges_vtx_zero : star.incidentEdges {vtx 0} = {edg 0, edg 1} := by
  ext ⟨e, he⟩
  fin_cases e <;> simp

private theorem incidentEdges_vtx_one : star.incidentEdges {vtx 1} = {edg 0} := by
  ext ⟨e, he⟩
  fin_cases e <;> simp [starEnd]

private theorem incidentEdges_vtx_two : star.incidentEdges {vtx 2} = {edg 1} := by
  ext ⟨e, he⟩
  fin_cases e <;> simp [starEnd]

private theorem incidentEdges_vtx_three : star.incidentEdges {vtx 3} = ∅ := by
  ext ⟨e, he⟩
  fin_cases e <;> simp [starEnd]

private theorem forall_vtx {P : V(star) → Prop} :
    (∀ v, P v) ↔ P (vtx 0) ∧ P (vtx 1) ∧ P (vtx 2) ∧ P (vtx 3) := by
  refine ⟨fun h ↦ ⟨h _, h _, h _, h _⟩, fun h ⟨i, _⟩ ↦ ?_⟩
  fin_cases i
  exacts [h.1, h.2.1, h.2.2.1, h.2.2.2]

private theorem star_adj_zero_two : star.Adj 0 2 :=
  ⟨1, rfl⟩

private theorem not_star_adj_three (y : Fin 4) : ¬star.Adj 3 y := by
  rintro ⟨e, he⟩
  rw [star_isLink, Sym2.eq_iff] at he
  fin_cases e <;> simp [starEnd] at he

/-- The sides `{0, 3}` and `{1, 2}` form a bipartition of `star`. -/
theorem isBipartition_star : star.IsBipartition {vtx 0, vtx 3} {vtx 1, vtx 2} where
  disjoint := by simp
  mem_or_mem := by
    rintro ⟨i, -⟩
    fin_cases i <;> simp
  isLink := by
    rintro e ⟨x, _⟩ ⟨y, _⟩ h
    rw [star_isLink, Sym2.eq_iff] at h
    revert h
    fin_cases e <;> rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [starEnd]

/-- Capacities two, zero, one and one at the vertices `0`, `1`, `2` and `3` of `star`. -/
def capacity (v : V(star)) : ℕ :=
  match v.1 with
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | 3 => 1

/-- The centre of `star` has capacity two. -/
@[simp]
theorem capacity_vtx_zero : capacity (vtx 0) = 2 :=
  by simp [capacity]

/-- Leaf `1` of `star` has capacity zero. -/
@[simp]
theorem capacity_vtx_one : capacity (vtx 1) = 0 :=
  by simp [capacity]

/-- Leaf `2` of `star` has capacity one. -/
@[simp]
theorem capacity_vtx_two : capacity (vtx 2) = 1 :=
  by simp [capacity]

/-- The isolated vertex `3` of `star` has capacity one. -/
@[simp]
theorem capacity_vtx_three : capacity (vtx 3) = 1 :=
  by simp [capacity]

/-- No multiset capacitated matching uses edge `0`, since leaf `1` has capacity zero. -/
theorem eq_zero_of_isCapacitatedMatching {x : E(star) → ℕ}
    (hx : star.IsCapacitatedMatching capacity x) : x (edg 0) = 0 := by
  simpa [incidentEdges_vtx_one, capacity] using isCapacitatedMatching_def.1 hx (vtx 1)

/-- Using edge `1` once is a multiset capacitated matching. -/
theorem isCapacitatedMatching_single :
    star.IsCapacitatedMatching capacity (Pi.single (edg 1) 1) := by
  rw [isCapacitatedMatching_def, forall_vtx]
  simp [incidentEdges_vtx_zero, incidentEdges_vtx_one, incidentEdges_vtx_two,
    incidentEdges_vtx_three, capacity]

/-- The largest multiset capacitated matching has size one, by the Kőnig–Ore inequality for the
whole side `{0, 3}`. -/
theorem isGreatest_sum_star :
    IsGreatest {n | ∃ x, star.IsCapacitatedMatching capacity x ∧ ∑ e, x e = n} 1 := by
  refine ⟨⟨_, isCapacitatedMatching_single, by simp [univ_edgeSet_star]⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have h₁ := hx.sum_add_sum_le isBipartition_star subset_rfl
  have h₂ := sum_le_sum_of_subset (f := capacity) (neighborsIn_subset (G := star)
    (S := {vtx 0, vtx 3}) (T := {vtx 1, vtx 2}))
  simp only [mem_singleton, Subtype.mk.injEq, Fin.reduceEq, not_false_eq_true, sum_insert,
    sum_singleton, capacity] at h₁ h₂
  omega

/-- Each vertex of the side `{0, 3}` alone violates Hall's condition: the centre `0` has capacity
two while its neighbours have total capacity one, and the isolated vertex `3` has capacity one but
no neighbours. -/
theorem sum_neighborsIn_lt {v : V(star)} (hv : v ∈ ({vtx 0, vtx 3} : Finset V(star))) :
    ∑ w ∈ star.neighborsIn {v} {vtx 1, vtx 2}, capacity w < ∑ w ∈ {v}, capacity w := by
  rw [mem_insert, mem_singleton] at hv
  rcases hv with rfl | rfl
  · calc ∑ w ∈ star.neighborsIn {vtx 0} {vtx 1, vtx 2}, capacity w
        ≤ ∑ w ∈ {vtx 1, vtx 2}, capacity w := sum_le_sum_of_subset neighborsIn_subset
      _ < ∑ w ∈ {vtx 0}, capacity w := by simp [capacity]
  · have : star.neighborsIn {vtx 3} {vtx 1, vtx 2} = ∅ := by
      ext
      simp [not_star_adj_three]
    simp [this, capacity]

/-- **A capacitated Hall obstruction.** No multiset capacitated matching saturates the side
`{0, 3}`, as the subset `{3}` witnesses. -/
theorem not_exists_saturating_left :
    ¬∃ x, star.IsCapacitatedMatching capacity x ∧
      ∀ v ∈ ({vtx 0, vtx 3} : Finset V(star)), ∑ e ∈ star.incidentEdges {v}, x e = capacity v := by
  rw [isBipartition_star.exists_isCapacitatedMatching_saturating_left_iff]
  exact fun h ↦ (sum_neighborsIn_lt (v := vtx 3) (by simp)).not_ge (h {vtx 3} (by simp))

/-- By the Kőnig–Ore formula, the largest deficiency `b(S) - b(N(S))` of a subset `S` of the side
`{0, 3}` is two. -/
theorem sup_deficiency_eq_two :
    (({vtx 0, vtx 3} : Finset V(star)).powerset.sup fun S ↦
      ∑ v ∈ S, capacity v - ∑ v ∈ star.neighborsIn S {vtx 1, vtx 2}, capacity v) = 2 := by
  have := (isBipartition_star.isGreatest_sum_isCapacitatedMatching capacity).unique
    isGreatest_sum_star
  have hL : ∑ v ∈ ({vtx 0, vtx 3} : Finset V(star)), capacity v = 3 := by simp [capacity]
  omega

/-- Capacities one, zero, one and zero at the vertices `0`, `1`, `2` and `3` of `star`. -/
def balancedCapacity (v : V(star)) : ℕ :=
  match v.1 with
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | 3 => 0

/-- The centre of `star` has balanced capacity one. -/
@[simp]
theorem balancedCapacity_vtx_zero : balancedCapacity (vtx 0) = 1 :=
  by simp [balancedCapacity]

/-- Leaf `1` of `star` has balanced capacity zero. -/
@[simp]
theorem balancedCapacity_vtx_one : balancedCapacity (vtx 1) = 0 :=
  by simp [balancedCapacity]

/-- Leaf `2` of `star` has balanced capacity one. -/
@[simp]
theorem balancedCapacity_vtx_two : balancedCapacity (vtx 2) = 1 :=
  by simp [balancedCapacity]

/-- The isolated vertex `3` of `star` has balanced capacity zero. -/
@[simp]
theorem balancedCapacity_vtx_three : balancedCapacity (vtx 3) = 0 :=
  by simp [balancedCapacity]

/-- With zero capacity at leaf `1` and at the isolated vertex `3`, Hall's condition holds and both
sides have total capacity one, so some multiset capacitated matching saturates every vertex. -/
theorem exists_saturating :
    ∃ x, star.IsCapacitatedMatching balancedCapacity x ∧
      ∀ v, ∑ e ∈ star.incidentEdges {v}, x e = balancedCapacity v := by
  rw [isBipartition_star.exists_isCapacitatedMatching_saturating_iff]
  refine ⟨by simp [balancedCapacity], fun S hS ↦ ?_⟩
  by_cases h0 : vtx 0 ∈ S
  · -- The leaf `2` is a neighbour of `S` and carries the whole capacity of the side `{0, 3}`.
    have h2 : vtx 2 ∈ star.neighborsIn S {vtx 1, vtx 2} :=
      mem_neighborsIn.2 ⟨by simp, vtx 0, h0, star_adj_zero_two⟩
    calc ∑ v ∈ S, balancedCapacity v ≤ ∑ v ∈ {vtx 0, vtx 3}, balancedCapacity v :=
          sum_le_sum_of_subset hS
      _ = balancedCapacity (vtx 2) := by simp [balancedCapacity]
      _ ≤ _ := single_le_sum (fun _ _ ↦ Nat.zero_le _) h2
  · -- Otherwise `S` lies in `{3}`, of capacity zero.
    have hS3 : S ⊆ {vtx 3} := fun v hv ↦ by
      rcases mem_insert.1 (hS hv) with rfl | h
      exacts [absurd hv h0, h]
    calc ∑ v ∈ S, balancedCapacity v ≤ ∑ v ∈ {vtx 3}, balancedCapacity v :=
          sum_le_sum_of_subset hS3
      _ = 0 := by simp [balancedCapacity]
      _ ≤ _ := Nat.zero_le _

end TauCeti.Examples.CapacitatedMatching
