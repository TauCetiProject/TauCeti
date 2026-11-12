/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Matching.Network
public import TauCeti.Combinatorics.Graph.Matching.Capacitated

/-!
# Capacitated matchings as integral bipartite flows

A multiset capacitated matching is equivalent to an integer flow in the bipartite network.
The value on an original edge is its multiplicity; the terminal arrow at a vertex carries the
sum of its incident multiplicities. Conservation therefore determines all terminal-arrow
values from the original edges. The equivalence preserves matching size and flow value,
including for empty sides, isolated vertices, and parallel edges.

This is the flow side of the classical network proof of capacitated Kőnig's theorem; see
A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
Section 21.1. The cut--cover correspondence is in
`TauCeti.Combinatorics.Graph.Matching.Network`.
-/

public section

open Finset Sum TauCeti
open scoped Graph

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β}
variable [Fintype V(G)] [Fintype E(G)] {L R : Finset V(G)}

omit [Fintype V(G)] in
/-- The assignment associated to edge multiplicities: original arrows carry the multiplicity,
and each terminal arrow carries the total usage of its vertex. -/
noncomputable def bipartiteMatchingAssignment (L R : Finset V(G)) (x : E(G) → ℕ) :
    Assignment (AuxTerminalHom (G.BipartiteHom L) L R) ℤ :=
  auxTerminalCapacity (fun {_ _} e ↦ (x e.edge : ℤ))
    (fun a ↦ ∑ e ∈ G.incidentEdges {a}, (x e : ℤ))
    (fun a ↦ ∑ e ∈ G.incidentEdges {a}, (x e : ℤ))

omit [Fintype V(G)] in
@[simp]
theorem bipartiteMatchingAssignment_original (x : E(G) → ℕ) {a b : V(G)}
    (e : G.BipartiteHom L a b) :
    bipartiteMatchingAssignment L R x (AuxTerminalHom.original e) = x e.edge :=
  auxTerminalCapacity_original _ _ _ e

omit [Fintype V(G)] in
@[simp]
theorem bipartiteMatchingAssignment_source (x : E(G) → ℕ) {a : V(G)} (ha : a ∈ L) :
    bipartiteMatchingAssignment L R x (AuxTerminalHom.source ha) =
      ∑ e ∈ G.incidentEdges {a}, (x e : ℤ) :=
  auxTerminalCapacity_source _ _ _ ha

omit [Fintype V(G)] in
@[simp]
theorem bipartiteMatchingAssignment_sink (x : E(G) → ℕ) {a : V(G)} (ha : a ∈ R) :
    bipartiteMatchingAssignment L R x (AuxTerminalHom.sink ha) =
      ∑ e ∈ G.incidentEdges {a}, (x e : ℤ) :=
  auxTerminalCapacity_sink _ _ _ ha

variable [DecidableEq V(G)]

private theorem conserve_matchingAssignment (hLR : G.IsBipartition L R)
    (x : E(G) → ℕ) (a : V(G)) :
    excessAt (bipartiteMatchingAssignment L R x) (inl a) = 0 := by
  rw [bipartiteMatchingAssignment, AuxTerminalHom.excessAt_inl,
    auxTerminalRestrict_auxTerminalCapacity, sum_auxTerminalCapacity_source,
    sum_auxTerminalCapacity_sink]
  rcases hLR.mem_or_mem a with ha | ha
  · rw [hLR.excessAt_bipartiteHom_left (fun e ↦ (x e : ℤ)) ha]
    simp [ha, disjoint_left.1 hLR.disjoint ha]
  · rw [hLR.excessAt_bipartiteHom_right (fun e ↦ (x e : ℤ)) ha]
    simp [ha, disjoint_right.1 hLR.disjoint ha]

/-- A multiset capacitated matching gives an integer flow with the same multiplicities on the
original edges and its vertex usages on the terminal arrows. -/
noncomputable def IsCapacitatedMatching.toBipartiteFlow {b : V(G) → ℕ} {x : E(G) → ℕ}
    (hx : G.IsCapacitatedMatching b x) (hLR : G.IsBipartition L R) :
    Flow (bipartiteCapacity L R b) (inr false) (inr true) where
  toFun := bipartiteMatchingAssignment L R x
  mem_Icc := ⟨by
    apply auxTerminalCapacity_nonneg
    · intro a b e
      exact Int.natCast_nonneg _
    · intro a _
      exact sum_nonneg fun _ _ ↦ Int.natCast_nonneg _
    · intro a _
      exact sum_nonneg fun _ _ ↦ Int.natCast_nonneg _, by
    intro v w e
    refine (AuxTerminalHom.forall_iff (P := fun {_ _} e ↦
      bipartiteMatchingAssignment L R x e ≤ bipartiteCapacity L R b e)).2
        ⟨fun a c e ↦ ?_, fun a ha ↦ ?_, fun a ha ↦ ?_⟩ e
    · rw [bipartiteMatchingAssignment_original, bipartiteCapacity_original]
      have hsize : ∑ e, x e ≤ ∑ a ∈ L, b a :=
        hx.sum_le_sum_of_isVertexCover hLR.isVertexCover_left
      have hle := (single_le_sum (fun _ _ ↦ Nat.zero_le _) (mem_univ e.edge)).trans hsize
      simp only [bipartiteLargeCapacity_def, Nat.cast_add, Nat.cast_one]
      exact_mod_cast hle.trans (Nat.le_add_right _ _)
    · rw [bipartiteMatchingAssignment_source, bipartiteCapacity_source]
      exact_mod_cast isCapacitatedMatching_def.1 hx a
    · rw [bipartiteMatchingAssignment_sink, bipartiteCapacity_sink]
      exact_mod_cast isCapacitatedMatching_def.1 hx a⟩
  conserve
    | inl a, _, _ => conserve_matchingAssignment hLR x a
    | inr false, h, _ => (h rfl).elim
    | inr true, _, h => (h rfl).elim
  excessAt_sink_nonneg := by
    rw [AuxTerminalHom.excessAt_inr_true]
    exact sum_nonneg fun _ _ ↦ sum_nonneg fun e _ ↦ by
      rw [AuxTerminalHom.eq_sink e, bipartiteMatchingAssignment_sink]
      exact sum_nonneg fun _ _ ↦ Int.natCast_nonneg _

@[simp]
theorem IsCapacitatedMatching.toBipartiteFlow_toFun {b : V(G) → ℕ} {x : E(G) → ℕ}
    (hx : G.IsCapacitatedMatching b x) (hLR : G.IsBipartition L R) :
    (hx.toBipartiteFlow hLR).toFun = bipartiteMatchingAssignment L R x :=
  (rfl)

/-- The integer flow associated to a matching has value equal to its size. -/
@[simp]
theorem IsCapacitatedMatching.val_toBipartiteFlow {b : V(G) → ℕ} {x : E(G) → ℕ}
    (hx : G.IsCapacitatedMatching b x) (hLR : G.IsBipartition L R) :
    (hx.toBipartiteFlow hLR).val = ∑ e, (x e : ℤ) := by
  rw [BoundedFlow.val_def, toBipartiteFlow_toFun, bipartiteMatchingAssignment,
    AuxTerminalHom.excessAt_inr_true]
  simp only [sum_auxTerminalCapacity_sink, sum_ite_mem, univ_inter]
  exact hLR.sum_sum_incidentEdges_right _

/-- Recover natural edge multiplicities from an integer flow, using the unique left-to-right
arrow belonging to each original edge. -/
noncomputable def IsBipartition.flowMultiplicity (hLR : G.IsBipartition L R)
    {b : V(G) → ℕ} (f : Flow (bipartiteCapacity L R b) (inr false) (inr true)) :
    E(G) → ℕ :=
  fun e ↦ (f.toFun (AuxTerminalHom.original (hLR.bipartiteEdgeEquiv.symm e).2.2)).toNat

/-- The recovered multiplicity on each original arrow is exactly its nonnegative integer flow. -/
@[simp]
theorem IsBipartition.natCast_flowMultiplicity (hLR : G.IsBipartition L R)
    {b : V(G) → ℕ} (f : Flow (bipartiteCapacity L R b) (inr false) (inr true))
    {a c : V(G)} (e : G.BipartiteHom L a c) :
    (hLR.flowMultiplicity f e.edge : ℤ) = f.toFun (AuxTerminalHom.original e) := by
  rw [flowMultiplicity, hLR.bipartiteEdgeEquiv_symm_apply_edge e,
    Int.toNat_of_nonneg (f.nonneg _)]

private theorem restrict_eq_multiplicity (hLR : G.IsBipartition L R)
    {b : V(G) → ℕ} (f : Flow (bipartiteCapacity L R b) (inr false) (inr true)) :
    auxTerminalRestrict f.toFun =
      fun {_ _} e ↦ (hLR.flowMultiplicity f e.edge : ℤ) := by
  funext a c e
  rw [auxTerminalRestrict_apply, hLR.natCast_flowMultiplicity]

/-- Conservation forces the source arrow at a left vertex to carry its total edge usage. -/
theorem IsBipartition.bipartiteFlow_source_eq_sum (hLR : G.IsBipartition L R)
    {b : V(G) → ℕ} (f : Flow (bipartiteCapacity L R b) (inr false) (inr true))
    {a : V(G)} (ha : a ∈ L) :
    f.toFun (AuxTerminalHom.source ha) =
      ∑ e ∈ G.incidentEdges {a}, (hLR.flowMultiplicity f e : ℤ) := by
  have hc := f.conserve (inl a) (by simp) (by simp)
  rw [AuxTerminalHom.excessAt_inl, restrict_eq_multiplicity hLR f,
    hLR.excessAt_bipartiteHom_left (fun e ↦ (hLR.flowMultiplicity f e : ℤ)) ha,
    AuxTerminalHom.sum_source ha,
    AuxTerminalHom.sum_sink_of_notMem (disjoint_left.1 hLR.disjoint ha)] at hc
  omega

/-- Conservation forces the sink arrow at a right vertex to carry its total edge usage. -/
theorem IsBipartition.bipartiteFlow_sink_eq_sum (hLR : G.IsBipartition L R)
    {b : V(G) → ℕ} (f : Flow (bipartiteCapacity L R b) (inr false) (inr true))
    {a : V(G)} (ha : a ∈ R) :
    f.toFun (AuxTerminalHom.sink ha) =
      ∑ e ∈ G.incidentEdges {a}, (hLR.flowMultiplicity f e : ℤ) := by
  have hc := f.conserve (inl a) (by simp) (by simp)
  rw [AuxTerminalHom.excessAt_inl, restrict_eq_multiplicity hLR f,
    hLR.excessAt_bipartiteHom_right (fun e ↦ (hLR.flowMultiplicity f e : ℤ)) ha,
    AuxTerminalHom.sum_source_of_notMem (disjoint_right.1 hLR.disjoint ha),
    AuxTerminalHom.sum_sink ha] at hc
  omega

/-- Every integral flow in the bipartite network recovers a feasible multiset matching. -/
theorem IsBipartition.isCapacitatedMatching_flowMultiplicity (hLR : G.IsBipartition L R)
    {b : V(G) → ℕ} (f : Flow (bipartiteCapacity L R b) (inr false) (inr true)) :
    G.IsCapacitatedMatching b (hLR.flowMultiplicity f) := by
  refine isCapacitatedMatching_def.2 fun a ↦ ?_
  rcases hLR.mem_or_mem a with ha | ha
  · have hle := f.le_upper (AuxTerminalHom.source ha)
    rw [hLR.bipartiteFlow_source_eq_sum f ha, bipartiteCapacity_source] at hle
    exact_mod_cast hle
  · have hle := f.le_upper (AuxTerminalHom.sink ha)
    rw [hLR.bipartiteFlow_sink_eq_sum f ha, bipartiteCapacity_sink] at hle
    exact_mod_cast hle

/-- Recovering multiplicities and then forming a flow preserves every arrow, including the
terminal arrows whose values are forced by conservation. -/
@[simp]
theorem IsBipartition.toBipartiteFlow_flowMultiplicity (hLR : G.IsBipartition L R)
    {b : V(G) → ℕ} (f : Flow (bipartiteCapacity L R b) (inr false) (inr true)) :
    ((hLR.isCapacitatedMatching_flowMultiplicity f).toBipartiteFlow hLR) = f := by
  apply Flow.ext
  funext v w e
  refine (AuxTerminalHom.forall_iff (P := fun {_ _} e ↦
    bipartiteMatchingAssignment L R (hLR.flowMultiplicity f) e = f.toFun e)).2
      ⟨fun a c e ↦ ?_, fun a ha ↦ ?_, fun a ha ↦ ?_⟩ e
  · simp
  · rw [bipartiteMatchingAssignment_source, hLR.bipartiteFlow_source_eq_sum f ha]
  · rw [bipartiteMatchingAssignment_sink, hLR.bipartiteFlow_sink_eq_sum f ha]

/-- Forming a flow from a multiset matching and recovering multiplicities is the identity. -/
@[simp]
theorem IsCapacitatedMatching.flowMultiplicity_toBipartiteFlow {b : V(G) → ℕ}
    {x : E(G) → ℕ} (hx : G.IsCapacitatedMatching b x) (hLR : G.IsBipartition L R) :
    hLR.flowMultiplicity (hx.toBipartiteFlow hLR) = x := by
  funext e
  obtain ⟨⟨a, c, e⟩, rfl⟩ := hLR.bipartiteEdgeEquiv.surjective e
  rw [hLR.bipartiteEdgeEquiv_apply, IsBipartition.flowMultiplicity,
    hLR.bipartiteEdgeEquiv_symm_apply_edge e]
  simp

/-- Multiset capacitated matchings correspond exactly to integer flows of the bipartite network.
Original arrows retain their edge multiplicities; terminal arrows carry vertex usages. -/
noncomputable def IsBipartition.capacitatedMatchingEquivFlow (hLR : G.IsBipartition L R)
    (b : V(G) → ℕ) :
    {x : E(G) → ℕ // G.IsCapacitatedMatching b x} ≃
      Flow (bipartiteCapacity L R b) (inr false) (inr true) where
  toFun x := x.2.toBipartiteFlow hLR
  invFun f := ⟨hLR.flowMultiplicity f, hLR.isCapacitatedMatching_flowMultiplicity f⟩
  left_inv x := Subtype.ext (x.2.flowMultiplicity_toBipartiteFlow hLR)
  right_inv f := hLR.toBipartiteFlow_flowMultiplicity f

@[simp]
theorem IsBipartition.capacitatedMatchingEquivFlow_apply (hLR : G.IsBipartition L R)
    (b : V(G) → ℕ) (x : {x : E(G) → ℕ // G.IsCapacitatedMatching b x}) :
    hLR.capacitatedMatchingEquivFlow b x = x.2.toBipartiteFlow hLR :=
  (rfl)

@[simp]
theorem IsBipartition.capacitatedMatchingEquivFlow_symm_apply (hLR : G.IsBipartition L R)
    (b : V(G) → ℕ) (f : Flow (bipartiteCapacity L R b) (inr false) (inr true)) :
    ((hLR.capacitatedMatchingEquivFlow b).symm f).val = hLR.flowMultiplicity f :=
  (rfl)

/-- Recovering a matching preserves the value of an integral bipartite flow as its size. -/
@[simp]
theorem IsBipartition.sum_flowMultiplicity (hLR : G.IsBipartition L R)
    {b : V(G) → ℕ} (f : Flow (bipartiteCapacity L R b) (inr false) (inr true)) :
    ∑ e, (hLR.flowMultiplicity f e : ℤ) = f.val := by
  rw [← IsCapacitatedMatching.val_toBipartiteFlow
    (hLR.isCapacitatedMatching_flowMultiplicity f) hLR, hLR.toBipartiteFlow_flowMultiplicity]

end Graph
