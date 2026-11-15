/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Matching.Capacitated
public import TauCeti.Combinatorics.Network.AuxiliaryTerminals

/-!
# The flow network of a bipartite multigraph

For a bipartition `L, R` of a finite multigraph, orient every actual edge from `L` to `R`, add a
fresh source with one arrow to each vertex of `L`, and add one arrow from each vertex of `R` to a
fresh sink.  The terminal arrows at `v` have capacity `b v`; every original edge has the large
capacity `b(L) + 1`.

This file develops the flow and cut sides of the standard network proof of capacitated Kőnig's
theorem. Multiset capacitated matchings are equivalent to integral flows in this network: an
original arrow carries its edge multiplicity, and each terminal arrow carries the total usage of
its vertex. A
vertex cover `C` gives the source side

`{source} ∪ (L \ C) ∪ (R ∩ C)`,

whose cut capacity is exactly the weight of `C`.  Conversely, every terminal-separating cut of
capacity below `b(L) + 1` determines the vertex cover `(L \ S) ∪ (R ∩ S)`, because such a cut
cannot cross an original edge.  Edge identities are retained, so the construction applies to
parallel edges; a displayed bipartition already excludes loops.

The construction follows the classical network proof of Kőnig's theorem; see A. Schrijver,
*Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003, Section 21.1.

## Main definitions

* `Graph.BipartiteHom`: one arrow for every actual edge, directed from `L` to `R`.
* `Graph.bipartiteCapacity`: the capacities after adjoining the fresh source and sink.
* `Graph.bipartiteNetwork`: the corresponding zero-lower-bound integer network.
* `Graph.IsBipartition.matchingFlowEquiv`: the equivalence between multiset capacitated matchings
  and flows in the bipartite network.
* `Graph.bipartiteCoverSourceSide`: the source side associated to a vertex cover.
* `Graph.bipartiteCutCover`: the candidate cover extracted from a source side; a low-capacity cut
  guarantees that it covers every edge.

## Main results

* `Graph.IsCapacitatedMatching.val_toBipartiteFlow` and
  `Graph.IsBipartition.sum_flowMatching_eq_val`: both directions of the matching-flow
  correspondence preserve total size.
* `Graph.IsVertexCover.arrowSum_bipartiteCapacity_bipartiteCoverSourceSide`: a cover gives a cut
  of the same weight.
* `Graph.IsBipartition.arrowSum_bipartiteCapacity_eq_sum_bipartiteCutCover`: a low-capacity cut
  has the same weight as its associated cover.
* `Graph.IsBipartition.isVertexCover_bipartiteCutCover`: every cut below the large capacity gives
  a vertex cover.
-/

public section

open Finset Sum TauCeti
open scoped Graph

universe u v

namespace Graph

variable {alpha : Type u} {beta : Type v} {G : Graph alpha beta}
variable {L R : Finset V(G)}

/-- The capacity assigned to every original edge in the bipartite network.  It exceeds the
capacity of the cut obtained by deleting all source arrows. -/
def bipartiteLargeCapacity (L : Finset V(G)) (b : V(G) → ℕ) : ℤ :=
  ((∑ x ∈ L, b x) + 1 : ℕ)

/-- The large capacity is one more than the total capacity on `L`. -/
theorem bipartiteLargeCapacity_def (L : Finset V(G)) (b : V(G) → ℕ) :
    bipartiteLargeCapacity L b = ((∑ x ∈ L, b x) + 1 : ℕ) :=
  (rfl)

/-- The capacities of the bipartite network: `b v` on the terminal arrow at `v`, and
`b(L) + 1` on every original edge directed from `L` to `R`. -/
def bipartiteCapacity (L R : Finset V(G)) (b : V(G) → ℕ) :
    Assignment (AuxTerminalHom (G.BipartiteHom L) L R) ℤ :=
  auxTerminalCapacity (A := L) (B := R)
    (fun {_ _} _ ↦ bipartiteLargeCapacity L b) (fun x ↦ (b x : ℤ)) fun x ↦ (b x : ℤ)

/-- The bipartite capacity as an auxiliary-terminal capacity. -/
theorem bipartiteCapacity_def (L R : Finset V(G)) (b : V(G) → ℕ) :
    bipartiteCapacity L R b =
      auxTerminalCapacity (A := L) (B := R)
        (fun {_ _} _ ↦ bipartiteLargeCapacity L b) (fun x ↦ (b x : ℤ)) fun x ↦ (b x : ℤ) :=
  (rfl)

/-- Every capacity in the bipartite network is nonnegative. -/
theorem bipartiteCapacity_nonneg (L R : Finset V(G)) (b : V(G) → ℕ) :
    0 ≤ bipartiteCapacity L R b :=
  auxTerminalCapacity_nonneg (fun _ _ _ ↦ by
      rw [bipartiteLargeCapacity_def]
      exact Int.natCast_nonneg _)
    (fun _ _ ↦ Int.natCast_nonneg _) fun _ _ ↦ Int.natCast_nonneg _

@[simp]
theorem bipartiteCapacity_original (b : V(G) → ℕ) {x y : V(G)}
    (e : G.BipartiteHom L x y) :
    bipartiteCapacity L R b (AuxTerminalHom.original e) = bipartiteLargeCapacity L b :=
  auxTerminalCapacity_original _ _ _ e

@[simp]
theorem bipartiteCapacity_source (b : V(G) → ℕ) {x : V(G)} (hx : x ∈ L) :
    bipartiteCapacity L R b (AuxTerminalHom.source hx) = b x :=
  auxTerminalCapacity_source _ _ _ hx

@[simp]
theorem bipartiteCapacity_sink (b : V(G) → ℕ) {x : V(G)} (hx : x ∈ R) :
    bipartiteCapacity L R b (AuxTerminalHom.sink hx) = b x :=
  auxTerminalCapacity_sink _ _ _ hx

/-- The integer network used in the flow proof of capacitated Kőnig's theorem. -/
@[expose] noncomputable def bipartiteNetwork
    (G : Graph alpha beta) (L R : Finset V(G)) (b : V(G) → ℕ) :
  Network ℤ (V(G) ⊕ Bool) :=
  Network.ofCapacity (AuxTerminalHom (G.BipartiteHom L) L R) (bipartiteCapacity L R b)
    fun {_ _} e ↦ bipartiteCapacity_nonneg L R b _ _ e

@[simp]
theorem bipartiteNetwork_Hom (b : V(G) → ℕ) :
    (bipartiteNetwork G L R b).Hom = AuxTerminalHom (G.BipartiteHom L) L R :=
  rfl

@[simp]
theorem bipartiteNetwork_upper (b : V(G) → ℕ) {x y : V(G) ⊕ Bool}
    (e : (bipartiteNetwork G L R b).Hom x y) :
    (bipartiteNetwork G L R b).upper e = bipartiteCapacity L R b e :=
  rfl

@[simp]
theorem bipartiteNetwork_lower (b : V(G) → ℕ) {x y : V(G) ⊕ Bool}
    (e : (bipartiteNetwork G L R b).Hom x y) :
    (bipartiteNetwork G L R b).lower e = 0 :=
  rfl

/-! ### Matchings as integral flows -/

/-- The auxiliary-network assignment associated to edge multiplicities `x`. An original arrow
carries the multiplicity of its edge, and a terminal arrow at `v` carries the total usage of
`v`. -/
noncomputable def bipartiteFlowAssignment [Fintype E(G)]
    (L R : Finset V(G)) (x : E(G) → ℕ) :
    Assignment (AuxTerminalHom (G.BipartiteHom L) L R) ℤ :=
  auxTerminalCapacity (fun {_ _} e ↦ (x e.edge : ℤ))
    (fun v ↦ ∑ e ∈ G.incidentEdges {v}, (x e : ℤ))
    fun v ↦ ∑ e ∈ G.incidentEdges {v}, (x e : ℤ)

/-- The matching assignment written as an auxiliary-terminal assignment. -/
theorem bipartiteFlowAssignment_def [Fintype E(G)] (L R : Finset V(G)) (x : E(G) → ℕ) :
    bipartiteFlowAssignment L R x =
      auxTerminalCapacity (fun {_ _} (e : G.BipartiteHom L _ _) ↦ (x e.edge : ℤ))
        (fun v ↦ ∑ e ∈ G.incidentEdges {v}, (x e : ℤ))
        fun v ↦ ∑ e ∈ G.incidentEdges {v}, (x e : ℤ) :=
  (rfl)

@[simp]
theorem bipartiteFlowAssignment_original (x : E(G) → ℕ) {v w : V(G)}
    [Fintype E(G)]
    (e : G.BipartiteHom L v w) :
    bipartiteFlowAssignment L R x (AuxTerminalHom.original e) = x e.edge :=
  by rw [bipartiteFlowAssignment_def, auxTerminalCapacity_original]

@[simp]
theorem bipartiteFlowAssignment_source [Fintype E(G)] (x : E(G) → ℕ)
    {v : V(G)} (hv : v ∈ L) :
    bipartiteFlowAssignment L R x (AuxTerminalHom.source hv) =
      ∑ e ∈ G.incidentEdges {v}, (x e : ℤ) :=
  by rw [bipartiteFlowAssignment_def, auxTerminalCapacity_source]

@[simp]
theorem bipartiteFlowAssignment_sink [Fintype E(G)] (x : E(G) → ℕ)
    {v : V(G)} (hv : v ∈ R) :
    bipartiteFlowAssignment L R x (AuxTerminalHom.sink hv) =
      ∑ e ∈ G.incidentEdges {v}, (x e : ℤ) :=
  by rw [bipartiteFlowAssignment_def, auxTerminalCapacity_sink]

private theorem IsBipartition.excessAt_bipartiteHom_of_mem_left
    [Fintype V(G)] [Fintype E(G)] (hLR : G.IsBipartition L R) (x : E(G) → ℕ)
    (v : V(G)) (hv : v ∈ L) :
    excessAt (fun {a c} (e : G.BipartiteHom L a c) ↦ (x e.edge : ℤ)) v =
      -(∑ e ∈ G.incidentEdges {v}, (x e : ℤ)) := by
  rw [excessAt_def]
  have hout := BipartiteHom.sum_outgoing_eq_sum_incidentEdges v hv
    (fun e ↦ (x e : ℤ))
  have hin : ∑ w, ∑ e : G.BipartiteHom L w v, (x e.edge : ℤ) = 0 := by
    apply Fintype.sum_eq_zero
    intro w
    apply Fintype.sum_eq_zero
    intro e
    exact (disjoint_left.1 hLR.disjoint hv (e.target_mem hLR)).elim
  rw [hin, hout, zero_sub]

private theorem IsBipartition.excessAt_bipartiteHom_of_mem_right
    [Fintype V(G)] [Fintype E(G)] (hLR : G.IsBipartition L R) (x : E(G) → ℕ)
    (v : V(G)) (hv : v ∈ R) :
    excessAt (fun {a c} (e : G.BipartiteHom L a c) ↦ (x e.edge : ℤ)) v =
      ∑ e ∈ G.incidentEdges {v}, (x e : ℤ) := by
  rw [excessAt_def]
  have hin := BipartiteHom.sum_incoming_eq_sum_incidentEdges hLR v hv
    (fun e ↦ (x e : ℤ))
  have hout : ∑ w, ∑ e : G.BipartiteHom L v w, (x e.edge : ℤ) = 0 := by
    apply Fintype.sum_eq_zero
    intro w
    apply Fintype.sum_eq_zero
    intro e
    exact (disjoint_left.1 hLR.disjoint e.source_mem hv).elim
  rw [hin, hout, sub_zero]

/-- A multiset capacitated matching gives an integral flow in the bipartite network. Original
arrows carry the edge multiplicities, while each terminal arrow carries the usage of its vertex. -/
noncomputable def IsCapacitatedMatching.toBipartiteFlow [Fintype V(G)] [DecidableEq V(G)]
    [Fintype E(G)]
    {b : V(G) → ℕ} {x : E(G) → ℕ} (hx : G.IsCapacitatedMatching b x)
    (hLR : G.IsBipartition L R) :
    Flow (bipartiteCapacity L R b) (inr false) (inr true) where
  toFun := bipartiteFlowAssignment L R x
  mem_Icc := ⟨by
    refine AuxTerminalHom.forall_iff.2 ⟨fun _ _ e ↦ ?_, fun v hv ↦ ?_, fun v hv ↦ ?_⟩
    · rw [bipartiteFlowAssignment_original]
      exact Int.natCast_nonneg _
    · rw [bipartiteFlowAssignment_source]
      exact sum_nonneg fun _ _ ↦ Int.natCast_nonneg _
    · rw [bipartiteFlowAssignment_sink]
      exact sum_nonneg fun _ _ ↦ Int.natCast_nonneg _, by
    refine AuxTerminalHom.forall_iff.2 ⟨fun v w e ↦ ?_, fun v hv ↦ ?_, fun v hv ↦ ?_⟩
    · rw [bipartiteFlowAssignment_original, bipartiteCapacity_original,
        bipartiteLargeCapacity_def]
      have he : e.edge ∈ G.incidentEdges {v} :=
        (mem_incidentEdges G).2 ⟨v, by simp, e.isLink.inc_left⟩
      have hxe : x e.edge ≤ b v :=
        (single_le_sum (fun _ _ ↦ Nat.zero_le _) he).trans
          (isCapacitatedMatching_def.1 hx v)
      have hb : b v ≤ ∑ z ∈ L, b z :=
        single_le_sum (fun _ _ ↦ Nat.zero_le _) e.source_mem
      exact_mod_cast hxe.trans (hb.trans (Nat.le_add_right _ _))
    · rw [bipartiteFlowAssignment_source, bipartiteCapacity_source]
      exact_mod_cast isCapacitatedMatching_def.1 hx v
    · rw [bipartiteFlowAssignment_sink, bipartiteCapacity_sink]
      exact_mod_cast isCapacitatedMatching_def.1 hx v⟩
  conserve
    | inl v, _, _ => by
        rw [AuxTerminalHom.excessAt_inl, bipartiteFlowAssignment_def,
          auxTerminalRestrict_auxTerminalCapacity,
          sum_auxTerminalCapacity_source, sum_auxTerminalCapacity_sink]
        rcases hLR.mem_or_mem v with hv | hv
        · rw [hLR.excessAt_bipartiteHom_of_mem_left x v hv]
          simp [hv, disjoint_left.1 hLR.disjoint hv]
        · rw [hLR.excessAt_bipartiteHom_of_mem_right x v hv]
          simp [hv, disjoint_right.1 hLR.disjoint hv]
    | inr false, h, _ => (h rfl).elim
    | inr true, _, h => (h rfl).elim
  excessAt_sink_nonneg := by
    rw [AuxTerminalHom.excessAt_inr_true]
    rw [bipartiteFlowAssignment_def]
    simp only [sum_auxTerminalCapacity_sink, sum_ite_mem,
      univ_inter]
    exact sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ Int.natCast_nonneg _

@[simp]
theorem IsCapacitatedMatching.toBipartiteFlow_toFun [Fintype V(G)] [Fintype E(G)]
    [DecidableEq V(G)] {b : V(G) → ℕ} {x : E(G) → ℕ}
    (hx : G.IsCapacitatedMatching b x) (hLR : G.IsBipartition L R) :
    (hx.toBipartiteFlow hLR).toFun = bipartiteFlowAssignment L R x :=
  (rfl)

@[simp]
theorem IsCapacitatedMatching.toBipartiteFlow_original [Fintype V(G)] [Fintype E(G)]
    [DecidableEq V(G)]
    {b : V(G) → ℕ} {x : E(G) → ℕ} (hx : G.IsCapacitatedMatching b x)
    (hLR : G.IsBipartition L R) {v w : V(G)} (e : G.BipartiteHom L v w) :
    (hx.toBipartiteFlow hLR).toFun (AuxTerminalHom.original e) = x e.edge :=
  by rw [toBipartiteFlow_toFun, bipartiteFlowAssignment_original]

@[simp]
theorem IsCapacitatedMatching.toBipartiteFlow_source [Fintype V(G)] [Fintype E(G)]
    [DecidableEq V(G)] {b : V(G) → ℕ} {x : E(G) → ℕ}
    (hx : G.IsCapacitatedMatching b x) (hLR : G.IsBipartition L R)
    {v : V(G)} (hv : v ∈ L) :
    (hx.toBipartiteFlow hLR).toFun (AuxTerminalHom.source hv) =
      ∑ e ∈ G.incidentEdges {v}, (x e : ℤ) := by
  rw [toBipartiteFlow_toFun, bipartiteFlowAssignment_source]

@[simp]
theorem IsCapacitatedMatching.toBipartiteFlow_sink [Fintype V(G)] [Fintype E(G)]
    [DecidableEq V(G)] {b : V(G) → ℕ} {x : E(G) → ℕ}
    (hx : G.IsCapacitatedMatching b x) (hLR : G.IsBipartition L R)
    {v : V(G)} (hv : v ∈ R) :
    (hx.toBipartiteFlow hLR).toFun (AuxTerminalHom.sink hv) =
      ∑ e ∈ G.incidentEdges {v}, (x e : ℤ) := by
  rw [toBipartiteFlow_toFun, bipartiteFlowAssignment_sink]

/-- The flow obtained from a multiset capacitated matching has value equal to the total edge
multiplicity. -/
@[simp]
theorem IsCapacitatedMatching.val_toBipartiteFlow [Fintype V(G)] [Fintype E(G)]
    [DecidableEq V(G)]
    {b : V(G) → ℕ} {x : E(G) → ℕ} (hx : G.IsCapacitatedMatching b x)
    (hLR : G.IsBipartition L R) :
    (hx.toBipartiteFlow hLR).val = ∑ e, (x e : ℤ) := by
  rw [BoundedFlow.val_def, toBipartiteFlow_toFun, AuxTerminalHom.excessAt_inr_true,
    bipartiteFlowAssignment_def]
  simp only [sum_auxTerminalCapacity_sink,
    sum_ite_mem, univ_inter]
  exact hLR.sum_sum_incidentEdges_right (fun e ↦ (x e : ℤ))

/-- The edge multiplicities obtained by restricting an integral bipartite-network flow to its
original arrows. Since the flow is nonnegative, converting its integer arrow values to naturals
loses no information. -/
noncomputable def IsBipartition.flowMatching [Fintype V(G)] [DecidableEq V(G)]
    [Fintype E(G)] {b : V(G) → ℕ} (hLR : G.IsBipartition L R)
    (f : Flow (bipartiteCapacity L R b) (inr false) (inr true)) : E(G) → ℕ :=
  fun e ↦ Int.toNat <| f.toFun <| AuxTerminalHom.original <|
    ((BipartiteHom.arrowEquiv hLR).symm e).2.2

/-- On an original arrow, the matching extracted from a flow is its arrow value. -/
@[simp]
theorem IsBipartition.flowMatching_edge [Fintype V(G)] [DecidableEq V(G)]
    [Fintype E(G)] {b : V(G) → ℕ} (hLR : G.IsBipartition L R)
    (f : Flow (bipartiteCapacity L R b) (inr false) (inr true))
    {v w : V(G)} (e : G.BipartiteHom L v w) :
    (hLR.flowMatching f e.edge : ℤ) = f.toFun (AuxTerminalHom.original e) := by
  rw [flowMatching, BipartiteHom.arrowEquiv_symm_edge]
  exact Int.toNat_of_nonneg (f.nonneg _)

/-- At a left-side vertex, the usage of the matching extracted from a flow equals the value on
the arrow from the fresh source. -/
theorem IsBipartition.sum_flowMatching_incidentEdges_eq_source [Fintype V(G)]
    [DecidableEq V(G)] [Fintype E(G)] {b : V(G) → ℕ}
    (hLR : G.IsBipartition L R)
    (f : Flow (bipartiteCapacity L R b) (inr false) (inr true))
    (v : V(G)) (hv : v ∈ L) :
    ∑ e ∈ G.incidentEdges {v}, (hLR.flowMatching f e : ℤ) =
      f.toFun (AuxTerminalHom.source hv) := by
  have hin : ∑ w, ∑ e : G.BipartiteHom L w v,
      f.toFun (AuxTerminalHom.original e) = 0 := by
    apply Fintype.sum_eq_zero
    intro w
    apply Fintype.sum_eq_zero
    intro e
    exact (disjoint_left.1 hLR.disjoint hv (e.target_mem hLR)).elim
  have hout : ∑ w, ∑ e : G.BipartiteHom L v w,
      f.toFun (AuxTerminalHom.original e) =
        ∑ e ∈ G.incidentEdges {v}, (hLR.flowMatching f e : ℤ) := by
    rw [← BipartiteHom.sum_outgoing_eq_sum_incidentEdges v hv
      (fun e ↦ (hLR.flowMatching f e : ℤ))]
    apply Fintype.sum_congr
    intro w
    apply Fintype.sum_congr
    intro e
    exact (hLR.flowMatching_edge f e).symm
  have h := f.conserve (inl v) inl_ne_inr inl_ne_inr
  rw [AuxTerminalHom.excessAt_inl, excessAt_def] at h
  simp only [auxTerminalRestrict_apply] at h
  rw [hin, hout,
    AuxTerminalHom.sum_source hv,
    AuxTerminalHom.sum_sink_of_notMem (disjoint_left.1 hLR.disjoint hv), zero_sub,
    sub_zero] at h
  omega

/-- At a right-side vertex, the usage of the matching extracted from a flow equals the value on
the arrow to the fresh sink. -/
theorem IsBipartition.sum_flowMatching_incidentEdges_eq_sink [Fintype V(G)]
    [DecidableEq V(G)] [Fintype E(G)] {b : V(G) → ℕ}
    (hLR : G.IsBipartition L R)
    (f : Flow (bipartiteCapacity L R b) (inr false) (inr true))
    (v : V(G)) (hv : v ∈ R) :
    ∑ e ∈ G.incidentEdges {v}, (hLR.flowMatching f e : ℤ) =
      f.toFun (AuxTerminalHom.sink hv) := by
  have hin : ∑ w, ∑ e : G.BipartiteHom L w v,
      f.toFun (AuxTerminalHom.original e) =
        ∑ e ∈ G.incidentEdges {v}, (hLR.flowMatching f e : ℤ) := by
    rw [← BipartiteHom.sum_incoming_eq_sum_incidentEdges hLR v hv
      (fun e ↦ (hLR.flowMatching f e : ℤ))]
    apply Fintype.sum_congr
    intro w
    apply Fintype.sum_congr
    intro e
    exact (hLR.flowMatching_edge f e).symm
  have hout : ∑ w, ∑ e : G.BipartiteHom L v w,
      f.toFun (AuxTerminalHom.original e) = 0 := by
    apply Fintype.sum_eq_zero
    intro w
    apply Fintype.sum_eq_zero
    intro e
    exact (disjoint_left.1 hLR.disjoint e.source_mem hv).elim
  have h := f.conserve (inl v) inl_ne_inr inl_ne_inr
  rw [AuxTerminalHom.excessAt_inl, excessAt_def] at h
  simp only [auxTerminalRestrict_apply] at h
  rw [hin, hout,
    AuxTerminalHom.sum_source_of_notMem (disjoint_right.1 hLR.disjoint hv),
    AuxTerminalHom.sum_sink hv, sub_zero, add_zero] at h
  exact sub_eq_zero.mp h

/-- Restricting an integral flow in the bipartite network to the original edges gives a multiset
capacitated matching. -/
theorem IsBipartition.isCapacitatedMatching_flowMatching [Fintype V(G)]
    [DecidableEq V(G)] [Fintype E(G)] {b : V(G) → ℕ}
    (hLR : G.IsBipartition L R)
    (f : Flow (bipartiteCapacity L R b) (inr false) (inr true)) :
    G.IsCapacitatedMatching b (hLR.flowMatching f) := by
  rw [isCapacitatedMatching_def]
  intro v
  rcases hLR.mem_or_mem v with hv | hv
  · have hle := f.le_upper (AuxTerminalHom.source hv)
    rw [bipartiteCapacity_source] at hle
    exact_mod_cast (hLR.sum_flowMatching_incidentEdges_eq_source f v hv).trans_le hle
  · have hle := f.le_upper (AuxTerminalHom.sink hv)
    rw [bipartiteCapacity_sink] at hle
    exact_mod_cast (hLR.sum_flowMatching_incidentEdges_eq_sink f v hv).trans_le hle

/-- Restricting an integral bipartite-network flow to a matching preserves its value. -/
theorem IsBipartition.sum_flowMatching_eq_val [Fintype V(G)] [DecidableEq V(G)]
    [Fintype E(G)] {b : V(G) → ℕ} (hLR : G.IsBipartition L R)
    (f : Flow (bipartiteCapacity L R b) (inr false) (inr true)) :
    ∑ e, (hLR.flowMatching f e : ℤ) = f.val := by
  rw [← hLR.sum_sum_incidentEdges_right (fun e ↦ (hLR.flowMatching f e : ℤ))]
  rw [BoundedFlow.val_def, AuxTerminalHom.excessAt_inr_true]
  calc
    ∑ v ∈ R, ∑ e ∈ G.incidentEdges {v}, (hLR.flowMatching f e : ℤ) =
        ∑ v ∈ R, ∑ e : AuxTerminalHom (G.BipartiteHom L) L R (inl v) (inr true),
          f.toFun e := by
      apply sum_congr rfl
      intro v hv
      rw [AuxTerminalHom.sum_sink hv]
      exact hLR.sum_flowMatching_incidentEdges_eq_sink f v hv
    _ = ∑ v, ∑ e : AuxTerminalHom (G.BipartiteHom L) L R (inl v) (inr true),
          f.toFun e := sum_subset (subset_univ R) fun v _ hv ↦ by
      rw [AuxTerminalHom.sum_sink_of_notMem hv]

/-- Extracting a matching from the flow associated to a matching recovers every edge
multiplicity. -/
@[simp]
theorem IsCapacitatedMatching.flowMatching_toBipartiteFlow [Fintype V(G)]
    [DecidableEq V(G)] [Fintype E(G)] {b : V(G) → ℕ} {x : E(G) → ℕ}
    (hx : G.IsCapacitatedMatching b x) (hLR : G.IsBipartition L R) :
    hLR.flowMatching (hx.toBipartiteFlow hLR) = x := by
  funext e
  let a := (BipartiteHom.arrowEquiv hLR).symm e
  have ha : a.2.2.edge = e := by
    have h := (BipartiteHom.arrowEquiv hLR).apply_symm_apply e
    rw [BipartiteHom.arrowEquiv_apply] at h
    exact h
  have h := hLR.flowMatching_edge (hx.toBipartiteFlow hLR) a.2.2
  rw [hx.toBipartiteFlow_original hLR, ha] at h
  exact_mod_cast h

/-- Rebuilding a flow from its matching of original-edge values recovers the entire flow,
including both families of terminal arrows. -/
@[simp]
theorem IsBipartition.toBipartiteFlow_flowMatching [Fintype V(G)] [DecidableEq V(G)]
    [Fintype E(G)] {b : V(G) → ℕ} (hLR : G.IsBipartition L R)
    (f : Flow (bipartiteCapacity L R b) (inr false) (inr true)) :
    (hLR.isCapacitatedMatching_flowMatching f).toBipartiteFlow hLR = f := by
  apply Flow.ext
  apply funext₃
  refine AuxTerminalHom.forall_iff.2 ⟨fun _ _ e ↦ ?_, fun v hv ↦ ?_, fun v hv ↦ ?_⟩
  · rw [IsCapacitatedMatching.toBipartiteFlow_original]
    exact hLR.flowMatching_edge f e
  · rw [IsCapacitatedMatching.toBipartiteFlow_source]
    exact hLR.sum_flowMatching_incidentEdges_eq_source f v hv
  · rw [IsCapacitatedMatching.toBipartiteFlow_sink]
    exact hLR.sum_flowMatching_incidentEdges_eq_sink f v hv

/-- Multiset capacitated matchings are equivalent to integral flows in the associated bipartite
network. The equivalence preserves every original edge value and the total matching size. -/
noncomputable def IsBipartition.matchingFlowEquiv [Fintype V(G)] [DecidableEq V(G)]
    [Fintype E(G)] (hLR : G.IsBipartition L R) (b : V(G) → ℕ) :
    {x : E(G) → ℕ // G.IsCapacitatedMatching b x} ≃
      Flow (bipartiteCapacity L R b) (inr false) (inr true) where
  toFun x := x.2.toBipartiteFlow hLR
  invFun f := ⟨hLR.flowMatching f, hLR.isCapacitatedMatching_flowMatching f⟩
  left_inv x := Subtype.ext (x.2.flowMatching_toBipartiteFlow hLR)
  right_inv f := hLR.toBipartiteFlow_flowMatching f

@[simp]
theorem IsBipartition.matchingFlowEquiv_apply [Fintype V(G)] [DecidableEq V(G)]
    [Fintype E(G)] (hLR : G.IsBipartition L R) (b : V(G) → ℕ)
    (x : {x : E(G) → ℕ // G.IsCapacitatedMatching b x}) :
    hLR.matchingFlowEquiv b x = x.2.toBipartiteFlow hLR :=
  (rfl)

@[simp]
theorem IsBipartition.matchingFlowEquiv_symm_apply [Fintype V(G)] [DecidableEq V(G)]
    [Fintype E(G)] (hLR : G.IsBipartition L R) (b : V(G) → ℕ)
    (f : Flow (bipartiteCapacity L R b) (inr false) (inr true)) :
    (hLR.matchingFlowEquiv b).symm f =
      ⟨hLR.flowMatching f, hLR.isCapacitatedMatching_flowMatching f⟩ :=
  (rfl)

/-- The source side associated to a vertex set `C`: it contains the fresh source, the vertices of
`L` outside `C`, and the vertices of `R` inside `C`. -/
noncomputable def bipartiteCoverSourceSide
    (L R C : Finset V(G)) : Finset (V(G) ⊕ Bool) := by
  classical
  exact ((L \ C) ∪ (R ∩ C)).disjSum {false}

@[simp]
theorem inl_mem_bipartiteCoverSourceSide (L R C : Finset V(G)) (x : V(G)) :
    inl x ∈ bipartiteCoverSourceSide L R C ↔
      (x ∈ L ∧ x ∉ C) ∨ (x ∈ R ∧ x ∈ C) := by
  simp [bipartiteCoverSourceSide]

@[simp]
theorem inr_mem_bipartiteCoverSourceSide (L R C : Finset V(G)) (t : Bool) :
    inr t ∈ bipartiteCoverSourceSide L R C ↔ t = false := by
  simp [bipartiteCoverSourceSide]

@[simp]
theorem bipartiteCoverSourceSide_toLeft [DecidableEq V(G)] (L R C : Finset V(G)) :
    (bipartiteCoverSourceSide L R C).toLeft = (L \ C) ∪ (R ∩ C) :=
  by
    ext x
    simp

/-- The vertex set associated to a source side `S`: vertices of `L` outside `S`, together with
vertices of `R` inside `S`. It is a vertex cover when the cut capacity is below `b(L) + 1`; see
`Graph.IsBipartition.isVertexCover_bipartiteCutCover`. -/
noncomputable def bipartiteCutCover
    (L R : Finset V(G)) (S : Finset (V(G) ⊕ Bool)) : Finset V(G) := by
  classical
  exact (L \ S.toLeft) ∪ (R ∩ S.toLeft)

@[simp]
theorem mem_bipartiteCutCover (L R : Finset V(G)) (S : Finset (V(G) ⊕ Bool)) (x : V(G)) :
    x ∈ bipartiteCutCover L R S ↔
      (x ∈ L ∧ inl x ∉ S) ∨ (x ∈ R ∧ inl x ∈ S) := by
  simp [bipartiteCutCover]

private theorem sum_bipartiteCoverSourceSide [DecidableEq V(G)]
    (hLR : G.IsBipartition L R) (b : V(G) → ℕ)
    (C : Finset V(G)) :
    ∑ x ∈ L \ ((L \ C) ∪ (R ∩ C)), (b x : ℤ) +
        ∑ x ∈ R ∩ ((L \ C) ∪ (R ∩ C)), (b x : ℤ) =
      ∑ x ∈ C, (b x : ℤ) := by
  classical
  have hL : L \ ((L \ C) ∪ (R ∩ C)) = L ∩ C := by
    ext x
    have hdisjoint : x ∈ L → x ∈ R → False :=
      fun hxL hxR ↦ disjoint_left.1 hLR.disjoint hxL hxR
    grind
  have hR : R ∩ ((L \ C) ∪ (R ∩ C)) = R ∩ C := by
    ext x
    have hdisjoint : x ∈ L → x ∈ R → False :=
      fun hxL hxR ↦ disjoint_left.1 hLR.disjoint hxL hxR
    grind
  rw [hL, hR, ← sum_union]
  · congr 1
    ext x
    have hmem := hLR.mem_or_mem x
    grind
  · exact hLR.disjoint.mono inter_subset_left inter_subset_left

private theorem sum_bipartiteCutCover [DecidableEq V(G)]
    (hLR : G.IsBipartition L R) (b : V(G) → ℕ) (S : Finset (V(G) ⊕ Bool)) :
    ∑ x ∈ L \ S.toLeft, (b x : ℤ) + ∑ x ∈ R ∩ S.toLeft, (b x : ℤ) =
      ∑ x ∈ bipartiteCutCover L R S, (b x : ℤ) := by
  classical
  have hcover : bipartiteCutCover L R S = (L \ S.toLeft) ∪ (R ∩ S.toLeft) := by
    ext x
    simp
  rw [hcover, sum_union]
  exact hLR.disjoint.mono sdiff_subset inter_subset_left

private theorem bipartiteHom_closed_of_arrowSum_lt [Fintype V(G)] [DecidableEq V(G)]
    [Fintype E(G)] (b : V(G) → ℕ) {S : Finset (V(G) ⊕ Bool)}
    (hsmall : arrowSum (bipartiteCapacity L R b) S Sᶜ < bipartiteLargeCapacity L b) :
    ∀ {x y : V(G)}, G.BipartiteHom L x y → x ∈ S.toLeft → y ∈ S.toLeft := by
  intro x y e hx
  by_contra hy
  have hx' : inl x ∈ S := by simpa using hx
  have hy' : inl y ∈ Sᶜ := by
    simp only [mem_compl]
    exact fun hyS ↦ hy (Finset.mem_toLeft.2 hyS)
  have hle := apply_le_arrowSum (bipartiteCapacity_nonneg L R b) hx' hy'
    (AuxTerminalHom.original e)
  rw [bipartiteCapacity_original] at hle
  exact (not_lt_of_ge hle) hsmall

/-- A vertex cover gives a terminal-separating cut whose capacity is exactly the weight of the
cover. -/
theorem IsVertexCover.arrowSum_bipartiteCapacity_bipartiteCoverSourceSide
    [Fintype V(G)] [DecidableEq V(G)]
    [Fintype E(G)] {C : Finset V(G)}
    (hC : G.IsVertexCover (C : Set V(G))) (hLR : G.IsBipartition L R) (b : V(G) → ℕ) :
    arrowSum (bipartiteCapacity L R b) (bipartiteCoverSourceSide L R C)
        (bipartiteCoverSourceSide L R C)ᶜ = ∑ x ∈ C, (b x : ℤ) := by
  classical
  rw [bipartiteCapacity_def]
  rw [arrowSum_auxTerminalCapacity (S := bipartiteCoverSourceSide L R C)
    (fun {_ _} _ ↦ bipartiteLargeCapacity L b) (fun x ↦ (b x : ℤ)) (fun x ↦ (b x : ℤ))
    (by simp) (by simp)]
  rw [arrowSum_compl_eq_zero_of_forall_mem]
  · simpa only [bipartiteCoverSourceSide_toLeft, add_zero] using
      sum_bipartiteCoverSourceSide hLR b C
  · intro x y e hx
    have hxC : x ∉ C := by
      simpa [e.source_mem, disjoint_left.1 hLR.disjoint] using hx
    have hyR := e.target_mem hLR
    have hyC : y ∈ C := by
      rw [isVertexCover_def] at hC
      rcases hC e.isLink with h | h
      · exact (hxC h).elim
      · exact h
    simp [hyR, hyC]

/-- A terminal-separating cut below the large capacity has the same capacity as the weight of its
associated vertex cover. -/
theorem IsBipartition.arrowSum_bipartiteCapacity_eq_sum_bipartiteCutCover
    [Fintype V(G)] [DecidableEq V(G)] [Fintype E(G)]
    (hLR : G.IsBipartition L R) (b : V(G) → ℕ) {S : Finset (V(G) ⊕ Bool)}
    (hsource : inr false ∈ S) (hsink : inr true ∉ S)
    (hsmall : arrowSum (bipartiteCapacity L R b) S Sᶜ < bipartiteLargeCapacity L b) :
    arrowSum (bipartiteCapacity L R b) S Sᶜ =
      ∑ x ∈ bipartiteCutCover L R S, (b x : ℤ) := by
  have hclosed : ∀ {x y : V(G)}, G.BipartiteHom L x y →
      x ∈ S.toLeft → y ∈ S.toLeft :=
    bipartiteHom_closed_of_arrowSum_lt b hsmall
  rw [bipartiteCapacity_def]
  rw [arrowSum_auxTerminalCapacity (S := S) (fun {_ _} _ ↦ bipartiteLargeCapacity L b)
    (fun x ↦ (b x : ℤ)) (fun x ↦ (b x : ℤ)) hsource hsink]
  rw [arrowSum_compl_eq_zero_of_forall_mem]
  · simpa only [add_zero] using sum_bipartiteCutCover hLR b S
  · intro x y e hx
    exact hclosed e hx

/-- A cut below the large capacity cannot cross an original edge, so its associated vertex set
is a vertex cover. -/
theorem IsBipartition.isVertexCover_bipartiteCutCover [Fintype V(G)] [DecidableEq V(G)]
    [Fintype E(G)]
    (hLR : G.IsBipartition L R) (b : V(G) → ℕ) {S : Finset (V(G) ⊕ Bool)}
    (hsmall : arrowSum (bipartiteCapacity L R b) S Sᶜ < bipartiteLargeCapacity L b) :
    G.IsVertexCover (bipartiteCutCover L R S : Set V(G)) := by
  classical
  have hclosed : ∀ {x y : V(G)}, G.BipartiteHom L x y →
      x ∈ S.toLeft → y ∈ S.toLeft :=
    bipartiteHom_closed_of_arrowSum_lt b hsmall
  rw [isVertexCover_def]
  intro e x y he
  rcases hLR.isLink he with hxy | hxy
  · by_cases hxS : x ∈ S.toLeft
    · have hyS : y ∈ S.toLeft :=
        hclosed (⟨⟨e, he.edge_mem⟩, he, hxy.1⟩ : G.BipartiteHom L x y) hxS
      have hyS' : inl y ∈ S := by simpa using hyS
      right
      simp [hxy.2, hyS']
    · left
      have hxS' : inl x ∉ S := by simpa using hxS
      simp [hxy.1, hxS']
  · by_cases hyS : y ∈ S.toLeft
    · have hxS : x ∈ S.toLeft :=
        hclosed (⟨⟨e, he.edge_mem⟩, he.symm, hxy.2⟩ : G.BipartiteHom L y x) hyS
      have hxS' : inl x ∈ S := by simpa using hxS
      left
      simp [hxy.1, hxS']
    · right
      have hyS' : inl y ∉ S := by simpa using hyS
      simp [hxy.2, hyS']

end Graph
