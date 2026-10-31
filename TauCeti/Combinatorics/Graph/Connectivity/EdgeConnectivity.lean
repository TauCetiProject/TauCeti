/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
public import TauCeti.Combinatorics.Graph.Connectivity.Bridge.Basic
public import TauCeti.Combinatorics.Graph.Connectivity.Component
public import TauCeti.Combinatorics.Graph.Delete
public import TauCeti.Combinatorics.Graph.Incidence
public import TauCeti.Data.ENat.Lattice

/-!
# Edge reachability and edge connectivity of multigraphs

Two points `x, y` of a multigraph `G : Graph α β` are `k`-edge-reachable, `G.IsEdgeReachable k x y`,
when they remain reachable after deleting any set of fewer than `k` edges, and `G` is
`k`-edge-connected, `G.IsEdgeConnected k`, when any two of its actual vertices are
`k`-edge-reachable. Deleted edges are counted as edge identities, so parallel edges count
separately: two vertices joined by `n` parallel edges are `n`-edge-reachable. The thresholds are
natural numbers, and `G.edgeReachability x y` and `G.edgeConnectivity` are the suprema in `ℕ∞` of
the thresholds at which the predicates hold. These supremum definitions and the bounds by incident
edge counts follow [mathlib4#42494](https://github.com/leanprover-community/mathlib4/pull/42494).

The predicates follow Mathlib's `SimpleGraph.IsEdgeReachable` and `SimpleGraph.IsEdgeConnected`,
and agree with them on `Graph.ofSimpleGraph`. Unlike a simple graph, a multigraph has actual
vertices `V(G)` inside its ambient vertex type, and reachability requires actual endpoints. So
for `k ≠ 0` a point is `k`-edge-reachable from itself exactly when it is an actual vertex, and
`k`-edge-reachability is an equivalence relation on `V(G)`. Global edge connectivity only
quantifies over actual vertices, so it is monotone along inclusions of multigraphs with the same
actual vertex set.

## Main results

* `Graph.isEdgeReachable_one`, `Graph.isEdgeConnected_one`: the threshold `1` is reachability.
* `Graph.isEdgeConnected_iff_forall_connected`: a multigraph with an actual vertex is
  `k`-edge-connected exactly when it stays connected after deleting fewer than `k` edges.
* `Graph.IsLink.isBridge_iff_not_isEdgeReachable_two`: an edge is a bridge exactly when its ends
  are not `2`-edge-reachable.
* `Graph.isEdgeReachable_ofSimpleGraph_iff`, `Graph.isEdgeConnected_ofSimpleGraph_iff`: agreement
  with the simple-graph predicates.
* `Graph.isEdgeReachable_iff_le_edgeReachability`, `Graph.isEdgeConnected_iff_le_edgeConnectivity`:
  the numerical invariants record exactly the thresholds at which the predicates hold.
* `Graph.edgeConnectivity_eq_iInf_edgeReachability`: edge connectivity is the least local edge
  reachability between actual vertices.
* `Graph.edgeReachability_le_nonloopIncidenceCount`: local edge reachability between distinct
  vertices is bounded by the number of nonloop edges at the first vertex.
* `Graph.edgeConnectivity_eq_top_iff`: when the actual edge set is finite, edge connectivity is
  `⊤` exactly when there is at most one actual vertex.
* `Graph.edgeReachability_banana`, `Graph.edgeConnectivity_banana`: two distinct vertices joined by
  `n` parallel edges have local edge reachability and edge connectivity `n`.
-/

public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G H : Graph α β} {k l : ℕ} {e : β} {x y z : α}

/-! ### Edge reachability -/

/-- Two points of a multigraph are `k`-edge-reachable if they remain reachable after deleting any
set of fewer than `k` edges. -/
def IsEdgeReachable (G : Graph α β) (k : ℕ) (x y : α) : Prop :=
  ∀ ⦃F : Set β⦄, F.encard < k → (G.deleteEdges F).Reachable x y

theorem isEdgeReachable_def : G.IsEdgeReachable k x y ↔
    ∀ ⦃F : Set β⦄, F.encard < k → (G.deleteEdges F).Reachable x y := Iff.rfl

/-- Only actual edges need to be deleted in the definition of edge reachability. -/
theorem isEdgeReachable_iff_forall_subset_edgeSet : G.IsEdgeReachable k x y ↔
    ∀ ⦃F : Set β⦄, F ⊆ E(G) → F.encard < k → (G.deleteEdges F).Reachable x y := by
  refine ⟨fun h F _ hF ↦ h hF, fun h F hF ↦ ?_⟩
  obtain ⟨hx, p, hp⟩ := reachable_deleteEdges_iff_exists_walk.mp
    (h inter_subset_left ((encard_le_encard (inter_subset_right (s := E(G)))).trans_lt hF))
  exact reachable_deleteEdges_iff_exists_walk.mpr
    ⟨hx, p, fun f hf hfF ↦ hp f hf ⟨p.edges_subset_edgeSet hf, hfF⟩⟩

@[simp]
protected theorem IsEdgeReachable.zero : G.IsEdgeReachable 0 x y := by
  simp [isEdgeReachable_def]

/-- Reachability is `1`-edge-reachability. -/
@[simp]
theorem isEdgeReachable_one : G.IsEdgeReachable 1 x y ↔ G.Reachable x y := by
  simp [isEdgeReachable_def]

/-- Edge reachability at a smaller threshold follows from edge reachability at a larger one. -/
@[gcongr]
theorem IsEdgeReachable.anti (hkl : k ≤ l) (h : G.IsEdgeReachable l x y) :
    G.IsEdgeReachable k x y :=
  fun _ hF ↦ h (hF.trans_le (Nat.cast_le.mpr hkl))

/-- Edge reachability is monotone under inclusion of multigraphs. -/
@[gcongr]
theorem IsEdgeReachable.mono (hGH : G ≤ H) (h : G.IsEdgeReachable k x y) :
    H.IsEdgeReachable k x y :=
  fun F hF ↦ (h hF).mono (deleteEdges_mono_left hGH F)

theorem IsEdgeReachable.reachable (hk : k ≠ 0) (h : G.IsEdgeReachable k x y) : G.Reachable x y :=
  isEdgeReachable_one.mp (h.anti (Nat.one_le_iff_ne_zero.mpr hk))

theorem IsEdgeReachable.left_mem (hk : k ≠ 0) (h : G.IsEdgeReachable k x y) : x ∈ V(G) :=
  (h.reachable hk).left_mem

theorem IsEdgeReachable.right_mem (hk : k ≠ 0) (h : G.IsEdgeReachable k x y) : y ∈ V(G) :=
  (h.reachable hk).right_mem

/-- An actual vertex is `k`-edge-reachable from itself, since deleting edges keeps every
vertex. -/
protected theorem IsEdgeReachable.refl (hx : x ∈ V(G)) : G.IsEdgeReachable k x x :=
  fun _ _ ↦ Reachable.refl (by simpa using hx)

/-- For a positive threshold, a point is `k`-edge-reachable from itself exactly when it is an
actual vertex. -/
theorem isEdgeReachable_self_iff (hk : k ≠ 0) : G.IsEdgeReachable k x x ↔ x ∈ V(G) :=
  ⟨IsEdgeReachable.left_mem hk, IsEdgeReachable.refl⟩

@[symm]
theorem IsEdgeReachable.symm (h : G.IsEdgeReachable k x y) : G.IsEdgeReachable k y x :=
  fun _ hF ↦ (h hF).symm

theorem isEdgeReachable_comm : G.IsEdgeReachable k x y ↔ G.IsEdgeReachable k y x :=
  ⟨.symm, .symm⟩

@[trans]
theorem IsEdgeReachable.trans (hxy : G.IsEdgeReachable k x y) (hyz : G.IsEdgeReachable k y z) :
    G.IsEdgeReachable k x z :=
  fun _ hF ↦ (hxy hF).trans (hyz hF)

/-- For every threshold, edge reachability is an equivalence relation on the actual vertices. -/
theorem isEdgeReachable_equivalence (G : Graph α β) (k : ℕ) :
    Equivalence fun x y : V(G) ↦ G.IsEdgeReachable k x y :=
  ⟨fun x ↦ .refl x.property, .symm, .trans⟩

/-! ### Edge connectivity -/

/-- A multigraph is `k`-edge-connected if any two of its actual vertices are `k`-edge-reachable.
-/
def IsEdgeConnected (G : Graph α β) (k : ℕ) : Prop :=
  ∀ ⦃x⦄, x ∈ V(G) → ∀ ⦃y⦄, y ∈ V(G) → G.IsEdgeReachable k x y

theorem isEdgeConnected_def : G.IsEdgeConnected k ↔
    ∀ ⦃x⦄, x ∈ V(G) → ∀ ⦃y⦄, y ∈ V(G) → G.IsEdgeReachable k x y := Iff.rfl

theorem IsEdgeConnected.isEdgeReachable (h : G.IsEdgeConnected k) (hx : x ∈ V(G))
    (hy : y ∈ V(G)) : G.IsEdgeReachable k x y :=
  h hx hy

@[simp]
protected theorem IsEdgeConnected.zero : G.IsEdgeConnected 0 :=
  fun _ _ _ _ ↦ .zero

/-- A multigraph is `1`-edge-connected exactly when any two actual vertices are reachable from
each other. -/
@[simp]
theorem isEdgeConnected_one :
    G.IsEdgeConnected 1 ↔ ∀ ⦃x⦄, x ∈ V(G) → ∀ ⦃y⦄, y ∈ V(G) → G.Reachable x y := by
  simp [isEdgeConnected_def]

theorem IsEdgeConnected.anti (hkl : k ≤ l) (h : G.IsEdgeConnected l) : G.IsEdgeConnected k :=
  fun _ hx _ hy ↦ (h hx hy).anti hkl

/-- Edge connectivity is monotone under inclusions of multigraphs with the same actual vertices.
Without equal vertex sets this fails: the larger graph may have additional, isolated vertices. -/
theorem IsEdgeConnected.mono (hGH : G ≤ H) (hV : V(G) = V(H)) (h : G.IsEdgeConnected k) :
    H.IsEdgeConnected k :=
  fun _ hx _ hy ↦ (h (hV ▸ hx) (hV ▸ hy)).mono hGH

/-- A multigraph with at most one actual vertex is `k`-edge-connected for every `k`. -/
theorem IsEdgeConnected.of_subsingleton (hG : V(G).Subsingleton) : G.IsEdgeConnected k :=
  fun _ hx _ hy ↦ hG hx hy ▸ .refl hx

/-- A `k`-edge-connected multigraph with an actual vertex is connected, for `k ≠ 0`. -/
theorem IsEdgeConnected.connected (hk : k ≠ 0) (hV : V(G).Nonempty) (h : G.IsEdgeConnected k) :
    G.Connected :=
  connected_iff_forall_reachable.mpr ⟨hV, fun {_ _} hx hy ↦ (h hx hy).reachable hk⟩

/-- A multigraph with an actual vertex is `k`-edge-connected exactly when it remains connected
after deleting any set of fewer than `k` edges. -/
theorem isEdgeConnected_iff_forall_connected (hV : V(G).Nonempty) :
    G.IsEdgeConnected k ↔ ∀ ⦃F : Set β⦄, F.encard < k → (G.deleteEdges F).Connected := by
  simp only [connected_iff_forall_reachable, vertexSet_deleteEdges, hV, true_and]
  exact ⟨fun h F hF x y hx hy ↦ h hx hy hF, fun h x hx y hy F hF ↦ h hF hx hy⟩

/-! ### Bridges -/

/-- The ends of a link of a bridge are not `2`-edge-reachable. -/
theorem IsBridge.not_isEdgeReachable_two (he : G.IsBridge e) (h : G.IsLink e x y) :
    ¬ G.IsEdgeReachable 2 x y :=
  fun hxy ↦ he.not_reachable_deleteEdges h (hxy (by simp))

/-- An edge joining `x` and `y` is a bridge exactly when `x` and `y` are not `2`-edge-reachable. -/
theorem IsLink.isBridge_iff_not_isEdgeReachable_two (h : G.IsLink e x y) :
    G.IsBridge e ↔ ¬ G.IsEdgeReachable 2 x y := by
  refine ⟨fun he ↦ he.not_isEdgeReachable_two h, fun hxy ↦ ?_⟩
  rw [h.isBridge_iff_not_reachable_deleteEdges]
  intro hre
  refine hxy fun F hF ↦ ?_
  obtain rfl | ⟨f, rfl⟩ := encard_le_one_iff_eq.mp (ENat.lt_two_iff.mp hF)
  · simpa using h.reachable
  · obtain rfl | hfe := eq_or_ne f e
    · exact hre
    · exact IsLink.reachable (e := e) (by simpa [deleteEdges_isLink] using ⟨h, hfe.symm⟩)

/-! ### Graphs from simple graphs -/

/-- Edge reachability in `Graph.ofSimpleGraph H` is simple-graph edge reachability in `H`. -/
@[simp]
theorem isEdgeReachable_ofSimpleGraph_iff (H : SimpleGraph α) (k : ℕ) (x y : α) :
    (Graph.ofSimpleGraph H).IsEdgeReachable k x y ↔ H.IsEdgeReachable k x y := by
  simp [isEdgeReachable_def, SimpleGraph.IsEdgeReachable, ofSimpleGraph_deleteEdges]

/-- Edge connectivity of `Graph.ofSimpleGraph H` is simple-graph edge connectivity of `H`. -/
@[simp]
theorem isEdgeConnected_ofSimpleGraph_iff (H : SimpleGraph α) (k : ℕ) :
    (Graph.ofSimpleGraph H).IsEdgeConnected k ↔ H.IsEdgeConnected k := by
  simp [isEdgeConnected_def, SimpleGraph.IsEdgeConnected]

/-! ### Numerical invariants -/

/-- The local edge reachability of two points: the supremum in `ℕ∞` of the natural thresholds `k`
at which they are `k`-edge-reachable. -/
noncomputable def edgeReachability (G : Graph α β) (x y : α) : ℕ∞ :=
  ⨆ (k : ℕ) (_ : G.IsEdgeReachable k x y), (k : ℕ∞)

/-- The edge connectivity of a multigraph: the supremum in `ℕ∞` of the natural thresholds `k` at
which it is `k`-edge-connected. It is `⊤` when there is at most one actual vertex. -/
noncomputable def edgeConnectivity (G : Graph α β) : ℕ∞ :=
  ⨆ (k : ℕ) (_ : G.IsEdgeConnected k), (k : ℕ∞)

/-- Local edge reachability records exactly the thresholds at which edge reachability holds. -/
theorem isEdgeReachable_iff_le_edgeReachability (k : ℕ) :
    G.IsEdgeReachable k x y ↔ k ≤ G.edgeReachability x y :=
  (Antitone.natCast_le_iSup_iff (fun _ _ hkl (h : G.IsEdgeReachable _ x y) ↦ h.anti hkl)
    IsEdgeReachable.zero).symm

/-- Edge connectivity records exactly the thresholds at which edge connectivity holds. -/
theorem isEdgeConnected_iff_le_edgeConnectivity (k : ℕ) :
    G.IsEdgeConnected k ↔ k ≤ G.edgeConnectivity :=
  (Antitone.natCast_le_iSup_iff (fun _ _ hkl (h : G.IsEdgeConnected _) ↦ h.anti hkl)
    IsEdgeConnected.zero).symm

theorem edgeReachability_comm (x y : α) : G.edgeReachability x y = G.edgeReachability y x :=
  ENat.eq_of_forall_natCast_le_iff fun k ↦ by
    rw [← isEdgeReachable_iff_le_edgeReachability, ← isEdgeReachable_iff_le_edgeReachability,
      isEdgeReachable_comm]

/-- An actual vertex has local edge reachability `⊤` with itself. -/
theorem edgeReachability_self (hx : x ∈ V(G)) : G.edgeReachability x x = ⊤ :=
  ENat.eq_top_iff_forall_ge.mpr fun _ ↦
    (isEdgeReachable_iff_le_edgeReachability _).mp (.refl hx)

/-- Edge connectivity is the infimum of the local edge reachabilities between actual vertices. -/
theorem edgeConnectivity_eq_iInf_edgeReachability (G : Graph α β) :
    G.edgeConnectivity = ⨅ x ∈ V(G), ⨅ y ∈ V(G), G.edgeReachability x y :=
  ENat.eq_of_forall_natCast_le_iff fun k ↦ by
    simp only [le_iInf_iff, ← isEdgeReachable_iff_le_edgeReachability,
      ← isEdgeConnected_iff_le_edgeConnectivity, isEdgeConnected_def]

theorem edgeConnectivity_le_edgeReachability (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    G.edgeConnectivity ≤ G.edgeReachability x y := by
  rw [edgeConnectivity_eq_iInf_edgeReachability]
  exact iInf₂_le_of_le x hx (iInf₂_le y hy)

/-- A multigraph with at most one actual vertex has edge connectivity `⊤`. -/
theorem edgeConnectivity_eq_top_of_subsingleton (hG : V(G).Subsingleton) :
    G.edgeConnectivity = ⊤ :=
  ENat.eq_top_iff_forall_ge.mpr fun _ ↦
    (isEdgeConnected_iff_le_edgeConnectivity _).mp (.of_subsingleton hG)

/-! ### Bounds by incident edges -/

/-- If distinct points are `k`-edge-reachable, then the first one has at least `k` incident
nonloop edges, provided it has finitely many incident edges. -/
theorem IsEdgeReachable.le_nonloopIncidenceCount (h : G.IsEdgeReachable k x y) (hxy : x ≠ y)
    (hfin : (G.incidenceSet x).Finite) : k ≤ G.nonloopIncidenceCount x := by
  by_contra! hlt
  set F := G.incidenceSet x \ G.loopSet x
  have hF : F.encard < k := by
    rw [← (hfin.sdiff (t := G.loopSet x)).cast_ncard_eq, ← nonloopIncidenceCount_def]
    exact Nat.cast_lt.mpr hlt
  obtain ⟨p, hp⟩ := (h hF).exists_isPath
  cases p with
  | nil => exact hxy rfl
  | cons f hf q =>
    rw [deleteEdges_isLink] at hf
    obtain ⟨hf, hfF⟩ := hf
    refine hfF ⟨hf.inc_left, fun hloop ↦ ?_⟩
    rw [Walk.isPath_cons] at hp
    exact hp.2 ((hf.right_unique hloop) ▸ q.start_mem_support)

/-- The local edge reachability between distinct points is at most the number of nonloop edges
incident with the first, provided it has finitely many incident edges. -/
theorem edgeReachability_le_nonloopIncidenceCount (hxy : x ≠ y)
    (hfin : (G.incidenceSet x).Finite) :
    G.edgeReachability x y ≤ G.nonloopIncidenceCount x :=
  ENat.forall_natCast_le_iff_le.mp fun _ hk ↦ Nat.cast_le.mpr
    (((isEdgeReachable_iff_le_edgeReachability _).mpr hk).le_nonloopIncidenceCount hxy hfin)

/-- The edge connectivity of a multigraph with two distinct actual vertices is at most the number
of nonloop edges at the first, provided it has finitely many incident edges. -/
theorem edgeConnectivity_le_nonloopIncidenceCount (hx : x ∈ V(G)) (hy : y ∈ V(G)) (hxy : x ≠ y)
    (hfin : (G.incidenceSet x).Finite) :
    G.edgeConnectivity ≤ G.nonloopIncidenceCount x :=
  (edgeConnectivity_le_edgeReachability hx hy).trans
    (edgeReachability_le_nonloopIncidenceCount hxy hfin)

/-- With finitely many actual edges, edge connectivity is `⊤` exactly when there is at most one
actual vertex. -/
theorem edgeConnectivity_eq_top_iff [Finite E(G)] :
    G.edgeConnectivity = ⊤ ↔ V(G).Subsingleton := by
  refine ⟨fun h x hx y hy ↦ ?_, edgeConnectivity_eq_top_of_subsingleton⟩
  by_contra hxy
  have hle := edgeConnectivity_le_nonloopIncidenceCount hx hy hxy (G.finite_incidenceSet x)
  rw [h, top_le_iff] at hle
  exact ENat.natCast_ne_top _ hle

/-! ### Two vertices joined by parallel edges -/

/-- Two distinct vertices joined by the edges of `F` are reachable from each other exactly when
`F` is nonempty. -/
theorem reachable_banana_iff {u w : α} {F : Set β} (huw : u ≠ w) :
    (banana u w F).Reachable u w ↔ F.Nonempty := by
  exact ⟨fun h ↦ edgeCut_banana_singleton huw F ▸
    h.edgeCut_nonempty rfl (by simpa using huw.symm),
    fun ⟨f, hf⟩ ↦ IsLink.reachable (e := f) (by simp [hf])⟩

/-- Two distinct vertices joined by the parallel edges of `F` are `k`-edge-reachable exactly when
there are at least `k` of these edges. -/
theorem isEdgeReachable_banana_iff {u w : α} {F : Set β} (huw : u ≠ w) :
    (banana u w F).IsEdgeReachable k u w ↔ k ≤ F.encard := by
  simp only [isEdgeReachable_def, banana_deleteEdges, reachable_banana_iff huw]
  refine ⟨fun h ↦ ?_, fun h D hD ↦ ?_⟩
  · by_contra! hF
    simpa using h hF
  · by_contra hFD
    rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at hFD
    exact (hD.trans_le h).not_ge (encard_le_encard hFD)

/-- The local edge reachability of two distinct vertices joined by the parallel edges of `F` is
the number of these edges. -/
theorem edgeReachability_banana {u w : α} {F : Set β} (huw : u ≠ w) :
    (banana u w F).edgeReachability u w = F.encard :=
  ENat.eq_of_forall_natCast_le_iff fun _ ↦ by
    rw [← isEdgeReachable_iff_le_edgeReachability, isEdgeReachable_banana_iff huw]

/-- Two distinct vertices joined by the parallel edges of `F` form a `k`-edge-connected graph
exactly when there are at least `k` of these edges. -/
theorem isEdgeConnected_banana_iff {u w : α} {F : Set β} (huw : u ≠ w) :
    (banana u w F).IsEdgeConnected k ↔ k ≤ F.encard := by
  rw [← isEdgeReachable_banana_iff huw]
  refine ⟨fun h ↦ h (by simp) (by simp), fun h x hx y hy ↦ ?_⟩
  simp only [vertexSet_banana, mem_insert_iff, mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact .refl (by simp)
  · exact h
  · exact h.symm
  · exact .refl (by simp)

/-- The edge connectivity of two distinct vertices joined by the parallel edges of `F` is the
number of these edges; in particular a single edge gives edge connectivity `1`. -/
theorem edgeConnectivity_banana {u w : α} {F : Set β} (huw : u ≠ w) :
    (banana u w F).edgeConnectivity = F.encard :=
  ENat.eq_of_forall_natCast_le_iff fun _ ↦ by
    rw [← isEdgeConnected_iff_le_edgeConnectivity, isEdgeConnected_banana_iff huw]

end Graph
