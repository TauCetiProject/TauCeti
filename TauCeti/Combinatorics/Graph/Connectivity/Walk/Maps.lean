/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Delete
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Basic

/-!
# Mapping multigraph walks to supergraphs

This file transports an edge-labelled multigraph walk along a graph inclusion and restricts a
walk to a subgraph containing all its traversed edges. Since the ambient vertex and edge types do
not change, both operations preserve the support and edge list. In particular, they preserve
paths, trails, cycles, and reachability. In particular, reachability after deleting a set of edges
is witnessed exactly by walks avoiding those edges.

The interface follows Mathlib's `SimpleGraph.Walk.mapLe`, `SimpleGraph.Walk.transfer`, and
`SimpleGraph.reachable_deleteEdges_iff_exists_walk`, adapted to retain multigraph edge identities.
-/

public section

universe u v

namespace Graph

namespace Walk

variable {α : Type u} {β : Type v} {G H K : Graph α β}
variable {x y z : α}

/-- Regard a walk in a subgraph as a walk in a supergraph. -/
def mapLe (h : G ≤ H) : {x y : α} → G.Walk x y → H.Walk x y
  | _, _, .nil => .nil
  | _, _, .cons e he p => .cons e (he.mono h) (p.mapLe h)

@[simp]
theorem mapLe_nil (h : G ≤ H) : (nil : G.Walk x x).mapLe h = nil :=
  (rfl)

@[simp]
theorem mapLe_cons (h : G ≤ H) (e : β) (he : G.IsLink e x y) (p : G.Walk y z) :
    (cons e he p).mapLe h = cons e (he.mono h) (p.mapLe h) :=
  (rfl)

@[simp]
theorem _root_.Graph.IsLink.mapLe_toWalk (h : G ≤ H) (he : G.IsLink e x y) :
    he.toWalk.mapLe h = (he.mono h).toWalk :=
  by rw [he.toWalk_eq_cons, (he.mono h).toWalk_eq_cons, mapLe_cons, mapLe_nil]

@[simp]
theorem mapLe_rfl (p : G.Walk x y) : p.mapLe le_rfl = p := by
  induction p with
  | nil => rfl
  | cons e he p ih => simp [ih]

@[simp]
theorem mapLe_mapLe (hGH : G ≤ H) (hHK : H ≤ K) (p : G.Walk x y) :
    (p.mapLe hGH).mapLe hHK = p.mapLe (hGH.trans hHK) := by
  induction p with
  | nil => rfl
  | cons e he p ih => simp [ih]

@[simp]
theorem length_mapLe (h : G ≤ H) (p : G.Walk x y) : (p.mapLe h).length = p.length := by
  induction p with
  | nil => simp
  | cons e he p ih => simp [ih]

@[simp]
theorem support_mapLe_eq_support (h : G ≤ H) (p : G.Walk x y) :
    (p.mapLe h).support = p.support := by
  induction p with
  | nil => simp
  | cons e he p ih => simp [ih]

@[simp]
theorem edges_mapLe_eq_edges (h : G ≤ H) (p : G.Walk x y) :
    (p.mapLe h).edges = p.edges := by
  induction p with
  | nil => simp
  | cons e he p ih => simp [ih]

@[simp]
theorem mapLe_append (h : G ≤ H) (p : G.Walk x y) (q : G.Walk y z) :
    (p.append q).mapLe h = (p.mapLe h).append (q.mapLe h) := by
  induction p with
  | nil => simp
  | cons e he p ih => simp [ih]

@[simp]
theorem reverse_mapLe (h : G ≤ H) (p : G.Walk x y) :
    (p.mapLe h).reverse = p.reverse.mapLe h := by
  induction p with
  | nil => simp
  | cons e he p ih => simp [ih]

@[simp]
theorem mapLe_nil_iff (h : G ≤ H) (p : G.Walk x y) : (p.mapLe h).Nil ↔ p.Nil := by
  cases p <;> simp

@[simp]
theorem isTrail_mapLe (h : G ≤ H) (p : G.Walk x y) :
    (p.mapLe h).IsTrail ↔ p.IsTrail := by
  rw [isTrail_def, isTrail_def, edges_mapLe_eq_edges]

alias ⟨IsTrail.of_mapLe, IsTrail.mapLe⟩ := isTrail_mapLe

@[simp]
theorem isPath_mapLe (h : G ≤ H) (p : G.Walk x y) :
    (p.mapLe h).IsPath ↔ p.IsPath := by
  rw [isPath_def, isPath_def, support_mapLe_eq_support]

alias ⟨IsPath.of_mapLe, IsPath.mapLe⟩ := isPath_mapLe

@[simp]
theorem isCycle_mapLe (h : G ≤ H) (p : G.Walk x x) :
    (p.mapLe h).IsCycle ↔ p.IsCycle := by
  simp only [isCycle_def, edges_mapLe_eq_edges, support_mapLe_eq_support,
    ne_eq, eq_nil_iff_nil, mapLe_nil_iff]

alias ⟨IsCycle.of_mapLe, IsCycle.mapLe⟩ := isCycle_mapLe

/-! ### Restriction to a subgraph -/

/-- Restrict a walk to a subgraph containing every edge that it traverses. -/
def transfer (hGH : G ≤ H) :
    {x y : α} → (p : H.Walk x y) → (∀ e, e ∈ p.edges → e ∈ E(G)) → G.Walk x y
  | _, _, .nil, _ => .nil
  | _, _, .cons e he p, hp =>
      .cons e ((hGH.isLink_iff (hp e (by simp))).mpr he)
        (p.transfer hGH fun f hf ↦ hp f (by simp [hf]))

@[simp]
theorem transfer_nil (hGH : G ≤ H) (hp : ∀ e, e ∈ (nil : H.Walk x x).edges → e ∈ E(G)) :
    (nil : H.Walk x x).transfer hGH hp = nil :=
  (rfl)

@[simp]
theorem transfer_cons (hGH : G ≤ H) (e : β) (he : H.IsLink e x y) (p : H.Walk y z)
    (hp : ∀ f, f ∈ (cons e he p).edges → f ∈ E(G)) :
    (cons e he p).transfer hGH hp =
      cons e ((hGH.isLink_iff (hp e (by simp))).mpr he)
        (p.transfer hGH fun f hf ↦ hp f (by simp [hf])) :=
  (rfl)

/-- Restriction is independent of the proofs that the traversed edges lie in the subgraph. -/
theorem transfer_congr (hGH : G ≤ H) {p q : H.Walk x y}
    (hp : ∀ e, e ∈ p.edges → e ∈ E(G)) (hq : ∀ e, e ∈ q.edges → e ∈ E(G))
    (hpq : p = q) : p.transfer hGH hp = q.transfer hGH hq := by
  subst q
  rfl

@[simp]
theorem _root_.Graph.IsLink.transfer_toWalk (hGH : G ≤ H) (he : H.IsLink e x y)
    (hp : ∀ f, f ∈ he.toWalk.edges → f ∈ E(G)) :
    he.toWalk.transfer hGH hp =
      ((hGH.isLink_iff (hp e (by simp))).mpr he).toWalk := by
  have hp' : ∀ f, f ∈ (cons e he (nil : H.Walk y y)).edges → f ∈ E(G) := by
    intro f hf
    apply hp f
    rwa [he.toWalk_eq_cons]
  calc
    he.toWalk.transfer hGH hp =
        (cons e he (nil : H.Walk y y)).transfer hGH hp' :=
      transfer_congr hGH hp hp' he.toWalk_eq_cons
    _ = ((hGH.isLink_iff (hp e (by simp))).mpr he).toWalk := by
      rw [transfer_cons, transfer_nil,
        ((hGH.isLink_iff (hp e (by simp))).mpr he).toWalk_eq_cons]

@[simp]
theorem length_transfer (hGH : G ≤ H) (p : H.Walk x y)
    (hp : ∀ e, e ∈ p.edges → e ∈ E(G)) :
    (p.transfer hGH hp).length = p.length := by
  induction p with
  | nil => simp
  | cons e he p ih => simp [ih]

@[simp]
theorem support_transfer (hGH : G ≤ H) (p : H.Walk x y)
    (hp : ∀ e, e ∈ p.edges → e ∈ E(G)) :
    (p.transfer hGH hp).support = p.support := by
  induction p with
  | nil => simp
  | cons e he p ih => simp [ih]

@[simp]
theorem edges_transfer (hGH : G ≤ H) (p : H.Walk x y)
    (hp : ∀ e, e ∈ p.edges → e ∈ E(G)) :
    (p.transfer hGH hp).edges = p.edges := by
  induction p with
  | nil => simp
  | cons e he p ih => simp [ih]

@[simp]
theorem transfer_append (hGH : G ≤ H) (p : H.Walk x y) (q : H.Walk y z)
    (hpq : ∀ e, e ∈ (p.append q).edges → e ∈ E(G)) :
    (p.append q).transfer hGH hpq =
      (p.transfer hGH fun e he ↦ hpq e (by simp [he])).append
        (q.transfer hGH fun e he ↦ hpq e (by simp [he])) := by
  induction p with
  | nil => simp
  | cons e he p ih => simp [ih]

@[simp]
theorem reverse_transfer (hGH : G ≤ H) (p : H.Walk x y)
    (hp : ∀ e, e ∈ p.edges → e ∈ E(G)) :
    (p.transfer hGH hp).reverse =
      p.reverse.transfer hGH (by simpa only [edges_reverse, List.mem_reverse] using hp) := by
  induction p with
  | nil => simp
  | cons e he p ih => simp [ih]

@[simp]
theorem transfer_nil_iff (hGH : G ≤ H) (p : H.Walk x y)
    (hp : ∀ e, e ∈ p.edges → e ∈ E(G)) :
    (p.transfer hGH hp).Nil ↔ p.Nil := by
  cases p <;> simp

@[simp]
theorem isTrail_transfer (hGH : G ≤ H) (p : H.Walk x y)
    (hp : ∀ e, e ∈ p.edges → e ∈ E(G)) :
    (p.transfer hGH hp).IsTrail ↔ p.IsTrail := by
  rw [isTrail_def, isTrail_def, edges_transfer]

@[simp]
theorem isPath_transfer (hGH : G ≤ H) (p : H.Walk x y)
    (hp : ∀ e, e ∈ p.edges → e ∈ E(G)) :
    (p.transfer hGH hp).IsPath ↔ p.IsPath := by
  rw [isPath_def, isPath_def, support_transfer]

@[simp]
theorem isCycle_transfer (hGH : G ≤ H) (p : H.Walk x x)
    (hp : ∀ e, e ∈ p.edges → e ∈ E(G)) :
    (p.transfer hGH hp).IsCycle ↔ p.IsCycle := by
  simp only [isCycle_def, edges_transfer, support_transfer, ne_eq, eq_nil_iff_nil,
    transfer_nil_iff]

@[simp]
theorem mapLe_transfer (hGH : G ≤ H) (p : H.Walk x y)
    (hp : ∀ e, e ∈ p.edges → e ∈ E(G)) :
    (p.transfer hGH hp).mapLe hGH = p := by
  induction p with
  | nil => simp
  | cons e he p ih => simp [ih]

@[simp]
theorem transfer_mapLe (hGH : G ≤ H) (p : G.Walk x y)
    (hp : ∀ e, e ∈ (p.mapLe hGH).edges → e ∈ E(G)) :
    (p.mapLe hGH).transfer hGH hp = p := by
  induction p with
  | nil => simp
  | cons e he p ih => simp [ih]

/-- Mapping a walk to a supergraph is injective. -/
theorem mapLe_injective (hGH : G ≤ H) (x y : α) :
    Function.Injective (mapLe hGH : G.Walk x y → H.Walk x y) := by
  intro p q hpq
  have hp : ∀ e, e ∈ (p.mapLe hGH).edges → e ∈ E(G) := by
    simpa only [edges_mapLe_eq_edges] using p.edges_subset_edgeSet
  have hq : ∀ e, e ∈ (q.mapLe hGH).edges → e ∈ E(G) := by
    simpa only [edges_mapLe_eq_edges] using q.edges_subset_edgeSet
  calc
    p = (p.mapLe hGH).transfer hGH hp := (transfer_mapLe hGH p hp).symm
    _ = (q.mapLe hGH).transfer hGH hq := transfer_congr hGH hp hq hpq
    _ = q := transfer_mapLe hGH q hq

end Walk

namespace Reachable

variable {α : Type u} {β : Type v} {G H : Graph α β} {x y : α}

/-- Reachability is monotone under inclusion of multigraphs. -/
protected theorem mono (hGH : G ≤ H) (hxy : G.Reachable x y) : H.Reachable x y := by
  rcases reachable_def.mp hxy with ⟨hx, ⟨p⟩⟩
  exact reachable_def.mpr ⟨hGH.vertexSet_mono hx, ⟨p.mapLe hGH⟩⟩

end Reachable

/-- Pointwise reachability is monotone under inclusion of multigraphs. -/
theorem reachable_mono {α : Type u} {β : Type v} {G H : Graph α β} (hGH : G ≤ H) :
    G.Reachable ≤ H.Reachable :=
  fun _ _ ↦ Reachable.mono hGH

/-- Two points are reachable after deleting a set of edges exactly when the first is an actual
vertex and some walk between them traverses none of the deleted edges. -/
theorem reachable_deleteEdges_iff_exists_walk {α : Type u} {β : Type v} {G : Graph α β}
    {F : Set β} {x y : α} :
    (G.deleteEdges F).Reachable x y ↔ x ∈ V(G) ∧ ∃ p : G.Walk x y, ∀ e ∈ p.edges, e ∉ F := by
  constructor
  · rintro h
    obtain ⟨hx, ⟨p⟩⟩ := reachable_def.mp h
    refine ⟨by simpa using hx, p.mapLe deleteEdges_le, fun e he ↦ ?_⟩
    rw [Walk.edges_mapLe_eq_edges] at he
    have he' := p.edges_subset_edgeSet he
    rw [edgeSet_deleteEdges] at he'
    exact he'.2
  · rintro ⟨hx, p, hp⟩
    refine (p.transfer deleteEdges_le fun e he ↦ ?_).reachable (by simpa using hx)
    rw [edgeSet_deleteEdges]
    exact ⟨p.edges_subset_edgeSet he, hp e he⟩

end Graph
