/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Menger
public import TauCeti.Data.ENat.Lattice

/-!
# Vertex reachability and vertex connectivity of simple graphs

Two vertices `u, v` of a simple graph `G` are `k`-vertex-reachable, `G.IsVertexReachable k u v`,
when they remain reachable after deleting any set of fewer than `k` vertices other than `u` and
`v`; deletion of a set `s` is the subgraph `G.induce sᶜ` induced on the remaining vertices. The
graph is `k`-vertex-connected, `G.IsVertexConnected k`, when it has at least `k + 1` vertices (more
than `k` for finite `k`, infinitely many for `k = ⊤`) and any two vertices are
`k`-vertex-reachable. Thus a single vertex is `0`- but not `1`-vertex-connected,
and the complete graph on `n ≥ 1` vertices is `(n - 1)`- but not `n`-vertex-connected. The numerical
vertex connectivity `G.vertexConnectivity` is the supremum in `ℕ∞` of the natural thresholds at
which `G` is vertex-connected; it is `0` on the empty vertex type and finite on a finite one.

Adjacent vertices are `k`-vertex-reachable for every `k`, since no deletion of other vertices can
separate them. Vertex reachability is therefore not transitive, and for adjacent vertices it
says nothing about internally disjoint paths. For distinct nonadjacent vertices on a finite
vertex type, Menger's theorem identifies `k`-vertex-reachability with the existence of `k` paths
pairwise sharing no vertex other than their ends. On a finite graph with more than `k` vertices,
`k`-vertex-connectivity is the existence of `k` such paths between every two distinct vertices,
adjacent ones included.

The definitions follow the proposal
[mathlib4#33355](https://github.com/leanprover-community/mathlib4/pull/33355), and their shape
and API follow Mathlib's `SimpleGraph.IsEdgeReachable` and `SimpleGraph.IsEdgeConnected`. The
numerical invariant follows the multigraph `Graph.edgeConnectivity` in
`TauCeti.Combinatorics.Graph.Connectivity.EdgeConnectivity`, a supremum in `ℕ∞` of natural
thresholds. The vertex count condition is the usual one, as in R. Diestel, *Graph Theory*, 5th
ed., Graduate Texts in Mathematics 173, Springer, 2017, Section 1.4.

## Main definitions

* `SimpleGraph.IsVertexReachable G k u v`: `u` and `v` stay reachable after deleting fewer than
  `k` other vertices.
* `SimpleGraph.IsVertexConnected G k`: `G` has at least `k + 1` vertices, any two of which are
  `k`-vertex-reachable.
* `SimpleGraph.vertexConnectivity G`: the supremum in `ℕ∞` of the natural thresholds at which `G`
  is vertex-connected.

## Main results

* `SimpleGraph.isVertexReachable_one`, `SimpleGraph.isVertexConnected_one`: the threshold `1` is
  reachability, respectively connectedness on at least two vertices.
* `SimpleGraph.isVertexConnected_iff`: `G` is `k`-vertex-connected exactly when it has at least
  `k + 1` vertices and stays preconnected after deleting fewer than `k` vertices.
* `SimpleGraph.isVertexReachable_of_pairwise_internallyDisjoint`: `k` walks pairwise sharing no
  vertex other than their ends make their ends `k`-vertex-reachable.
* `SimpleGraph.isVertexConnected_iff_le_vertexConnectivity`: on a nonempty vertex type, the
  numerical invariant records exactly the thresholds at which `G` is vertex-connected.
* `SimpleGraph.vertexConnectivity_add_one_le_card`: on a nonempty vertex type, `κ + 1` is at
  most the number of vertices, where `κ` is the vertex connectivity.
* `SimpleGraph.vertexConnectivity_top`: the complete graph has vertex connectivity
  `ENat.card V - 1`.
* `SimpleGraph.isVertexReachable_iff_exists_paths`: **Menger's theorem**, predicate form, for
  nonadjacent vertices.
* `SimpleGraph.isVertexConnected_iff_forall_exists_paths`: the **global form of Menger's
  theorem**: on a finite vertex type with more than `k` vertices, `k`-vertex-connectivity is the
  existence of `k` distinct internally disjoint paths between every two distinct vertices.

## Implementation notes

The Menger statements are derived from the witness forms in
`TauCeti.Combinatorics.SimpleGraph.Connectivity.Menger`. For adjacent vertices `s` and `t` of a
`k`-vertex-connected graph, `SimpleGraph.exists_paths_vertexSeparator_card_add_one_eq` gives
`#X + 1` paths together with a set `X` separating `s` from `t` after the edge `s(s, t)` is deleted.
If `#X + 1 < k`, some vertex `w` lies outside `X ∪ {s, t}`, and deleting `X` together with `t`, or
with `s`, leaves `w` reachable from `s`, or from `t`, by walks avoiding the edge `s(s, t)`; so `X`
does not separate `s` from `t`. Hence `k ≤ #X + 1`.
-/

public section

open Finset

universe u

namespace SimpleGraph

variable {V : Type u} {G H : SimpleGraph V} {k l : ℕ∞} {u v w : V}

/-! ### Vertex reachability -/

variable (G k u v) in
/-- Two vertices are `k`-vertex-reachable if they remain reachable after deleting any set of fewer
than `k` vertices other than themselves. -/
def IsVertexReachable : Prop :=
  ∀ ⦃s : Set V⦄, s.encard < k → (hu : u ∉ s) → (hv : v ∉ s) →
    (G.induce sᶜ).Reachable ⟨u, hu⟩ ⟨v, hv⟩

theorem isVertexReachable_def : G.IsVertexReachable k u v ↔
    ∀ ⦃s : Set V⦄, s.encard < k → (hu : u ∉ s) → (hv : v ∉ s) →
      (G.induce sᶜ).Reachable ⟨u, hu⟩ ⟨v, hv⟩ :=
  Iff.rfl

/-- Vertex reachability through walks: after deleting fewer than `k` vertices other than `u` and
`v`, some walk from `u` to `v` avoids the deleted vertices. -/
theorem isVertexReachable_iff_exists_walk : G.IsVertexReachable k u v ↔
    ∀ ⦃s : Set V⦄, s.encard < k → u ∉ s → v ∉ s → ∃ p : G.Walk u v, ∀ x ∈ p.support, x ∉ s := by
  simp only [isVertexReachable_def, reachable_induce_iff, Set.mem_compl_iff]

@[refl, simp]
protected theorem IsVertexReachable.rfl : G.IsVertexReachable k u u :=
  fun _ _ _ _ ↦ .rfl

protected theorem IsVertexReachable.refl (u : V) : G.IsVertexReachable k u u := .rfl

@[symm]
theorem IsVertexReachable.symm (h : G.IsVertexReachable k u v) : G.IsVertexReachable k v u :=
  fun _ hs hv hu ↦ (h hs hu hv).symm

theorem isVertexReachable_comm : G.IsVertexReachable k u v ↔ G.IsVertexReachable k v u :=
  ⟨.symm, .symm⟩

/-- Vertex reachability at a smaller threshold follows from vertex reachability at a larger
one. -/
@[gcongr]
theorem IsVertexReachable.anti (hkl : k ≤ l) (h : G.IsVertexReachable l u v) :
    G.IsVertexReachable k u v :=
  fun _ hs ↦ h (hs.trans_le hkl)

/-- Vertex reachability is monotone in the graph. -/
@[gcongr]
theorem IsVertexReachable.mono (hGH : G ≤ H) (h : G.IsVertexReachable k u v) :
    H.IsVertexReachable k u v :=
  fun _ hs hu hv ↦ (h hs hu hv).mono (comap_monotone _ hGH)

@[simp]
protected theorem IsVertexReachable.zero : G.IsVertexReachable 0 u v := by
  simp [isVertexReachable_def]

/-- Reachability is `1`-vertex-reachability. -/
@[simp]
theorem isVertexReachable_one : G.IsVertexReachable 1 u v ↔ G.Reachable u v := by
  simp [isVertexReachable_iff_exists_walk, Reachable]

theorem IsVertexReachable.reachable (hk : k ≠ 0) (h : G.IsVertexReachable k u v) :
    G.Reachable u v :=
  isVertexReachable_one.mp (h.anti (Order.one_le_iff_ne_zero.mpr hk))

/-- Adjacent vertices are `k`-vertex-reachable for every `k`. -/
theorem Adj.isVertexReachable (h : G.Adj u v) : G.IsVertexReachable k u v :=
  isVertexReachable_iff_exists_walk.2 fun _ _ hu hv ↦ ⟨h.toWalk, by simp [hu, hv]⟩

/-- **Weak duality for vertex reachability.** If there are `n` walks from `u` to `v` pairwise
sharing no vertex other than `u` and `v`, then `u` and `v` are `n`-vertex-reachable. No finiteness
assumption on `V` is needed. -/
theorem isVertexReachable_of_pairwise_internallyDisjoint {n : ℕ} {P : Fin n → G.Walk u v}
    (hP : Pairwise fun i j ↦ (P i).InternallyDisjoint (P j)) : G.IsVertexReachable n u v := by
  -- A set of fewer than `n` vertices is finite, so weak duality for internally disjoint walks
  -- (`SimpleGraph.card_le_card_of_not_reachable_induce`) applies to it.
  intro s hs hu hv
  lift s to Finset V using Set.encard_lt_top_iff.1 (hs.trans (ENat.natCast_lt_top n))
  by_contra h
  have hle := card_le_card_of_not_reachable_induce hP hu hv h
  rw [Fintype.card_fin] at hle
  rw [Set.encard_coe_eq_coe_finsetCard, Nat.cast_lt] at hs
  exact hs.not_ge hle

/-! ### Vertex connectivity -/

variable (G k) in
/-- A graph is `k`-vertex-connected if it has at least `k + 1` vertices and any two vertices are
`k`-vertex-reachable. For finite `k` this asks for more than `k` vertices; for `k = ⊤` it asks for
infinitely many. -/
def IsVertexConnected : Prop :=
  k + 1 ≤ ENat.card V ∧ ∀ u v, G.IsVertexReachable k u v

theorem isVertexConnected_def :
    G.IsVertexConnected k ↔ k + 1 ≤ ENat.card V ∧ ∀ u v, G.IsVertexReachable k u v :=
  Iff.rfl

/-- A graph is `k`-vertex-connected exactly when it has at least `k + 1` vertices and stays
preconnected after deleting any set of fewer than `k` vertices. -/
theorem isVertexConnected_iff : G.IsVertexConnected k ↔
    k + 1 ≤ ENat.card V ∧ ∀ ⦃s : Set V⦄, s.encard < k → (G.induce sᶜ).Preconnected :=
  and_congr_right fun _ ↦ ⟨fun h _ hs ⟨u, hu⟩ ⟨v, hv⟩ ↦ h u v hs hu hv,
    fun h u v _ hs hu hv ↦ h hs ⟨u, hu⟩ ⟨v, hv⟩⟩

theorem IsVertexConnected.add_one_le_card (h : G.IsVertexConnected k) : k + 1 ≤ ENat.card V :=
  h.1

theorem IsVertexConnected.isVertexReachable (h : G.IsVertexConnected k) (u v : V) :
    G.IsVertexReachable k u v :=
  h.2 u v

theorem IsVertexConnected.nonempty (h : G.IsVertexConnected k) : Nonempty V :=
  (ENat.one_le_card_iff_nonempty V).1 (le_add_self.trans h.1)

/-- Vertex connectivity at a smaller threshold follows from vertex connectivity at a larger
one. -/
@[gcongr]
theorem IsVertexConnected.anti (hkl : k ≤ l) (h : G.IsVertexConnected l) :
    G.IsVertexConnected k :=
  ⟨le_trans (by gcongr) h.1, fun u v ↦ (h.2 u v).anti hkl⟩

/-- Vertex connectivity is monotone in the graph. -/
@[gcongr]
theorem IsVertexConnected.mono (hGH : G ≤ H) (h : G.IsVertexConnected k) :
    H.IsVertexConnected k :=
  ⟨h.1, fun u v ↦ (h.2 u v).mono hGH⟩

/-- A graph is `0`-vertex-connected exactly when its vertex type is nonempty. -/
@[simp]
theorem isVertexConnected_zero : G.IsVertexConnected 0 ↔ Nonempty V := by
  simp [isVertexConnected_def, ENat.one_le_card_iff_nonempty]

/-- A graph is `1`-vertex-connected exactly when it is connected and has at least two
vertices. -/
@[simp]
theorem isVertexConnected_one : G.IsVertexConnected 1 ↔ G.Connected ∧ Nontrivial V := by
  rw [isVertexConnected_def, ENat.add_one_le_iff ENat.one_ne_top, ENat.one_lt_card_iff_nontrivial,
    connected_iff]
  simp only [isVertexReachable_one]
  exact ⟨fun ⟨_, h⟩ ↦ ⟨⟨h, inferInstance⟩, inferInstance⟩, fun ⟨⟨h, _⟩, _⟩ ↦ ⟨‹_›, h⟩⟩

theorem IsVertexConnected.preconnected (hk : k ≠ 0) (h : G.IsVertexConnected k) :
    G.Preconnected :=
  fun u v ↦ (h.2 u v).reachable hk

theorem IsVertexConnected.connected (hk : k ≠ 0) (h : G.IsVertexConnected k) : G.Connected :=
  (connected_iff G).2 ⟨h.preconnected hk, h.nonempty⟩

/-- The complete graph is `k`-vertex-connected exactly when it has at least `k + 1` vertices. -/
@[simp]
theorem isVertexConnected_top_iff : (⊤ : SimpleGraph V).IsVertexConnected k ↔
    k + 1 ≤ ENat.card V := by
  refine ⟨And.left, fun h ↦ ⟨h, fun u v ↦ ?_⟩⟩
  obtain rfl | huv := eq_or_ne u v
  · exact .rfl
  · exact ((top_adj u v).2 huv).isVertexReachable

/-! ### The numerical invariant -/

variable (G) in
/-- The vertex connectivity of a simple graph: the supremum in `ℕ∞` of the natural thresholds `k`
at which it is `k`-vertex-connected. It is `0` on the empty vertex type. -/
noncomputable def vertexConnectivity : ℕ∞ :=
  ⨆ (k : ℕ) (_ : G.IsVertexConnected k), (k : ℕ∞)

/-- On a nonempty vertex type, vertex connectivity records exactly the thresholds at which the
graph is vertex-connected. -/
theorem isVertexConnected_iff_le_vertexConnectivity [Nonempty V] (k : ℕ) :
    G.IsVertexConnected k ↔ k ≤ G.vertexConnectivity :=
  (Antitone.natCast_le_iSup_iff
    (fun _ _ hkl (h : G.IsVertexConnected _) ↦ h.anti (Nat.cast_le.2 hkl))
    (by simpa using ‹Nonempty V›)).symm

@[simp]
theorem vertexConnectivity_of_isEmpty [IsEmpty V] : G.vertexConnectivity = 0 :=
  le_antisymm (iSup₂_le fun _ hk ↦ isEmptyElim hk.nonempty.some) bot_le

/-- Vertex connectivity is monotone in the graph. -/
@[gcongr]
theorem vertexConnectivity_mono (hGH : G ≤ H) : G.vertexConnectivity ≤ H.vertexConnectivity :=
  iSup_mono fun _ ↦ iSup_mono' fun hk ↦ ⟨hk.mono hGH, le_rfl⟩

theorem vertexConnectivity_le_card : G.vertexConnectivity ≤ ENat.card V :=
  iSup₂_le fun _ hk ↦ le_self_add.trans hk.1

/-- The vertex connectivity of a graph on a finite vertex type is finite. -/
@[simp]
theorem vertexConnectivity_ne_top [Finite V] : G.vertexConnectivity ≠ ⊤ :=
  ne_top_of_le_ne_top ENat.card_lt_top_of_finite.ne vertexConnectivity_le_card

/-- On a nonempty vertex type, the vertex connectivity plus one is at most the number of
vertices, so the vertex connectivity is strictly less than it when `V` is finite. -/
theorem vertexConnectivity_add_one_le_card [Nonempty V] :
    G.vertexConnectivity + 1 ≤ ENat.card V := by
  cases finite_or_infinite V
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 G.vertexConnectivity_ne_top
    rw [← hn]
    exact ((isVertexConnected_iff_le_vertexConnectivity n).2 hn.le).1
  · rw [ENat.card_eq_top_of_infinite]
    exact le_top

/-- The complete graph on `V` has vertex connectivity `ENat.card V - 1`. -/
@[simp]
theorem vertexConnectivity_top : (⊤ : SimpleGraph V).vertexConnectivity = ENat.card V - 1 := by
  cases isEmpty_or_nonempty V
  · simp [(ENat.card_eq_zero_iff_empty V).2 ‹_›]
  · refine ENat.eq_of_forall_natCast_le_iff fun k ↦ ?_
    rw [← isVertexConnected_iff_le_vertexConnectivity, isVertexConnected_top_iff,
      (ENat.addLECancellable_of_ne_top ENat.one_ne_top).le_tsub_iff_right
        ((ENat.one_le_card_iff_nonempty V).2 ‹_›)]

/-! ### Menger's theorem -/

/-- **Menger's theorem for vertex reachability.** Two distinct nonadjacent vertices `s` and `t` of
a simple graph on a finite vertex type are `k`-vertex-reachable exactly when there are `k` paths
from `s` to `t` pairwise sharing no vertex other than `s` and `t`. -/
theorem isVertexReachable_iff_exists_paths [Finite V] {s t : V} (hst : s ≠ t) (hadj : ¬G.Adj s t)
    (k : ℕ) :
    G.IsVertexReachable k s t ↔ ∃ P : Fin k → G.Walk s t, (∀ i, (P i).IsPath) ∧
      Pairwise fun i j ↦ (P i).InternallyDisjoint (P j) :=
  ⟨fun h ↦ (forall_reachable_induce_iff_exists_paths hst hadj k).1 fun X hs ht hX ↦
      h (by simpa using hX) hs ht,
    fun ⟨_, _, hP⟩ ↦ isVertexReachable_of_pairwise_internallyDisjoint hP⟩

/-- If `x` and `w` stay reachable after deleting `y` and the vertices of `X`, they stay reachable
after deleting the edge `s(x, y)` and the vertices of `X`. -/
private theorem reachable_induce_deleteEdges_of_isVertexReachable {x y : V} {X : Finset V}
    (h : G.IsVertexReachable k x w) (hk : (#X + 1 : ℕ∞) < k) (hxy : x ≠ y) (hwy : w ≠ y)
    (hx : x ∉ X) (hw : w ∉ X) :
    ((G.deleteEdges {s(x, y)}).induce (X : Set V)ᶜ).Reachable ⟨x, hx⟩ ⟨w, hw⟩ := by
  obtain ⟨p, hp⟩ := isVertexReachable_iff_exists_walk.1 h (s := insert y (X : Set V))
    ((Set.encard_insert_le _ _).trans_lt (by simpa [add_comm] using hk)) (by simp [hxy, hx])
    (by simp [hwy, hw])
  refine reachable_induce_iff.2 ⟨p.toDeleteEdges {s(x, y)} fun e he hey ↦ ?_, fun z hz ↦ ?_⟩
  · rw [Set.mem_singleton_iff] at hey
    subst hey
    exact hp y (p.snd_mem_support_of_mem_edges he) (Set.mem_insert _ _)
  · rw [Walk.support_transfer] at hz
    exact fun hzX ↦ hp z hz (Set.mem_insert_of_mem _ hzX)

/-- **The global form of Menger's theorem.** A simple graph on a finite vertex type with more than
`k` vertices is `k`-vertex-connected exactly when every two distinct vertices `s` and `t`,
adjacent or not, are joined by `k` distinct paths pairwise sharing no vertex other than `s` and
`t`. -/
theorem isVertexConnected_iff_forall_exists_paths [Finite V] {k : ℕ} (hk : k < Nat.card V) :
    G.IsVertexConnected k ↔ ∀ s t, s ≠ t → ∃ P : Fin k → G.Walk s t, Function.Injective P ∧
      (∀ i, (P i).IsPath) ∧ Pairwise fun i j ↦ (P i).InternallyDisjoint (P j) := by
  have hcard : (k : ℕ∞) + 1 ≤ ENat.card V := by
    have := Fintype.ofFinite V
    rw [ENat.card_eq_coe_fintype_card, ← Nat.card_eq_fintype_card]
    exact_mod_cast Nat.succ_le_of_lt hk
  refine ⟨fun h s t hst ↦ ?_, fun h ↦ ⟨hcard, fun s t ↦ ?_⟩⟩
  · -- It suffices to find `n ≥ k` such paths; keep the first `k` of them.
    suffices ∃ (n : ℕ) (P : Fin n → G.Walk s t), k ≤ n ∧ Function.Injective P ∧
        (∀ i, (P i).IsPath) ∧ Pairwise fun i j ↦ (P i).InternallyDisjoint (P j) by
      obtain ⟨n, P, hkn, hinj, hP, hdisj⟩ := this
      exact ⟨P ∘ Fin.castLE hkn, hinj.comp (Fin.castLE_injective hkn), fun i ↦ hP _,
        fun i j hij ↦ hdisj ((Fin.castLE_injective hkn).ne hij)⟩
    by_cases hadj : G.Adj s t
    · obtain ⟨n, P, X, hinj, hP, hdisj, -, hs, ht, hX, rfl⟩ :=
        exists_paths_vertexSeparator_card_add_one_eq hadj
      refine ⟨#X + 1, P, ?_, hinj, hP, hdisj⟩
      by_contra! hlt
      -- A vertex `w` outside `X ∪ {s, t}` is separated from `s` or from `t` after deleting `X`
      -- and the edge `s(s, t)`, while deleting the other end and `X` keeps it reachable.
      classical
      have := Fintype.ofFinite V
      obtain ⟨w, -, hw⟩ := exists_mem_notMem_of_card_lt_card (s := insert s (insert t X))
        (t := univ) (by
          rw [card_univ, ← Nat.card_eq_fintype_card]
          exact (card_insert_le _ _).trans_lt
            (Nat.add_lt_of_lt_sub ((card_insert_le _ _).trans_lt (by omega))))
      simp only [mem_insert, not_or] at hw
      obtain ⟨hws, hwt, hwX⟩ := hw
      have hk' : (#X + 1 : ℕ∞) < k := by exact_mod_cast hlt
      refine hX ((reachable_induce_deleteEdges_of_isVertexReachable (h.2 s w) hk' hst hwt hs
        hwX).trans ?_)
      rw [Sym2.eq_swap]
      exact (reachable_induce_deleteEdges_of_isVertexReachable (h.2 t w) hk' hst.symm hws ht
        hwX).symm
    · obtain ⟨n, P, X, hinj, hP, hdisj, hs, ht, hX, rfl⟩ :=
        exists_paths_vertexSeparator_card_eq hst hadj
      refine ⟨#X, P, ?_, hinj, hP, hdisj⟩
      by_contra! hlt
      exact hX (h.2 s t (by simpa using hlt) hs ht)
  · obtain rfl | hst := eq_or_ne s t
    · exact .rfl
    · obtain ⟨P, -, -, hP⟩ := h s t hst
      exact isVertexReachable_of_pairwise_internallyDisjoint hP

end SimpleGraph
