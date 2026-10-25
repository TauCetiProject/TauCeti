/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Dual graphs of nodal curves

The **dual graph** of a proper nodal curve `X` over an algebraically closed field records how
the curve is assembled from smooth pieces. Its vertices are the irreducible components of the
normalization of `X`, its edges are the nodes of `X`, and the two endpoints of an edge are the
components carrying the two branches of the node; when both branches lie on one component the
edge is a loop. Each vertex is labelled by the genus of its normalized component, and each
marking of a pointed curve is attached to the component on which it lies.

This file introduces that combinatorial structure, `TauCeti.DualGraph`, together with the
numerical invariants through which the geometry of the curve is read off from it:

* the **valence** of a vertex, the number of branches of nodes on the component, so that a loop
  counts twice;
* the **first Betti number** `b₁ = #edges - #vertices + 1` of the connected graph and the
  **arithmetic genus** `pₐ = ∑ᵥ gᵥ + b₁` encoded by the graph;
* the **log-canonical degree** `2gᵥ - 2 + val(v) + n(v)` of a vertex carrying `n(v)` markings,
  which is the degree of `ω_X(s₁ + ⋯ + sₙ)` on the corresponding component.

A pointed nodal curve is stable exactly when every component has positive log-canonical degree,
and semistable when none has negative degree; `TauCeti.DualGraph.IsStable` and
`TauCeti.DualGraph.IsSemistable` are these conditions on the graph.

## Main results

* `TauCeti.DualGraph.sum_valence`: the handshake identity `∑ᵥ val(v) = 2 · #edges`.
* `TauCeti.DualGraph.card_vertex_le_card_edge_add_one`: a connected graph has at most one more
  vertex than it has edges, so the first Betti number is computed without truncation
  (`TauCeti.DualGraph.firstBetti_add_card_vertex`).
* `TauCeti.DualGraph.sum_logCanonicalDegree`: the log-canonical degrees add up to
  `2pₐ - 2 + n`, the total degree of `ω_X(s₁ + ⋯ + sₙ)`.
* `TauCeti.DualGraph.IsStable.card_vertex_le` and `TauCeti.DualGraph.IsStable.card_edge_le`:
  a stable graph of genus `g` with `n` markings has at most `2g - 2 + n` vertices and at most
  `3g - 3 + n` edges.
* `TauCeti.DualGraph.isSemistable_iff_forall_not_isRationalTail`: an unmarked graph of
  arithmetic genus at least one is semistable exactly when it has no rational tails, and
  `TauCeti.DualGraph.isStable_iff_forall_not_isRationalTail_and_not_isRationalBridge`: an
  unmarked graph of arithmetic genus at least two is stable exactly when it has neither rational
  tails nor rational bridges.
* `TauCeti.DualGraph.isRationalTail_or_isRationalBridge_of_logCanonicalDegree_nonpos`: a vertex of
  nonpositive log-canonical degree other than the only vertex is a rational tail with at most one
  marking or an unmarked rational bridge.

## Implementation notes

An edge carries an ordered pair of endpoints, so the two branches of a node are always two
distinct half-edges, even for a loop. Valence counts half-edges, which is what makes a loop
contribute two, matching the two points of the normalization lying over a self-node.

Rational tails and rational bridges are defined without reference to markings, as in the
unpointed theory of the Stacks Project; the characterizations of stability through them are
stated for unmarked graphs.

## References

* [Stacks, Tag 0E6X](https://stacks.math.columbia.edu/tag/0E6X) (semistable curves) and
  [Stacks, Tag 0E73](https://stacks.math.columbia.edu/tag/0E73) (stable curves).
* E. Arbarello, M. Cornalba and P. A. Griffiths, *Geometry of Algebraic Curves, Volume II*,
  Chapter X, for dual graphs of pointed nodal curves.
-/

public section

namespace TauCeti

open Finset

universe u v

/-- The dual graph of a proper nodal curve over an algebraically closed field, with markings
indexed by `ι`.

`Vertex` is the finite nonempty set of irreducible components of the normalization, `Edge` is the
finite set of nodes, `endpoint e 0` and `endpoint e 1` are the components carrying the two
branches of the node `e`, `genus v` is the genus of the normalized component `v`, and `marking i`
is the component carrying the `i`-th marking. The curve is connected, so the graph is. -/
structure DualGraph (ι : Type v) where
  /-- The finite nonempty type of vertices: the components of the normalization. -/
  Vertex : Type u
  /-- The vertices form a finite type. -/
  [vertexFintype : Fintype Vertex]
  /-- Equality of vertices is decidable. -/
  [vertexDecidableEq : DecidableEq Vertex]
  /-- There is at least one vertex. -/
  [vertexNonempty : Nonempty Vertex]
  /-- The finite type of edges: the nodes. -/
  Edge : Type u
  /-- The edges form a finite type. -/
  [edgeFintype : Fintype Edge]
  /-- Equality of edges is decidable. -/
  [edgeDecidableEq : DecidableEq Edge]
  /-- The components carrying the two branches of a node. -/
  endpoint : Edge → Fin 2 → Vertex
  /-- The genus of a normalized component. -/
  genus : Vertex → ℕ
  /-- The component carrying a marking. -/
  marking : ι → Vertex
  /-- Any two vertices are joined by a chain of edges. -/
  connected : ∀ v w, Relation.ReflTransGen
    (fun v w ↦ ∃ e, (endpoint e 0 = v ∧ endpoint e 1 = w) ∨
      (endpoint e 0 = w ∧ endpoint e 1 = v)) v w

namespace DualGraph

variable {ι : Type v} (G : DualGraph ι)

instance : Fintype G.Vertex := G.vertexFintype
instance : DecidableEq G.Vertex := G.vertexDecidableEq
instance : Nonempty G.Vertex := G.vertexNonempty
instance : Fintype G.Edge := G.edgeFintype
instance : DecidableEq G.Edge := G.edgeDecidableEq

/-! ### Adjacency and connectedness -/

/-- Two vertices are adjacent when they are the two endpoints of some edge, in either order.
A vertex carrying a loop is adjacent to itself. -/
def Adj (v w : G.Vertex) : Prop :=
  ∃ e, (G.endpoint e 0 = v ∧ G.endpoint e 1 = w) ∨ (G.endpoint e 0 = w ∧ G.endpoint e 1 = v)

variable {G} in
lemma adj_iff {v w : G.Vertex} : G.Adj v w ↔
    ∃ e, (G.endpoint e 0 = v ∧ G.endpoint e 1 = w) ∨
      (G.endpoint e 0 = w ∧ G.endpoint e 1 = v) :=
  Iff.rfl

variable {G} in
lemma Adj.symm {v w : G.Vertex} (h : G.Adj v w) : G.Adj w v := by
  obtain ⟨e, h | h⟩ := h
  exacts [⟨e, Or.inr h⟩, ⟨e, Or.inl h⟩]

/-- Any two vertices are joined by a chain of adjacencies. -/
lemma reflTransGen_adj (v w : G.Vertex) : Relation.ReflTransGen G.Adj v w :=
  G.connected v w

/-- The simple graph on the vertices joining two distinct vertices when some edge does. -/
def toSimpleGraph : SimpleGraph G.Vertex :=
  SimpleGraph.fromRel G.Adj

@[simp]
lemma toSimpleGraph_adj {v w : G.Vertex} : G.toSimpleGraph.Adj v w ↔ v ≠ w ∧ G.Adj v w := by
  rw [toSimpleGraph, SimpleGraph.fromRel_adj]
  exact and_congr_right fun _ ↦ ⟨fun h ↦ h.elim id Adj.symm, Or.inl⟩

/-- The simple graph underlying a dual graph is connected. -/
theorem toSimpleGraph_connected : G.toSimpleGraph.Connected := by
  obtain ⟨v⟩ := G.vertexNonempty
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨v, fun w ↦ ?_⟩
  rw [SimpleGraph.reachable_iff_reflTransGen]
  induction G.reflTransGen_adj v w with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    by_cases hb : b = c
    · exact hb ▸ ih
    · exact ih.tail (G.toSimpleGraph_adj.mpr ⟨hb, hbc⟩)

variable {G} in
/-- A connectivity criterion for a graph built on the image of a surjection `φ` from the vertices
of `G`: it suffices that each edge of `G` is either collapsed by `φ` or carried by `φ` to an edge
of the new graph, in either orientation. -/
theorem connected_of_surjective {V E : Type*} {f : E → Fin 2 → V} (φ : G.Vertex → V)
    (hφ : Function.Surjective φ)
    (h : ∀ e, φ (G.endpoint e 0) = φ (G.endpoint e 1) ∨
      ∃ e', (f e' 0 = φ (G.endpoint e 0) ∧ f e' 1 = φ (G.endpoint e 1)) ∨
        (f e' 0 = φ (G.endpoint e 1) ∧ f e' 1 = φ (G.endpoint e 0))) (x y : V) :
    Relation.ReflTransGen (fun v w ↦ ∃ e, (f e 0 = v ∧ f e 1 = w) ∨ (f e 0 = w ∧ f e 1 = v))
      x y := by
  obtain ⟨x, rfl⟩ := hφ x
  obtain ⟨y, rfl⟩ := hφ y
  refine Relation.ReflTransGen.lift' φ (fun a b ⟨e, hab⟩ ↦ ?_) x y (G.connected x y)
  rcases h e with heq | ⟨e', h'⟩ <;> obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hab
  · rw [Function.onFun, heq]
  · rw [Function.onFun, heq]
  · exact .single ⟨e', h'⟩
  · exact .single ⟨e', h'.symm⟩

/-- If every edge at `v` is a loop, then `v` is the only vertex: no edge leaves it, and the graph
is connected. -/
theorem eq_of_forall_endpoint_zero_eq_iff {v : G.Vertex}
    (h : ∀ e, G.endpoint e 0 = v ↔ G.endpoint e 1 = v) (w : G.Vertex) : w = v := by
  induction G.reflTransGen_adj v w with
  | refl => rfl
  | @tail b c _ hbc ih =>
    subst ih
    obtain ⟨e, ⟨he₀, he₁⟩ | ⟨he₀, he₁⟩⟩ := hbc
    · rw [← he₁, ← h, he₀]
    · rw [← he₀, h, he₁]

/-- A connected graph has at most one more vertex than it has edges. -/
theorem card_vertex_le_card_edge_add_one :
    Fintype.card G.Vertex ≤ Fintype.card G.Edge + 1 := by
  have hconn := G.toSimpleGraph_connected.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at hconn
  refine hconn.trans (Nat.add_le_add_right ?_ 1)
  -- Every edge of the underlying simple graph is the pair of endpoints of an edge of `G`.
  let f : G.Edge → Sym2 G.Vertex := fun e ↦ s(G.endpoint e 0, G.endpoint e 1)
  have hsub : G.toSimpleGraph.edgeSet ⊆ Set.range f := by
    intro s hs
    induction s using Sym2.ind with
    | h v w =>
      obtain ⟨-, e, ⟨he₀, he₁⟩ | ⟨he₀, he₁⟩⟩ :=
        G.toSimpleGraph_adj.mp (SimpleGraph.mem_edgeSet _ |>.mp hs)
      · exact ⟨e, by simp [f, he₀, he₁]⟩
      · exact ⟨e, by simp [f, he₀, he₁, Sym2.eq_swap]⟩
  calc Nat.card G.toSimpleGraph.edgeSet
      ≤ Nat.card (Set.range f) := Nat.card_mono (Set.toFinite _) hsub
    _ ≤ Nat.card G.Edge := Finite.card_range_le f
    _ = Fintype.card G.Edge := Nat.card_eq_fintype_card

/-! ### Valence and markings -/

/-- The valence of a vertex: the number of branches of nodes lying on the component, that is, the
number of half-edges at the vertex. A loop counts twice. -/
def valence (v : G.Vertex) : ℕ :=
  #{h : G.Edge × Fin 2 | G.endpoint h.1 h.2 = v}

lemma valence_def (v : G.Vertex) :
    G.valence v = #{h : G.Edge × Fin 2 | G.endpoint h.1 h.2 = v} :=
  (rfl)

/-- The valence of a vertex is the sum over the edges of the number of their branches at it. -/
lemma valence_eq_sum (v : G.Vertex) :
    G.valence v = ∑ e, #{i : Fin 2 | G.endpoint e i = v} := by
  simp only [valence_def, card_filter, Fintype.sum_prod_type]

/-- The handshake identity: the valences add up to twice the number of edges. -/
theorem sum_valence : ∑ v, G.valence v = 2 * Fintype.card G.Edge := by
  have := card_eq_sum_card_fiberwise (s := (univ : Finset (G.Edge × Fin 2))) (t := univ)
    (f := fun h ↦ G.endpoint h.1 h.2) fun _ _ ↦ mem_univ _
  simp only [valence, ← this, card_univ, Fintype.card_prod, Fintype.card_fin, mul_comm]

lemma valence_eq_zero_iff {v : G.Vertex} : G.valence v = 0 ↔ ∀ e i, G.endpoint e i ≠ v := by
  simp [valence, filter_eq_empty_iff]

/-- The number of markings carried by a vertex. -/
def numMarkings [Fintype ι] (v : G.Vertex) : ℕ :=
  #{i : ι | G.marking i = v}

lemma numMarkings_def [Fintype ι] (v : G.Vertex) : G.numMarkings v = #{i : ι | G.marking i = v} :=
  (rfl)

/-- Every marking lies on exactly one component. -/
theorem sum_numMarkings [Fintype ι] : ∑ v, G.numMarkings v = Fintype.card ι := by
  have := card_eq_sum_card_fiberwise (s := (univ : Finset ι)) (t := univ) (f := G.marking)
    fun _ _ ↦ mem_univ _
  simp only [numMarkings, ← this, card_univ]

@[simp]
lemma numMarkings_of_isEmpty [Fintype ι] [IsEmpty ι] (v : G.Vertex) : G.numMarkings v = 0 := by
  simp [numMarkings]

/-! ### Betti number and arithmetic genus -/

/-- The first Betti number `#edges - #vertices + 1` of the connected graph. -/
def firstBetti : ℕ :=
  Fintype.card G.Edge + 1 - Fintype.card G.Vertex

lemma firstBetti_def : G.firstBetti = Fintype.card G.Edge + 1 - Fintype.card G.Vertex :=
  (rfl)

/-- The first Betti number is computed without truncation. -/
theorem firstBetti_add_card_vertex :
    G.firstBetti + Fintype.card G.Vertex = Fintype.card G.Edge + 1 := by
  have := G.card_vertex_le_card_edge_add_one
  rw [firstBetti]
  omega

/-- The arithmetic genus encoded by the graph: the sum of the genera of the components and the
first Betti number. -/
def arithmeticGenus : ℕ :=
  ∑ v, G.genus v + G.firstBetti

lemma arithmeticGenus_def : G.arithmeticGenus = ∑ v, G.genus v + G.firstBetti :=
  (rfl)

/-- The arithmetic genus in terms of the numbers of vertices and edges. -/
theorem arithmeticGenus_add_card_vertex :
    G.arithmeticGenus + Fintype.card G.Vertex = ∑ v, G.genus v + Fintype.card G.Edge + 1 := by
  have := G.firstBetti_add_card_vertex
  rw [arithmeticGenus]
  omega

/-- If every edge at `v` is a loop, the graph has the single vertex `v`, and twice its arithmetic
genus is `2 g(v) + val(v)`. -/
theorem two_mul_arithmeticGenus_of_forall_endpoint_zero_eq_iff {v : G.Vertex}
    (h : ∀ e, G.endpoint e 0 = v ↔ G.endpoint e 1 = v) :
    2 * G.arithmeticGenus = 2 * G.genus v + G.valence v := by
  have hv := G.eq_of_forall_endpoint_zero_eq_iff h
  have huniv : (univ : Finset G.Vertex) = {v} := eq_singleton_iff_unique_mem.mpr
    ⟨mem_univ v, fun w _ ↦ hv w⟩
  have hcard : Fintype.card G.Vertex = 1 := by rw [← card_univ, huniv, card_singleton]
  have hval := G.sum_valence
  have hgenus := G.arithmeticGenus_add_card_vertex
  rw [huniv, sum_singleton] at hval hgenus
  omega

/-! ### Log-canonical degree and stability -/

/-- The log-canonical degree `2 g(v) - 2 + val(v) + n(v)` of a vertex carrying `n(v)` markings.
This is the numerical value that the degree of `ω_X(s₁ + ⋯ + sₙ)` takes on the corresponding
component of a pointed nodal curve. -/
def logCanonicalDegree [Fintype ι] (v : G.Vertex) : ℤ :=
  2 * G.genus v - 2 + G.valence v + G.numMarkings v

lemma logCanonicalDegree_def [Fintype ι] (v : G.Vertex) :
    G.logCanonicalDegree v = 2 * G.genus v - 2 + G.valence v + G.numMarkings v :=
  (rfl)

/-- The log-canonical degrees add up to `2pₐ - 2 + n`. -/
theorem sum_logCanonicalDegree [Fintype ι] :
    ∑ v, G.logCanonicalDegree v = 2 * G.arithmeticGenus - 2 + Fintype.card ι := by
  have hval : (∑ v, G.valence v : ℤ) = 2 * Fintype.card G.Edge := by
    exact_mod_cast G.sum_valence
  have hmark : (∑ v, G.numMarkings v : ℤ) = Fintype.card ι := by
    exact_mod_cast G.sum_numMarkings
  have hgenus : (G.arithmeticGenus + Fintype.card G.Vertex : ℤ) =
      ∑ v, (G.genus v : ℤ) + Fintype.card G.Edge + 1 := by
    exact_mod_cast G.arithmeticGenus_add_card_vertex
  simp only [logCanonicalDegree, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const,
    card_univ, nsmul_eq_mul]
  linarith

/-- The log-canonical degree of the only vertex of a graph is `2pₐ - 2 + n`. -/
theorem logCanonicalDegree_eq_of_forall_eq [Fintype ι] {v : G.Vertex} (h : ∀ w, w = v) :
    G.logCanonicalDegree v = 2 * G.arithmeticGenus - 2 + Fintype.card ι := by
  rw [← G.sum_logCanonicalDegree, Fintype.sum_eq_single v fun w hw ↦ absurd (h w) hw]

/-- A vertex has nonpositive log-canonical degree exactly when it is a rational component with at
most two special points, or a component of genus one with none. -/
theorem logCanonicalDegree_nonpos_iff [Fintype ι] {v : G.Vertex} :
    G.logCanonicalDegree v ≤ 0 ↔
      (G.genus v = 0 ∧ G.valence v + G.numMarkings v ≤ 2) ∨
        (G.genus v = 1 ∧ G.valence v = 0 ∧ G.numMarkings v = 0) := by
  rw [logCanonicalDegree]
  omega

/-- A vertex has negative log-canonical degree exactly when it is a rational component with at
most one special point. -/
theorem logCanonicalDegree_neg_iff [Fintype ι] {v : G.Vertex} :
    G.logCanonicalDegree v < 0 ↔ G.genus v = 0 ∧ G.valence v + G.numMarkings v ≤ 1 := by
  rw [logCanonicalDegree]
  omega

/-- A graph is stable when every vertex has positive log-canonical degree. -/
def IsStable [Fintype ι] : Prop :=
  ∀ v, 0 < G.logCanonicalDegree v

lemma isStable_iff [Fintype ι] : G.IsStable ↔ ∀ v, 0 < G.logCanonicalDegree v :=
  Iff.rfl

/-- A graph is semistable when no vertex has negative log-canonical degree. -/
def IsSemistable [Fintype ι] : Prop :=
  ∀ v, 0 ≤ G.logCanonicalDegree v

lemma isSemistable_iff [Fintype ι] : G.IsSemistable ↔ ∀ v, 0 ≤ G.logCanonicalDegree v :=
  Iff.rfl

variable {G}

lemma IsStable.isSemistable [Fintype ι] (hG : G.IsStable) : G.IsSemistable :=
  fun v ↦ (hG v).le

/-- A stable graph of genus `g` with `n` markings has at most `2g - 2 + n` vertices. -/
theorem IsStable.card_vertex_le [Fintype ι] (hG : G.IsStable) :
    (Fintype.card G.Vertex : ℤ) ≤ 2 * G.arithmeticGenus - 2 + Fintype.card ι := by
  rw [← G.sum_logCanonicalDegree]
  have : ∑ _v : G.Vertex, (1 : ℤ) ≤ ∑ v, G.logCanonicalDegree v :=
    sum_le_sum fun v _ ↦ by have := hG v; omega
  simpa using this

/-- A stable graph of genus `g` with `n` markings has at most `3g - 3 + n` edges. -/
theorem IsStable.card_edge_le [Fintype ι] (hG : G.IsStable) :
    (Fintype.card G.Edge : ℤ) ≤ 3 * G.arithmeticGenus - 3 + Fintype.card ι := by
  have hV := hG.card_vertex_le
  have hgenus : (G.arithmeticGenus + Fintype.card G.Vertex : ℤ) =
      ∑ v, (G.genus v : ℤ) + Fintype.card G.Edge + 1 := by
    exact_mod_cast G.arithmeticGenus_add_card_vertex
  have hpos : (0 : ℤ) ≤ ∑ v, (G.genus v : ℤ) := sum_nonneg fun _ _ ↦ Int.natCast_nonneg _
  linarith

/-- The stable range: a stable graph of genus `g` with `n` markings has `2g - 2 + n > 0`. -/
theorem IsStable.two_mul_arithmeticGenus_sub_two_add_card_pos [Fintype ι] (hG : G.IsStable) :
    0 < 2 * (G.arithmeticGenus : ℤ) - 2 + Fintype.card ι := by
  have := hG.card_vertex_le
  have : 0 < Fintype.card G.Vertex := Fintype.card_pos
  omega

/-! ### Rational tails and rational bridges -/

variable (G)

/-- A rational tail: a rational component meeting the rest of the curve in a single point. -/
def IsRationalTail (v : G.Vertex) : Prop :=
  G.genus v = 0 ∧ G.valence v = 1

lemma isRationalTail_iff {v : G.Vertex} : G.IsRationalTail v ↔ G.genus v = 0 ∧ G.valence v = 1 :=
  Iff.rfl

/-- A rational bridge: a smooth rational component meeting the rest of the curve in exactly two
points, so a rational component of valence two carrying no loop. -/
def IsRationalBridge (v : G.Vertex) : Prop :=
  G.genus v = 0 ∧ G.valence v = 2 ∧ ∀ e, G.endpoint e 0 = v → G.endpoint e 1 ≠ v

lemma isRationalBridge_iff {v : G.Vertex} : G.IsRationalBridge v ↔
    G.genus v = 0 ∧ G.valence v = 2 ∧ ∀ e, G.endpoint e 0 = v → G.endpoint e 1 ≠ v :=
  Iff.rfl

variable {G}

/-- A rational tail has log-canonical degree `-1 + n(v)`. -/
lemma IsRationalTail.logCanonicalDegree_eq [Fintype ι] {v : G.Vertex}
    (hv : G.IsRationalTail v) : G.logCanonicalDegree v = -1 + G.numMarkings v := by
  rw [logCanonicalDegree, hv.1, hv.2]
  omega

/-- A rational bridge has log-canonical degree `n(v)`. -/
lemma IsRationalBridge.logCanonicalDegree_eq [Fintype ι] {v : G.Vertex}
    (hv : G.IsRationalBridge v) : G.logCanonicalDegree v = G.numMarkings v := by
  rw [logCanonicalDegree, hv.1, hv.2.1]
  omega

/-- If a vertex carries no half-edge at all, twice the arithmetic genus is twice its genus. -/
private lemma two_mul_arithmeticGenus_of_valence_eq_zero {v : G.Vertex} (hv : G.valence v = 0) :
    2 * G.arithmeticGenus = 2 * G.genus v := by
  have h : ∀ e, G.endpoint e 0 = v ↔ G.endpoint e 1 = v := fun e ↦
    iff_of_false (G.valence_eq_zero_iff.mp hv e 0) (G.valence_eq_zero_iff.mp hv e 1)
  rw [G.two_mul_arithmeticGenus_of_forall_endpoint_zero_eq_iff h, hv, add_zero]

/-- If a vertex of valence two carries a loop `e`, the loop accounts for both half-edges at the
vertex: an edge has an endpoint there exactly when it is `e`. -/
theorem endpoint_eq_iff_eq_of_valence_eq_two {v : G.Vertex} (hv : G.valence v = 2) {e : G.Edge}
    (he₀ : G.endpoint e 0 = v) (he₁ : G.endpoint e 1 = v) (e' : G.Edge) (i : Fin 2) :
    G.endpoint e' i = v ↔ e' = e := by
  have hsub : ({(e, 0), (e, 1)} : Finset (G.Edge × Fin 2)) ⊆
      univ.filter fun h ↦ G.endpoint h.1 h.2 = v := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> simpa
  have hpair := eq_of_subset_of_card_le hsub (by rw [card_pair (by simp)]; exact hv.le)
  have hmem : (e', i) ∈ univ.filter (fun h : G.Edge × Fin 2 ↦ G.endpoint h.1 h.2 = v) ↔
      G.endpoint e' i = v := by simp
  rw [← hmem, ← hpair]
  fin_cases i <;> simp

/-- A vertex of nonpositive log-canonical degree in a graph with at least one other vertex is a
rational tail with at most one marking or an unmarked rational bridge. -/
theorem isRationalTail_or_isRationalBridge_of_logCanonicalDegree_nonpos [Fintype ι] {v : G.Vertex}
    (hv : G.logCanonicalDegree v ≤ 0) (hw : ∃ w, w ≠ v) :
    (G.IsRationalTail v ∧ G.numMarkings v ≤ 1) ∨
      (G.IsRationalBridge v ∧ ∀ i, G.marking i ≠ v) := by
  -- If every edge at `v` were a loop, `v` would be the only vertex.
  have hsingle : ¬ ∀ e, G.endpoint e 0 = v ↔ G.endpoint e 1 = v := fun h ↦
    have ⟨w, hw⟩ := hw
    hw (G.eq_of_forall_endpoint_zero_eq_iff h w)
  have hval₀ : G.valence v ≠ 0 := fun h ↦ hsingle fun e ↦
    iff_of_false (G.valence_eq_zero_iff.mp h e 0) (G.valence_eq_zero_iff.mp h e 1)
  rcases G.logCanonicalDegree_nonpos_iff.mp hv with ⟨hg, hval⟩ | ⟨-, hval, -⟩
  · have : G.valence v ≤ 2 := by omega
    interval_cases h : G.valence v
    · exact absurd rfl hval₀
    · exact .inl ⟨G.isRationalTail_iff.mpr ⟨hg, h⟩, by omega⟩
    · have hm : ∀ i, G.marking i ≠ v := by
        have : G.numMarkings v = 0 := by omega
        simpa [numMarkings_def, filter_eq_empty_iff] using this
      by_cases hloop : ∃ e, G.endpoint e 0 = v ∧ G.endpoint e 1 = v
      · obtain ⟨e, he₀, he₁⟩ := hloop
        have := endpoint_eq_iff_eq_of_valence_eq_two h he₀ he₁
        exact absurd (fun e' ↦ by rw [this, this]) hsingle
      · simp only [not_exists, not_and] at hloop
        exact .inr ⟨G.isRationalBridge_iff.mpr ⟨hg, h, hloop⟩, hm⟩
  · exact absurd hval hval₀

/-- If a vertex of valence two carries a loop, that loop is the only edge, and twice the
arithmetic genus is `2 g(v) + 2`. -/
private lemma two_mul_arithmeticGenus_of_valence_eq_two_of_loop {v : G.Vertex}
    (hv : G.valence v = 2) {e : G.Edge} (he₀ : G.endpoint e 0 = v) (he₁ : G.endpoint e 1 = v) :
    2 * G.arithmeticGenus = 2 * G.genus v + 2 := by
  have hloop := endpoint_eq_iff_eq_of_valence_eq_two hv he₀ he₁
  rw [G.two_mul_arithmeticGenus_of_forall_endpoint_zero_eq_iff fun e' ↦ by rw [hloop, hloop], hv]

/-- An unmarked graph of arithmetic genus at least one is semistable exactly when it has no
rational tails. -/
theorem isSemistable_iff_forall_not_isRationalTail [Fintype ι] [IsEmpty ι]
    (hg : 1 ≤ G.arithmeticGenus) : G.IsSemistable ↔ ∀ v, ¬ G.IsRationalTail v := by
  refine ⟨fun hG v hv ↦ ?_, fun hG v ↦ ?_⟩
  · have := hG v
    rw [hv.logCanonicalDegree_eq, numMarkings_of_isEmpty] at this
    omega
  · by_contra hneg
    obtain ⟨hgv, hval⟩ := G.logCanonicalDegree_neg_iff.mp (not_le.mp hneg)
    rw [numMarkings_of_isEmpty, add_zero] at hval
    obtain hval | hval := Nat.le_one_iff_eq_zero_or_eq_one.mp hval
    · have := two_mul_arithmeticGenus_of_valence_eq_zero hval
      omega
    · exact hG v ⟨hgv, hval⟩

/-- An unmarked graph of arithmetic genus at least two is stable exactly when it has neither
rational tails nor rational bridges. -/
theorem isStable_iff_forall_not_isRationalTail_and_not_isRationalBridge [Fintype ι] [IsEmpty ι]
    (hg : 2 ≤ G.arithmeticGenus) :
    G.IsStable ↔ ∀ v, ¬ G.IsRationalTail v ∧ ¬ G.IsRationalBridge v := by
  refine ⟨fun hG v ↦ ⟨fun hv ↦ ?_, fun hv ↦ ?_⟩, fun hG v ↦ ?_⟩
  · have := hG v
    rw [hv.logCanonicalDegree_eq, numMarkings_of_isEmpty] at this
    omega
  · have := hG v
    rw [hv.logCanonicalDegree_eq, numMarkings_of_isEmpty] at this
    omega
  · by_contra hnonpos
    rcases G.logCanonicalDegree_nonpos_iff.mp (not_lt.mp hnonpos) with ⟨hgv, hval⟩ | ⟨hgv, hval, -⟩
    · rw [numMarkings_of_isEmpty, add_zero] at hval
      interval_cases h : G.valence v
      · have := two_mul_arithmeticGenus_of_valence_eq_zero h
        omega
      · exact (hG v).1 ⟨hgv, h⟩
      · by_cases hloop : ∃ e, G.endpoint e 0 = v ∧ G.endpoint e 1 = v
        · obtain ⟨e, he₀, he₁⟩ := hloop
          have := two_mul_arithmeticGenus_of_valence_eq_two_of_loop h he₀ he₁
          omega
        · exact (hG v).2 ⟨hgv, h, fun e he₀ he₁ ↦ hloop ⟨e, he₀, he₁⟩⟩
    · have := two_mul_arithmeticGenus_of_valence_eq_zero hval
      omega

end DualGraph

end TauCeti
