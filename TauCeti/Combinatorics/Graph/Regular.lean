/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Bipartition
public import TauCeti.Combinatorics.Graph.LineGraph

/-!
# Regular multigraphs and regular bipartite completions

A multigraph `G : Graph α β` is `k`-regular when every actual vertex is incident with exactly `k`
actual edges. Edges are counted by identity, so parallel edges count separately and a loop counts
once; on `Graph.ofSimpleGraph H` this is Mathlib's `SimpleGraph.IsRegularOfDegree`.

Every finite bipartite multigraph whose degrees are at most `k` embeds in a finite `k`-regular
bipartite multigraph. A *regular completion* records such an embedding on the ambient types
`α ⊕ ℕ` and `β ⊕ ℕ`: `Sum.inl` keeps the original vertex and edge identities, with the same links
and sides, and `Sum.inr` supplies the additional vertices and edges. Deleting the added edges and
vertices recovers `G`, even where an added edge joins two original vertices, so a proper
edge-colouring of the completion restricts to one of `G`. Through a completion, results about
regular bipartite multigraphs, such as their decomposition into perfect matchings, apply to
bipartite multigraphs of bounded degree; this is the classical route to Kőnig's edge-colouring
theorem.

The completion is constructed by adding isolated vertices to the smaller side until both sides have
the same size, so that both sides have the same total degree deficit, and then joining the
deficits of the two sides in pairs by new edges. These edges may be parallel to each other or to
original edges.

## Main definitions

* `Graph.IsRegularOfDegree G k`: every actual vertex of `G` has exactly `k` incident edges.
* `Graph.IsRegularCompletion G L R k G' L' R'`: the finite `k`-regular multigraph `G'` with
  bipartition `(L', R')` extends `G` with bipartition `(L, R)` along `Sum.inl`.
* `Graph.IsRegularCompletion.isoRestrict`: `G` is isomorphic to the subgraph of `G'` on its original
  vertices and edges.
* `Graph.IsRegularCompletion.restrictEdgeColoring`: a proper edge-colouring of `G'` restricts to
  one of `G`.

## Main results

* `Graph.isRegularOfDegree_iff_incidenceCount_eq`: with finitely many edges, regularity is a
  condition on incidence counts.
* `Graph.isRegularOfDegree_ofSimpleGraph_iff`: regularity agrees with Mathlib's for simple graphs.
* `Graph.IsBipartition.exists_isRegularCompletion`: a finite bipartite multigraph whose degrees are
  at most `k` has a `k`-regular bipartite completion.

## References

* D. Kőnig, *Gráfok és alkalmazásuk a determinánsok és a halmazok elméletére*, Mat. Természettud.
  Értesítő 34 (1916), 104--119.
-/

public section

open Finset
open scoped Graph

universe u v w

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β} {k : ℕ}

/-! ### Regular multigraphs -/

variable (G) in
/-- A multigraph is `k`-regular when every actual vertex is incident with exactly `k` actual edges.
Edges are counted by identity: parallel edges count separately and a loop counts once. -/
def IsRegularOfDegree (k : ℕ) : Prop :=
  ∀ x ∈ V(G), (G.incidenceSet x).encard = k

theorem isRegularOfDegree_def :
    G.IsRegularOfDegree k ↔ ∀ x ∈ V(G), (G.incidenceSet x).encard = k :=
  Iff.rfl

/-- In a `k`-regular multigraph, every actual vertex has incidence count `k`. -/
theorem IsRegularOfDegree.incidenceCount_eq (h : G.IsRegularOfDegree k) {x : α}
    (hx : x ∈ V(G)) : G.incidenceCount x = k := by
  rw [incidenceCount_def, Set.ncard_def, isRegularOfDegree_def.1 h x hx, ENat.toNat_natCast]

/-- With finitely many edges, a multigraph is `k`-regular exactly when every actual vertex has
incidence count `k`. -/
theorem isRegularOfDegree_iff_incidenceCount_eq [Finite E(G)] :
    G.IsRegularOfDegree k ↔ ∀ x ∈ V(G), G.incidenceCount x = k := by
  refine ⟨fun h _ hx ↦ h.incidenceCount_eq hx, fun h ↦ isRegularOfDegree_def.2 fun x hx ↦ ?_⟩
  rw [← (G.finite_incidenceSet x).cast_ncard_eq, ← incidenceCount_def, h x hx]

/-- The multigraph of a locally finite simple graph is `k`-regular exactly when the simple graph
is. -/
theorem isRegularOfDegree_ofSimpleGraph_iff {H : SimpleGraph α} [H.LocallyFinite] :
    (ofSimpleGraph H).IsRegularOfDegree k ↔ H.IsRegularOfDegree k := by
  rw [isRegularOfDegree_def]
  refine forall_congr' fun x ↦ ?_
  rw [vertexSet_ofSimpleGraph, incidenceSet_ofSimpleGraph,
    ← (Set.toFinite (H.incidenceSet x)).cast_ncard_eq, SimpleGraph.ncard_incidenceSet]
  simp

/-! ### Regular bipartite completions -/

variable {L R : Finset V(G)} {G' : Graph (α ⊕ ℕ) (β ⊕ ℕ)} {L' R' : Finset V(G')}

variable (G) in
/-- `G'` with bipartition `(L', R')` is a `k`-regular bipartite completion of `G` with
bipartition `(L, R)`: `G'` is a `k`-regular multigraph with finitely many edges, and along
`Sum.inl` it has the actual vertices, actual edges, links and sides of `G`. The vertices and edges
in the range of `Sum.inr` are additional; an additional edge may join two original vertices. -/
structure IsRegularCompletion (L R : Finset V(G)) (k : ℕ) (G' : Graph (α ⊕ ℕ) (β ⊕ ℕ))
    (L' R' : Finset V(G')) : Prop where
  isBipartition : G'.IsBipartition L' R'
  finite_edgeSet : E(G').Finite
  isRegularOfDegree : G'.IsRegularOfDegree k
  inl_mem_vertexSet_iff (x : α) : .inl x ∈ V(G') ↔ x ∈ V(G)
  inl_mem_edgeSet_iff (e : β) : .inl e ∈ E(G') ↔ e ∈ E(G)
  isLink_inl_inl_iff (e : β) (x y : α) : G'.IsLink (.inl e) (.inl x) (.inl y) ↔ G.IsLink e x y
  inl_mem_left_iff {x : α} (hx : x ∈ V(G)) (hx' : .inl x ∈ V(G')) :
    (⟨.inl x, hx'⟩ : V(G')) ∈ L' ↔ ⟨x, hx⟩ ∈ L
  inl_mem_right_iff {x : α} (hx : x ∈ V(G)) (hx' : .inl x ∈ V(G')) :
    (⟨.inl x, hx'⟩ : V(G')) ∈ R' ↔ ⟨x, hx⟩ ∈ R

namespace IsRegularCompletion

variable (hC : G.IsRegularCompletion L R k G' L' R')
include hC

/-- The ends of an original edge in the completion are its original ends. -/
theorem isLink_inl_iff {e : β} {u w : α ⊕ ℕ} :
    G'.IsLink (.inl e) u w ↔ ∃ x y, G.IsLink e x y ∧ u = .inl x ∧ w = .inl y := by
  refine ⟨fun h ↦ ?_, fun ⟨x, y, h, hu, hw⟩ ↦ hu ▸ hw ▸ (hC.isLink_inl_inl_iff e x y).2 h⟩
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet ((hC.inl_mem_edgeSet_iff e).1 h.edge_mem)
  rcases ((hC.isLink_inl_inl_iff e x y).2 hxy).eq_and_eq_or_eq_and_eq h with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [⟨x, y, hxy, rfl, rfl⟩, ⟨y, x, hxy.symm, rfl, rfl⟩]

/-- An original edge is incident with an original vertex in the completion exactly when it is in
`G`. -/
theorem inc_inl_inl_iff {e : β} {x : α} : G'.Inc (.inl e) (.inl x) ↔ G.Inc e x := by
  refine ⟨fun ⟨_, h⟩ ↦ ?_, fun ⟨y, h⟩ ↦ ⟨.inl y, (hC.isLink_inl_inl_iff e x y).2 h⟩⟩
  obtain ⟨x', y, h, hx, -⟩ := hC.isLink_inl_iff.1 h
  exact ⟨y, Sum.inl_injective hx ▸ h⟩

/-- The original edges at an original vertex of the completion are the edges of `G` at that
vertex. -/
theorem image_inl_incidenceSet (x : α) :
    Sum.inl '' G.incidenceSet x = G'.incidenceSet (.inl x) ∩ Set.range Sum.inl := by
  ext e
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨hC.inc_inl_inl_iff.2 he, e, rfl⟩
  · rintro ⟨he, e, rfl⟩
    exact ⟨e, hC.inc_inl_inl_iff.1 he, rfl⟩

/-- The original edges of the completion are the images of the edges of `G`. -/
theorem edgeSet_restrict_induce :
    E((G'.restrict (Set.range Sum.inl)).induce (Sum.inl '' V(G))) = Sum.inl '' E(G) := by
  ext e
  simp only [edgeSet_induce, Set.mem_ofPred_eq, restrict_isLink, Set.mem_image]
  constructor
  · rintro ⟨u, w, ⟨⟨e, rfl⟩, h⟩, -, -⟩
    obtain ⟨x, y, h, -, -⟩ := hC.isLink_inl_iff.1 h
    exact ⟨e, h.edge_mem, rfl⟩
  · rintro ⟨e, he, rfl⟩
    obtain ⟨x, y, h⟩ := G.exists_isLink_of_mem_edgeSet he
    exact ⟨.inl x, .inl y, ⟨⟨e, rfl⟩, (hC.isLink_inl_inl_iff e x y).2 h⟩, ⟨x, h.left_mem, rfl⟩,
      ⟨y, h.right_mem, rfl⟩⟩

/-- Deleting the additional edges and then the additional vertices of a regular completion
recovers `G`: the isomorphism acts by `Sum.inl` on vertices and edges. -/
noncomputable def isoRestrict :
    G.Iso ((G'.restrict (Set.range Sum.inl)).induce (Sum.inl '' V(G))) where
  vertexEquiv := (Equiv.Set.image Sum.inl V(G) Sum.inl_injective).trans
    (Set.equivOfEq (vertexSet_induce _ _).symm)
  edgeEquiv := (Equiv.Set.image Sum.inl E(G) Sum.inl_injective).trans
    (Set.equivOfEq hC.edgeSet_restrict_induce.symm)
  map_isLink_iff e x y := by
    simp only [Equiv.trans_apply, Set.equivOfEq_apply, Equiv.Set.image_apply, induce_isLink,
      restrict_isLink, Set.mem_range, exists_apply_eq_apply, true_and, hC.isLink_inl_inl_iff]
    exact and_iff_left ⟨Set.mem_image_of_mem _ x.2, Set.mem_image_of_mem _ y.2⟩

/-- The isomorphism `isoRestrict` sends a vertex `x` to `Sum.inl x`. -/
@[simp]
theorem coe_isoRestrict_vertexEquiv (x : V(G)) :
    (hC.isoRestrict.vertexEquiv x : α ⊕ ℕ) = .inl x :=
  (rfl)

/-- The isomorphism `isoRestrict` sends an edge `e` to `Sum.inl e`. -/
@[simp]
theorem coe_isoRestrict_edgeEquiv (e : E(G)) : (hC.isoRestrict.edgeEquiv e : β ⊕ ℕ) = .inl e :=
  (rfl)

/-- The original vertices and edges of a regular completion form a subgraph of it. -/
theorem restrict_induce_le : (G'.restrict (Set.range Sum.inl)).induce (Sum.inl '' V(G)) ≤ G' :=
  (induce_le (by rintro _ ⟨x, hx, rfl⟩; exact (hC.inl_mem_vertexSet_iff x).2 hx)).trans
    restrict_le

/-- The restriction to `G` of a proper edge-colouring of a regular completion: the colour of an
edge `e` of `G` is that of `Sum.inl e`. -/
noncomputable def restrictEdgeColoring {C : Type w} (c : G'.EdgeColoring C) : G.EdgeColoring C :=
  (c.ofLE hC.restrict_induce_le).comp hC.isoRestrict.lineGraph.toHom

/-- The restricted edge-colouring gives an edge `e` of `G` the colour of `Sum.inl e`. -/
@[simp]
theorem restrictEdgeColoring_apply {C : Type w} (c : G'.EdgeColoring C) (e : E(G)) :
    hC.restrictEdgeColoring c e = c ⟨.inl e, (hC.inl_mem_edgeSet_iff e).2 e.2⟩ := by
  simp [restrictEdgeColoring, Set.inclusion]

end IsRegularCompletion

/-! ### Construction of a regular completion -/

section Construction

/-- The multigraph on `α ⊕ ℕ` with edges `β ⊕ ℕ` consisting of a copy of `G` along `Sum.inl`,
the extra vertices `X`, and for each `i : Fin n` an edge `Sum.inr i` with ends `ends i`. -/
private def extend (G : Graph α β) (X : Set (α ⊕ ℕ)) {n : ℕ} (ends : Fin n → Sym2 (α ⊕ ℕ)) :
    Graph (α ⊕ ℕ) (β ⊕ ℕ) where
  vertexSet := Sum.inl '' V(G) ∪ X ∪ {z | ∃ i, z ∈ ends i}
  IsLink e u w := match e with
    | .inl e => ∃ x y, G.IsLink e x y ∧ u = .inl x ∧ w = .inl y
    | .inr i => ∃ h : i < n, s(u, w) = ends ⟨i, h⟩
  isLink_symm e _ := ⟨fun u w h ↦ by
    cases e with
    | inl e =>
      obtain ⟨x, y, h, rfl, rfl⟩ := h
      exact ⟨y, x, h.symm, rfl, rfl⟩
    | inr i =>
      obtain ⟨hi, h⟩ := h
      exact ⟨hi, Sym2.eq_swap.trans h⟩⟩
  eq_or_eq_of_isLink_of_isLink e u w u' w' h h' := by
    cases e with
    | inl e =>
      obtain ⟨x, y, h, rfl, rfl⟩ := h
      obtain ⟨x', y', h', rfl, rfl⟩ := h'
      simpa using h.left_eq_or_eq h'
    | inr i =>
      obtain ⟨hi, h⟩ := h
      obtain ⟨hi', h'⟩ := h'
      have hu : u ∈ ends ⟨i, hi⟩ := h ▸ Sym2.mem_mk_left u w
      rw [← h'] at hu
      exact Sym2.mem_iff.1 hu
  left_mem_of_isLink e u w h := by
    cases e with
    | inl e =>
      obtain ⟨x, y, h, rfl, rfl⟩ := h
      exact .inl (.inl ⟨x, h.left_mem, rfl⟩)
    | inr i =>
      obtain ⟨hi, h⟩ := h
      exact .inr ⟨⟨i, hi⟩, h ▸ Sym2.mem_mk_left u w⟩

variable {X : Set (α ⊕ ℕ)} {n : ℕ} {ends : Fin n → Sym2 (α ⊕ ℕ)}

private theorem mem_vertexSet_extend {z : α ⊕ ℕ} :
    z ∈ V(extend G X ends) ↔ z ∈ Sum.inl '' V(G) ∨ z ∈ X ∨ ∃ i, z ∈ ends i := by
  rw [← or_assoc]
  exact Iff.rfl

private theorem extend_isLink_inl {e : β} {u w : α ⊕ ℕ} :
    (extend G X ends).IsLink (.inl e) u w ↔ ∃ x y, G.IsLink e x y ∧ u = .inl x ∧ w = .inl y :=
  Iff.rfl

private theorem extend_isLink_inr {i : ℕ} {u w : α ⊕ ℕ} :
    (extend G X ends).IsLink (.inr i) u w ↔ ∃ h : i < n, s(u, w) = ends ⟨i, h⟩ :=
  Iff.rfl

private theorem edgeSet_extend :
    E(extend G X ends) = Sum.inl '' E(G) ∪ Set.range fun i : Fin n ↦ (.inr i : β ⊕ ℕ) := by
  ext e
  rw [edge_mem_iff_exists_isLink]
  cases e with
  | inl e =>
    simp only [extend_isLink_inl, Set.mem_union, Set.mem_image, Sum.inl.injEq, exists_eq_right,
      Set.mem_range, reduceCtorEq, exists_false, or_false, G.edge_mem_iff_exists_isLink]
    exact ⟨fun ⟨_, _, x, y, h, _⟩ ↦ ⟨x, y, h⟩, fun ⟨x, y, h⟩ ↦ ⟨_, _, x, y, h, rfl, rfl⟩⟩
  | inr i =>
    simp only [extend_isLink_inr, Set.mem_union, Set.mem_image, reduceCtorEq, and_false,
      exists_false, Set.mem_range, Sum.inr.injEq, false_or]
    refine ⟨fun ⟨_, _, hi, _⟩ ↦ ⟨⟨i, hi⟩, rfl⟩, ?_⟩
    rintro ⟨i, rfl⟩
    induction h : ends i using Sym2.ind with
    | _ u w => exact ⟨u, w, i.2, h.symm⟩

private theorem extend_inc_inr {i : ℕ} {z : α ⊕ ℕ} :
    (extend G X ends).Inc (.inr i) z ↔ ∃ h : i < n, z ∈ ends ⟨i, h⟩ := by
  simp only [Inc, extend_isLink_inr, Sym2.mem_iff_exists]
  exact ⟨fun ⟨w, hi, h⟩ ↦ ⟨hi, w, h.symm⟩, fun ⟨hi, w, h⟩ ↦ ⟨w, hi, h.symm⟩⟩

/-- The edges at a vertex of `extend G X ends` are the edges of `G` at it, if it is original,
together with the new edges having it as an end. -/
private theorem encard_incidenceSet_extend [DecidableEq α] (z : α ⊕ ℕ) :
    ((extend G X ends).incidenceSet z).encard =
      {e | ∃ x, G.Inc e x ∧ z = .inl x}.encard + #{i | z ∈ ends i} := by
  have hset : (extend G X ends).incidenceSet z =
      Sum.inl '' {e | ∃ x, G.Inc e x ∧ z = .inl x} ∪
        (fun i : Fin n ↦ (.inr i : β ⊕ ℕ)) '' ({i | z ∈ ends i} : Finset (Fin n)) := by
    ext e
    cases e with
    | inl e =>
      simp only [mem_incidenceSet, Inc, extend_isLink_inl, Set.mem_union, Set.mem_image,
        Set.mem_ofPred_eq, Sum.inl.injEq, exists_eq_right, reduceCtorEq, and_false, exists_false,
        or_false]
      exact ⟨fun ⟨_, x, y, h, hz, _⟩ ↦ ⟨x, ⟨y, h⟩, hz⟩, fun ⟨x, ⟨y, h⟩, hz⟩ ↦ ⟨_, x, y, h, hz, rfl⟩⟩
    | inr i =>
      simp only [mem_incidenceSet, extend_inc_inr, Set.mem_union, Set.mem_image, reduceCtorEq,
        and_false, exists_false, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq,
        Sum.inr.injEq, false_or]
      exact ⟨fun ⟨hi, h⟩ ↦ ⟨⟨i, hi⟩, h, rfl⟩, fun ⟨i, h, hi⟩ ↦ ⟨hi ▸ i.2, by simpa [← hi] using h⟩⟩
  rw [hset, Set.encard_union_eq, Sum.inl_injective.encard_image,
    Function.Injective.encard_image fun i j h ↦ Fin.ext (Sum.inr_injective h),
    Set.encard_coe_eq_coe_finsetCard]
  rw [Set.disjoint_left]
  rintro _ ⟨_, -, rfl⟩ ⟨_, -, h⟩
  exact Sum.inr_ne_inl h

/-- The number of vertices added to the side `S` to bring it up to the size of `T`. -/
private def padding (S T : Finset V(G)) : ℕ := max #S #T - #S

/-- The vertices of one side of the completion: the vertices of `S`, followed by `pad` new
vertices `Sum.inr (2 * i + p)`. -/
private def sideVertex (S : Finset V(G)) (pad p : ℕ) : S ⊕ Fin pad → α ⊕ ℕ :=
  Sum.elim (fun x ↦ .inl x.1.1) fun i ↦ .inr (2 * i + p)

/-- The degree in `G` of a vertex of one side of the completion; new vertices have degree zero. -/
private noncomputable def sideDegree (S : Finset V(G)) (pad : ℕ) : S ⊕ Fin pad → ℕ :=
  Sum.elim (fun x ↦ G.incidenceCount x.1.1) 0

private theorem sideVertex_injective (S : Finset V(G)) (pad p : ℕ) :
    (sideVertex S pad p).Injective :=
  Function.Injective.sumElim (fun _ _ h ↦ Subtype.ext (Subtype.ext (Sum.inl_injective h)))
    (fun i j h ↦ Fin.ext (by have := Sum.inr_injective h; omega)) fun _ _ ↦ Sum.inl_ne_inr

private theorem sideVertex_eq_inl_iff {S : Finset V(G)} {pad p : ℕ} {v : S ⊕ Fin pad} {x : α} :
    sideVertex S pad p v = .inl x ↔
      ∃ (hx : x ∈ V(G)) (hS : ⟨x, hx⟩ ∈ S), v = .inl ⟨⟨x, hx⟩, hS⟩ := by
  cases v with
  | inl y =>
    obtain ⟨⟨y, hy⟩, hyS⟩ := y
    simp only [sideVertex, Sum.elim_inl, Sum.inl.injEq]
    exact ⟨fun h ↦ h ▸ ⟨hy, hyS, rfl⟩, fun ⟨_, _, h⟩ ↦ by cases h; rfl⟩
  | inr i => simp [sideVertex]

private theorem sideVertex_ne (hLR : Disjoint L R) {pl pr : ℕ} (v : L ⊕ Fin pl)
    (w : R ⊕ Fin pr) : sideVertex L pl 0 v ≠ sideVertex R pr 1 w := by
  cases v with
  | inl x =>
    cases w with
    | inl y =>
      intro h
      have hxy : x.1 = y.1 := Subtype.ext (Sum.inl_injective h)
      exact disjoint_left.1 hLR x.2 (hxy ▸ y.2)
    | inr j => exact Sum.inl_ne_inr
  | inr i =>
    cases w with
    | inl y => exact Sum.inr_ne_inl
    | inr j =>
      intro h
      have := Sum.inr_injective h
      omega

/-- The original edges at a vertex of one side form the incidence set of that vertex in `G`, or
are absent at a new vertex. -/
private theorem encard_inc_sideVertex [Finite E(G)] (S : Finset V(G)) (pad p : ℕ)
    (v : S ⊕ Fin pad) :
    {e | ∃ x, G.Inc e x ∧ sideVertex S pad p v = .inl x}.encard = sideDegree S pad v := by
  cases v with
  | inl x =>
    simp only [sideVertex, Sum.elim_inl, Sum.inl.injEq, sideDegree, exists_eq_right']
    rw [show {e | G.Inc e x.1.1} = G.incidenceSet x.1.1 by ext; simp, incidenceCount_def,
      (G.finite_incidenceSet _).cast_ncard_eq]
  | inr i => simp [sideVertex, sideDegree]

/-- Together, the degree deficits of the vertices of a padded side and the degrees of its original
vertices fill `k` slots at each vertex. -/
private theorem sum_sub_sideDegree_add (S : Finset V(G)) (pad : ℕ)
    (hk : ∀ x ∈ S, G.incidenceCount x.1 ≤ k) :
    ∑ v, (k - sideDegree S pad v) + ∑ x ∈ S, G.incidenceCount x.1 = k * (#S + pad) := by
  have hS : ∑ x ∈ S, (k - G.incidenceCount x.1) + ∑ x ∈ S, G.incidenceCount x.1 = #S * k := by
    rw [← sum_add_distrib, sum_congr rfl fun x hx ↦ tsub_add_cancel_of_le (hk x hx), sum_const,
      smul_eq_mul]
  rw [Fintype.sum_sum_type]
  simp only [sideDegree, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, tsub_zero, sum_const,
    card_univ, Fintype.card_fin, smul_eq_mul]
  rw [sum_coe_sort S fun x ↦ k - G.incidenceCount x.1, add_right_comm, hS, ← add_mul, mul_comm]

variable {pl pr : ℕ} (fl : Fin n → L ⊕ Fin pl) (fr : Fin n → R ⊕ Fin pr)

/-- The completion: `G`, the padding vertices of both sides, and for each `i : Fin n` an edge
joining the vertex `fl i` of the left side to the vertex `fr i` of the right side. -/
private def stubGraph : Graph (α ⊕ ℕ) (β ⊕ ℕ) :=
  extend G (Set.range (sideVertex L pl 0 ∘ Sum.inr) ∪ Set.range (sideVertex R pr 1 ∘ Sum.inr))
    fun i ↦ s(sideVertex L pl 0 (fl i), sideVertex R pr 1 (fr i))

private theorem sideVertex_left_mem (v : L ⊕ Fin pl) :
    sideVertex L pl 0 v ∈ V(stubGraph fl fr) := by
  rw [stubGraph, mem_vertexSet_extend]
  cases v with
  | inl x => exact .inl ⟨x.1.1, x.1.2, rfl⟩
  | inr i => exact .inr (.inl (.inl ⟨i, rfl⟩))

private theorem sideVertex_right_mem (w : R ⊕ Fin pr) :
    sideVertex R pr 1 w ∈ V(stubGraph fl fr) := by
  rw [stubGraph, mem_vertexSet_extend]
  cases w with
  | inl x => exact .inl ⟨x.1.1, x.1.2, rfl⟩
  | inr i => exact .inr (.inl (.inr ⟨i, rfl⟩))

private theorem mem_vertexSet_stubGraph (h : G.IsBipartition L R) {z : α ⊕ ℕ} :
    z ∈ V(stubGraph fl fr) ↔ (∃ v, sideVertex L pl 0 v = z) ∨ ∃ w, sideVertex R pr 1 w = z := by
  refine ⟨fun hz ↦ ?_, ?_⟩
  · rw [stubGraph, mem_vertexSet_extend, Set.mem_union] at hz
    rcases hz with ⟨x, hx, rfl⟩ | (⟨v, rfl⟩ | ⟨w, rfl⟩) | ⟨i, hz⟩
    · rcases h.mem_or_mem ⟨x, hx⟩ with hxL | hxR
      exacts [.inl ⟨.inl ⟨_, hxL⟩, rfl⟩, .inr ⟨.inl ⟨_, hxR⟩, rfl⟩]
    · exact .inl ⟨_, rfl⟩
    · exact .inr ⟨_, rfl⟩
    · rcases Sym2.mem_iff.1 hz with rfl | rfl
      exacts [.inl ⟨_, rfl⟩, .inr ⟨_, rfl⟩]
  · rintro (⟨v, rfl⟩ | ⟨w, rfl⟩)
    exacts [sideVertex_left_mem fl fr v, sideVertex_right_mem fl fr w]

private theorem encard_incidenceSet_left [Finite E(G)] [DecidableEq α] (hLR : Disjoint L R)
    (v : L ⊕ Fin pl) :
    ((stubGraph fl fr).incidenceSet (sideVertex L pl 0 v)).encard =
      sideDegree L pl v + #{i | fl i = v} := by
  rw [stubGraph, encard_incidenceSet_extend, encard_inc_sideVertex]
  congr 3
  ext i
  simp only [Sym2.mem_iff, (sideVertex_injective L pl 0).eq_iff, sideVertex_ne hLR, or_false,
    eq_comm]

private theorem encard_incidenceSet_right [Finite E(G)] [DecidableEq α] (hLR : Disjoint L R)
    (w : R ⊕ Fin pr) :
    ((stubGraph fl fr).incidenceSet (sideVertex R pr 1 w)).encard =
      sideDegree R pr w + #{i | fr i = w} := by
  rw [stubGraph, encard_incidenceSet_extend, encard_inc_sideVertex]
  congr 3
  ext i
  simp only [Sym2.mem_iff, (sideVertex_injective R pr 1).eq_iff, (sideVertex_ne hLR _ _).symm,
    false_or, eq_comm]

/-- The left side of the completion. -/
private def stubLeft : Finset V(stubGraph fl fr) :=
  univ.map ⟨fun v ↦ ⟨sideVertex L pl 0 v, sideVertex_left_mem fl fr v⟩,
    fun _ _ h ↦ sideVertex_injective L pl 0 (congrArg Subtype.val h)⟩

/-- The right side of the completion. -/
private def stubRight : Finset V(stubGraph fl fr) :=
  univ.map ⟨fun w ↦ ⟨sideVertex R pr 1 w, sideVertex_right_mem fl fr w⟩,
    fun _ _ h ↦ sideVertex_injective R pr 1 (congrArg Subtype.val h)⟩

private theorem mem_stubLeft {z : V(stubGraph fl fr)} :
    z ∈ stubLeft fl fr ↔ ∃ v, sideVertex L pl 0 v = z := by
  simp only [stubLeft, mem_map, mem_univ, true_and]
  exact exists_congr fun _ ↦ Subtype.ext_iff

private theorem mem_stubRight {z : V(stubGraph fl fr)} :
    z ∈ stubRight fl fr ↔ ∃ w, sideVertex R pr 1 w = z := by
  simp only [stubRight, mem_map, mem_univ, true_and]
  exact exists_congr fun _ ↦ Subtype.ext_iff

private theorem isBipartition_stubGraph (h : G.IsBipartition L R) :
    (stubGraph fl fr).IsBipartition (stubLeft fl fr) (stubRight fl fr) where
  disjoint := disjoint_left.2 fun z hzL hzR ↦ by
    obtain ⟨v, hv⟩ := (mem_stubLeft fl fr).1 hzL
    obtain ⟨w, hw⟩ := (mem_stubRight fl fr).1 hzR
    exact sideVertex_ne h.disjoint v w (hv.trans hw.symm)
  mem_or_mem z := by
    rw [mem_stubLeft, mem_stubRight]
    exact (mem_vertexSet_stubGraph fl fr h).1 z.2
  isLink {e z z'} hzz' := by
    simp only [mem_stubLeft, mem_stubRight]
    cases e with
    | inl e =>
      obtain ⟨x, y, hxy, hz, hz'⟩ := extend_isLink_inl.1 hzz'
      rw [hz, hz']
      rcases h.isLink (x := ⟨x, hxy.left_mem⟩) (y := ⟨y, hxy.right_mem⟩) hxy with
        ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact .inl ⟨⟨.inl ⟨_, hx⟩, rfl⟩, ⟨.inl ⟨_, hy⟩, rfl⟩⟩
      · exact .inr ⟨⟨.inl ⟨_, hx⟩, rfl⟩, ⟨.inl ⟨_, hy⟩, rfl⟩⟩
    | inr i =>
      obtain ⟨hi, hzz'⟩ := extend_isLink_inr.1 hzz'
      rcases Sym2.eq_iff.1 hzz' with ⟨hz, hz'⟩ | ⟨hz, hz'⟩
      · exact .inl ⟨⟨_, hz.symm⟩, ⟨_, hz'.symm⟩⟩
      · exact .inr ⟨⟨_, hz.symm⟩, ⟨_, hz'.symm⟩⟩

private theorem exists_sideVertex_eq_inl_iff {S : Finset V(G)} {pad p : ℕ} {x : α}
    (hx : x ∈ V(G)) : (∃ v, sideVertex S pad p v = .inl x) ↔ ⟨x, hx⟩ ∈ S := by
  simp only [sideVertex_eq_inl_iff]
  exact ⟨fun ⟨_, _, hS, _⟩ ↦ hS, fun hS ↦ ⟨_, hx, hS, rfl⟩⟩

/-- `stubGraph` is a `k`-regular completion as soon as each vertex `v` of either side is the end
of exactly `k - sideDegree v` new edges. -/
private theorem isRegularCompletion_stubGraph [Finite E(G)] [DecidableEq α]
    (h : G.IsBipartition L R) (hk : ∀ x ∈ V(G), G.incidenceCount x ≤ k)
    (hfl : ∀ v, #{i | fl i = v} = k - sideDegree L pl v)
    (hfr : ∀ w, #{i | fr i = w} = k - sideDegree R pr w) :
    G.IsRegularCompletion L R k (stubGraph fl fr) (stubLeft fl fr) (stubRight fl fr) where
  isBipartition := isBipartition_stubGraph fl fr h
  finite_edgeSet := by
    rw [stubGraph, edgeSet_extend]
    exact ((Set.toFinite E(G)).image _).union (Set.finite_range _)
  isRegularOfDegree z hz := by
    have hdeg {S : Finset V(G)} {pad : ℕ} (v : S ⊕ Fin pad) : sideDegree S pad v ≤ k := by
      cases v with
      | inl x => exact hk _ x.1.2
      | inr i => exact Nat.zero_le k
    rcases (mem_vertexSet_stubGraph fl fr h).1 hz with ⟨v, rfl⟩ | ⟨w, rfl⟩
    · rw [encard_incidenceSet_left fl fr h.disjoint, hfl, ← Nat.cast_add,
        Nat.add_sub_cancel' (hdeg v)]
    · rw [encard_incidenceSet_right fl fr h.disjoint, hfr, ← Nat.cast_add,
        Nat.add_sub_cancel' (hdeg w)]
  inl_mem_vertexSet_iff x := by
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · rcases (mem_vertexSet_stubGraph fl fr h).1 hx with ⟨v, hv⟩ | ⟨w, hw⟩
      exacts [(sideVertex_eq_inl_iff.1 hv).1, (sideVertex_eq_inl_iff.1 hw).1]
    · rw [stubGraph, mem_vertexSet_extend]
      exact .inl ⟨x, hx, rfl⟩
  inl_mem_edgeSet_iff e := by
    rw [stubGraph, edgeSet_extend]
    simp
  isLink_inl_inl_iff e x y := by
    rw [stubGraph, extend_isLink_inl]
    simp
  inl_mem_left_iff hx _ := by
    rw [mem_stubLeft, ← exists_sideVertex_eq_inl_iff hx]
  inl_mem_right_iff hx _ := by
    rw [mem_stubRight, ← exists_sideVertex_eq_inl_iff hx]

end Construction

/-- **Regular bipartite completion.** A bipartite multigraph with finitely many edges whose
degrees are at most `k` is the subgraph of a finite `k`-regular bipartite multigraph on its
original vertices and edges, with sides extending its own. -/
theorem IsBipartition.exists_isRegularCompletion [Finite E(G)] (h : G.IsBipartition L R)
    (hk : ∀ x ∈ V(G), G.incidenceCount x ≤ k) :
    ∃ (G' : Graph (α ⊕ ℕ) (β ⊕ ℕ)) (L' R' : Finset V(G')),
      G.IsRegularCompletion L R k G' L' R' := by
  classical
  have := Fintype.ofFinite E(G)
  -- Pad both sides to the same size; then both sides have the same total degree deficit.
  have hpad : #L + padding L R = #R + padding R L := by
    simp only [padding]
    omega
  have hsumL := sum_sub_sideDegree_add (k := k) L (padding L R) fun x _ ↦ hk _ x.2
  have hsumR := sum_sub_sideDegree_add (k := k) R (padding R L) fun x _ ↦ hk _ x.2
  have hEL := h.sum_sum_incidentEdges_left fun _ ↦ (1 : ℕ)
  have hER := h.sum_sum_incidentEdges_right fun _ ↦ (1 : ℕ)
  simp only [sum_const, smul_eq_mul, mul_one, card_incidentEdges_singleton] at hEL hER
  rw [hEL, hpad] at hsumL
  rw [hER, ← hsumL] at hsumR
  -- Number the deficits of each side and join the deficits with the same number. A numbering
  -- `e : Fin n ≃ Σ v, Fin (d v)` gives exactly `d v` numbers to the deficits at `v`.
  have hcard {ι : Type _} [Fintype ι] [DecidableEq ι] {d : ι → ℕ} {n : ℕ}
      (e : Fin n ≃ Σ v, Fin (d v)) (v : ι) : #{i | (e i).1 = v} = d v := by
    rw [card_filter, e.sum_comp fun σ ↦ if σ.1 = v then 1 else 0, Fintype.sum_sigma,
      Fintype.sum_eq_single v fun x hx ↦
        Fintype.sum_eq_zero _ fun _ ↦ ite_eq_right_iff.2 fun h ↦ absurd h hx]
    simp
  let eL := (Fintype.equivFinOfCardEq (α := Σ v, Fin (k - sideDegree L (padding L R) v))
    (n := ∑ v, (k - sideDegree L (padding L R) v)) (by simp)).symm
  let eR := (Fintype.equivFinOfCardEq (α := Σ w, Fin (k - sideDegree R (padding R L) w))
    (n := ∑ v, (k - sideDegree L (padding L R) v))
    (by rw [Fintype.card_sigma]; simpa using hsumR)).symm
  exact ⟨_, _, _, isRegularCompletion_stubGraph (fun i ↦ (eL i).1) (fun i ↦ (eR i).1) h hk
    (hcard eL) (hcard eR)⟩

end Graph
