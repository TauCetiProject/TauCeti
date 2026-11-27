/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Pretransitive
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Order.Group.Action.End
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import TauCeti.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Vertex-, edge- and arc-transitive graphs

The automorphism group `G ≃g G` of a simple graph acts on its vertices (through
`RelIso.applyMulAction`), on its edges and on its darts, the ordered pairs of adjacent vertices.
A graph is *vertex-*, *edge-* or *arc-transitive* when the respective action is transitive. These
three notions organize the group-theoretic side of algebraic graph theory: Cayley graphs are
vertex-transitive, and the transitivity of the automorphism group on longer non-backtracking walks
refines arc-transitivity.

An arc-transitive graph is edge-transitive, and vertex-transitive as soon as it has no isolated
vertex. Conversely, an edge-transitive graph without isolated vertices that is not
vertex-transitive is bipartite with the two automorphism orbits as colour classes, and a finite
vertex- and edge-transitive graph that is not arc-transitive has even degree: its darts fall into
two orbits exchanged by reversal, and each vertex is the tail of equally many darts of each orbit.

## Main definitions

* `SimpleGraph.IsVertexTransitive`: `G ≃g G` acts transitively on the vertices.
* `SimpleGraph.IsEdgeTransitive`: `G ≃g G` acts transitively on the edges.
* `SimpleGraph.IsArcTransitive`: `G ≃g G` acts transitively on the darts.

## Main results

* `SimpleGraph.isVertexTransitive_iff`, `SimpleGraph.isEdgeTransitive_iff`,
  `SimpleGraph.isArcTransitive_iff`: the three notions in terms of automorphisms.
* `SimpleGraph.Iso.isVertexTransitive_iff`, `SimpleGraph.Iso.isEdgeTransitive_iff`,
  `SimpleGraph.Iso.isArcTransitive_iff`: invariance under graph isomorphism.
* `SimpleGraph.IsArcTransitive.isEdgeTransitive` and
  `SimpleGraph.IsArcTransitive.isVertexTransitive`: arc-transitivity implies edge-transitivity,
  and vertex-transitivity in the absence of isolated vertices.
* `SimpleGraph.IsEdgeTransitive.exists_orbit_bipartition`: an edge-transitive graph without
  isolated vertices that is not vertex-transitive has a proper `2`-colouring whose colour classes
  are the automorphism orbits.
* `SimpleGraph.even_degree_of_not_isArcTransitive`: a finite vertex- and edge-transitive graph
  that is not arc-transitive has even degrees.
* `SimpleGraph.isArcTransitive_top`: complete graphs are arc-transitive.

## References

* C. Godsil, G. Royle, *Algebraic Graph Theory*, Graduate Texts in Mathematics 207, Springer,
  2001, §3.2, Lemmas 3.2.1 and 3.2.2.
-/

public section

namespace SimpleGraph

variable {V W : Type*} (G : SimpleGraph V) {G' : SimpleGraph W}

/-- A graph is vertex-transitive when its automorphism group acts transitively on its
vertices. -/
def IsVertexTransitive : Prop :=
  MulAction.IsPretransitive (G ≃g G) V

/-- A graph is edge-transitive when its automorphism group acts transitively on its edges. -/
def IsEdgeTransitive : Prop :=
  MulAction.IsPretransitive (G ≃g G) G.edgeSet

/-- A graph is arc-transitive when its automorphism group acts transitively on its darts, the
ordered pairs of adjacent vertices. -/
def IsArcTransitive : Prop :=
  MulAction.IsPretransitive (G ≃g G) G.Dart

variable {G}

/-- Unfolding `SimpleGraph.IsVertexTransitive`: the automorphism group acts transitively on
its vertices. -/
theorem isVertexTransitive_iff_isPretransitive :
    G.IsVertexTransitive ↔ MulAction.IsPretransitive (G ≃g G) V :=
  (Iff.rfl)

/-- Unfolding `SimpleGraph.IsEdgeTransitive`: the automorphism group acts transitively on
its edges. -/
theorem isEdgeTransitive_iff_isPretransitive :
    G.IsEdgeTransitive ↔ MulAction.IsPretransitive (G ≃g G) G.edgeSet :=
  (Iff.rfl)

/-- Unfolding `SimpleGraph.IsArcTransitive`: the automorphism group acts transitively on
its darts. -/
theorem isArcTransitive_iff_isPretransitive :
    G.IsArcTransitive ↔ MulAction.IsPretransitive (G ≃g G) G.Dart :=
  (Iff.rfl)

/-- A graph is vertex-transitive exactly when every vertex is carried to every other by an
automorphism. -/
theorem isVertexTransitive_iff : G.IsVertexTransitive ↔ ∀ x y : V, ∃ φ : G ≃g G, φ x = y := by
  simp [isVertexTransitive_iff_isPretransitive, MulAction.isPretransitive_iff, RelIso.smul_def]

/-- A graph is edge-transitive exactly when every edge is carried to every other by an
automorphism. -/
theorem isEdgeTransitive_iff : G.IsEdgeTransitive ↔
    ∀ e ∈ G.edgeSet, ∀ e' ∈ G.edgeSet, ∃ φ : G ≃g G, Sym2.map φ e = e' := by
  simp [isEdgeTransitive_iff_isPretransitive, MulAction.isPretransitive_iff, Subtype.ext_iff]

/-- A graph is arc-transitive exactly when, for any two pairs of adjacent vertices, some
automorphism carries the first pair to the second. -/
theorem isArcTransitive_iff : G.IsArcTransitive ↔
    ∀ ⦃x y x' y' : V⦄, G.Adj x y → G.Adj x' y' → ∃ φ : G ≃g G, φ x = x' ∧ φ y = y' := by
  simp only [isArcTransitive_iff_isPretransitive, MulAction.isPretransitive_iff, Dart.ext_iff,
    Prod.ext_iff, Iso.fst_smul_dart, Iso.snd_smul_dart]
  exact ⟨fun h x y x' y' hxy hxy' => h ⟨(x, y), hxy⟩ ⟨(x', y'), hxy'⟩,
    fun h d d' => h d.adj d'.adj⟩

/-- A graph is vertex-transitive as soon as a subgroup of its automorphism group acts
transitively on its vertices. -/
theorem IsVertexTransitive.of_subgroup (H : Subgroup (G ≃g G)) [MulAction.IsPretransitive H V] :
    G.IsVertexTransitive :=
  .of_smul_eq (Subtype.val : H → G ≃g G) rfl

/-- A graph is edge-transitive as soon as a subgroup of its automorphism group acts
transitively on its edges. -/
theorem IsEdgeTransitive.of_subgroup (H : Subgroup (G ≃g G))
    [MulAction.IsPretransitive H G.edgeSet] : G.IsEdgeTransitive :=
  .of_smul_eq (Subtype.val : H → G ≃g G) rfl

/-- A graph is arc-transitive as soon as a subgroup of its automorphism group acts
transitively on its darts. -/
theorem IsArcTransitive.of_subgroup (H : Subgroup (G ≃g G))
    [MulAction.IsPretransitive H G.Dart] : G.IsArcTransitive :=
  .of_smul_eq (Subtype.val : H → G ≃g G) rfl

section Iso

private theorem IsVertexTransitive.of_iso (e : G ≃g G') (h : G.IsVertexTransitive) :
    G'.IsVertexTransitive := by
  rw [isVertexTransitive_iff] at h ⊢
  intro x y
  obtain ⟨φ, hφ⟩ := h (e.symm x) (e.symm y)
  exact ⟨RelIso.relIsoCongr e e φ, by simp [hφ]⟩

private theorem IsEdgeTransitive.of_iso (e : G ≃g G') (h : G.IsEdgeTransitive) :
    G'.IsEdgeTransitive := by
  rw [isEdgeTransitive_iff] at h ⊢
  intro a ha b hb
  obtain ⟨φ, hφ⟩ := h _ (e.symm.map_mem_edgeSet_iff.2 ha) _ (e.symm.map_mem_edgeSet_iff.2 hb)
  refine ⟨RelIso.relIsoCongr e e φ, ?_⟩
  have hcongr : ⇑(RelIso.relIsoCongr e e φ) = e ∘ φ ∘ e.symm :=
    funext (RelIso.relIsoCongr_apply_apply e e φ)
  rw [hcongr, ← Sym2.map_map, ← Sym2.map_map, hφ, Sym2.map_map]
  simp

private theorem IsArcTransitive.of_iso (e : G ≃g G') (h : G.IsArcTransitive) :
    G'.IsArcTransitive := by
  rw [isArcTransitive_iff] at h ⊢
  intro x y x' y' hxy hxy'
  obtain ⟨φ, h₁, h₂⟩ := h (e.symm.map_adj_iff.2 hxy) (e.symm.map_adj_iff.2 hxy')
  exact ⟨RelIso.relIsoCongr e e φ, by simp [h₁], by simp [h₂]⟩

/-- Vertex-transitivity is invariant under graph isomorphism. -/
theorem Iso.isVertexTransitive_iff (e : G ≃g G') :
    G.IsVertexTransitive ↔ G'.IsVertexTransitive :=
  ⟨.of_iso e, .of_iso e.symm⟩

/-- Edge-transitivity is invariant under graph isomorphism. -/
theorem Iso.isEdgeTransitive_iff (e : G ≃g G') : G.IsEdgeTransitive ↔ G'.IsEdgeTransitive :=
  ⟨.of_iso e, .of_iso e.symm⟩

/-- Arc-transitivity is invariant under graph isomorphism. -/
theorem Iso.isArcTransitive_iff (e : G ≃g G') : G.IsArcTransitive ↔ G'.IsArcTransitive :=
  ⟨.of_iso e, .of_iso e.symm⟩

end Iso

/-- An arc-transitive graph is edge-transitive. -/
theorem IsArcTransitive.isEdgeTransitive (h : G.IsArcTransitive) : G.IsEdgeTransitive := by
  rw [isEdgeTransitive_iff]
  rintro ⟨x, y⟩ hxy ⟨x', y'⟩ hxy'
  obtain ⟨φ, h₁, h₂⟩ := isArcTransitive_iff.1 h hxy hxy'
  exact ⟨φ, by simp [h₁, h₂]⟩

/-- An arc-transitive graph without isolated vertices is vertex-transitive. -/
theorem IsArcTransitive.isVertexTransitive (h : G.IsArcTransitive) (hG : ∀ x, ∃ y, G.Adj x y) :
    G.IsVertexTransitive := by
  rw [isVertexTransitive_iff]
  intro x x'
  obtain ⟨y, hy⟩ := hG x
  obtain ⟨y', hy'⟩ := hG x'
  obtain ⟨φ, hφ, -⟩ := isArcTransitive_iff.1 h hy hy'
  exact ⟨φ, hφ⟩

/-- **Godsil–Royle, Lemma 3.2.1.** An edge-transitive graph without isolated vertices that is not
vertex-transitive has a proper `2`-colouring whose colour classes are exactly the orbits of its
automorphism group. -/
theorem IsEdgeTransitive.exists_orbit_bipartition (h : G.IsEdgeTransitive)
    (hG : ∀ x, ∃ y, G.Adj x y) (hvt : ¬ G.IsVertexTransitive) :
    ∃ c : V → Bool, (∀ x y, G.Adj x y → c x ≠ c y) ∧
      ∀ x y, (c x = c y ↔ ∃ φ : G ≃g G, φ x = y) := by
  classical
  -- `x ~ y` when an automorphism carries `x` to `y`.
  let R : V → V → Prop := fun x y => ∃ φ : G ≃g G, φ x = y
  have hsymm : ∀ {x y}, R x y → R y x := fun ⟨φ, hφ⟩ => ⟨φ.symm, by simp [← hφ]⟩
  have htrans : ∀ {x y z}, R x y → R y z → R x z := fun ⟨φ, hφ⟩ ⟨ψ, hψ⟩ =>
    ⟨φ.trans ψ, by simp [hφ, hψ]⟩
  -- Some vertex `x₀` is not related to every vertex; take a neighbour `y₀` of `x₀`.
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, ¬ ∀ y, R x₀ y := by
    by_contra! hall
    exact hvt (isVertexTransitive_iff.2 hall)
  obtain ⟨y₀, h₀⟩ := hG x₀
  -- An edge has one end in the orbit of `x₀` and the other in the orbit of `y₀`.
  have hedge : ∀ {x y}, G.Adj x y → (R x₀ x ∧ R y₀ y) ∨ (R x₀ y ∧ R y₀ x) := by
    intro x y hxy
    obtain ⟨φ, hφ⟩ := isEdgeTransitive_iff.1 h _ (G.mem_edgeSet.2 h₀) _ (G.mem_edgeSet.2 hxy)
    rcases Sym2.eq_iff.1 (by simpa using hφ) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact .inl ⟨⟨φ, h₁⟩, ⟨φ, h₂⟩⟩
    · exact .inr ⟨⟨φ, h₁⟩, ⟨φ, h₂⟩⟩
  have hcover : ∀ x, R x₀ x ∨ R y₀ x := fun x => by
    obtain ⟨y, hy⟩ := hG x
    rcases hedge hy with ⟨h₁, -⟩ | ⟨-, h₂⟩
    exacts [.inl h₁, .inr h₂]
  -- The two orbits are different, since otherwise there would be only one orbit.
  have hne : ¬ R x₀ y₀ := fun hxy => hx₀ fun y =>
    (hcover y).elim id fun hy => htrans hxy hy
  have hdisj : ∀ {x}, R x₀ x → ¬ R y₀ x := fun h₁ h₂ => hne (htrans h₁ (hsymm h₂))
  refine ⟨fun x => decide (R x₀ x), fun x y hxy => ?_, fun x y => ?_⟩
  · rcases hedge hxy with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · simpa [h₁] using fun h => hdisj h h₂
    · simpa [h₁] using fun h => hdisj h h₂
  · simp only [decide_eq_decide]
    refine ⟨fun hxy => ?_, fun hxy => ⟨fun h => htrans h hxy, fun h => htrans h (hsymm hxy)⟩⟩
    by_cases hx : R x₀ x
    · exact htrans (hsymm hx) (hxy.1 hx)
    · have hy : ¬ R x₀ y := fun h => hx (hxy.2 h)
      exact htrans (hsymm ((hcover x).resolve_left hx)) ((hcover y).resolve_left hy)

section Degree

variable [Fintype V] [DecidableRel G.Adj]

open Finset

/-- For a property of darts invariant under automorphisms, the number of darts with that property
starting at a vertex is unchanged when an automorphism moves the vertex. -/
private theorem card_filter_dart_fst_apply [DecidableEq V] (P : G.Dart → Prop) [DecidablePred P]
    (hP : ∀ (φ : G ≃g G) d, P (φ • d) ↔ P d) (φ : G ≃g G) (x : V) :
    #{d : G.Dart | d.fst = φ x ∧ P d} = #{d : G.Dart | d.fst = x ∧ P d} := by
  refine (card_equiv (MulAction.toPerm φ) fun d => ?_).symm
  simp [hP]

/-- In a vertex-transitive graph, for a property of darts invariant under automorphisms, the
total number of darts with that property is the number of vertices times the number of such darts
starting at any given vertex. -/
private theorem card_filter_dart_eq_card_mul [DecidableEq V] (hvt : G.IsVertexTransitive)
    (P : G.Dart → Prop) [DecidablePred P] (hP : ∀ (φ : G ≃g G) d, P (φ • d) ↔ P d) (x : V) :
    #{d : G.Dart | P d} = Fintype.card V * #{d : G.Dart | d.fst = x ∧ P d} := by
  rw [card_eq_sum_card_fiberwise (f := fun d : G.Dart => d.fst) (t := univ) fun _ _ => mem_univ _,
    ← card_univ, ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun y _ => ?_
  obtain ⟨φ, rfl⟩ := isVertexTransitive_iff.1 hvt x y
  rw [filter_filter, ← card_filter_dart_fst_apply P hP φ x]
  exact congrArg card (filter_congr fun _ _ => and_comm)

/-- **Godsil–Royle, Lemma 3.2.2.** In a finite vertex- and edge-transitive graph that is not
arc-transitive, every vertex has even degree. -/
theorem even_degree_of_not_isArcTransitive (hvt : G.IsVertexTransitive)
    (het : G.IsEdgeTransitive) (hat : ¬ G.IsArcTransitive) (x : V) : Even (G.degree x) := by
  classical
  -- There is a dart `d₀`, since a graph without darts is arc-transitive.
  obtain ⟨d₀⟩ : Nonempty G.Dart := by
    by_contra! hd
    exact hat ⟨fun d => (hd.false d).elim⟩
  let O := MulAction.orbit (G ≃g G) d₀
  have hO : ∀ (φ : G ≃g G) d, φ • d ∈ O ↔ d ∈ O := fun φ d => by
    rw [← MulAction.orbit_eq_iff, MulAction.orbit_smul, MulAction.orbit_eq_iff]
  -- Every dart or its reversal lies in the orbit `O` of `d₀`, by edge-transitivity.
  have hcover : ∀ d : G.Dart, d ∈ O ∨ d.symm ∈ O := by
    intro d
    obtain ⟨φ, hφ⟩ := isEdgeTransitive_iff.1 het _ d₀.edge_mem _ d.edge_mem
    rcases (dart_edge_eq_iff (φ • d₀) d).1 (by simpa using hφ) with h | h
    · exact .inl ⟨φ, h⟩
    · exact .inr ⟨φ, by simp [h]⟩
  -- The reversal of `d₀` is not in `O`, since otherwise `O` would contain every dart.
  have hd₀ : d₀.symm ∉ O := by
    intro h
    obtain ⟨φ, hφ⟩ := MulAction.mem_orbit_iff.1 h
    refine hat (.of_orbit fun d => (hcover d).elim MulAction.mem_orbit_iff.1 fun h' => ?_)
    obtain ⟨ψ, hψ⟩ := MulAction.mem_orbit_iff.1 h'
    exact ⟨ψ * φ, by rw [mul_smul, hφ, ← Iso.symm_smul_dart, hψ, Dart.symm_symm]⟩
  -- Hence exactly one of a dart and its reversal lies in `O`.
  have hsymm : ∀ d : G.Dart, d.symm ∈ O ↔ d ∉ O := by
    refine fun d => ⟨fun h₁ h₂ => hd₀ ?_, (hcover d).resolve_left⟩
    obtain ⟨φ, rfl⟩ := MulAction.mem_orbit_iff.1 h₂
    rwa [Iso.symm_smul_dart, hO] at h₁
  have hO' : ∀ (φ : G ≃g G) (d : G.Dart), (φ • d).symm ∈ O ↔ d.symm ∈ O := fun φ d => by
    rw [Iso.symm_smul_dart, hO]
  -- Reversal exchanges the darts in `O` with those whose reversal is in `O`; vertex-transitivity
  -- makes both kinds equally numerous at every vertex.
  have hcount : #{d : G.Dart | d.fst = x ∧ d ∈ O} = #{d : G.Dart | d.fst = x ∧ d.symm ∈ O} := by
    have h₁ := card_filter_dart_eq_card_mul hvt (· ∈ O) hO x
    have h₂ := card_filter_dart_eq_card_mul hvt (·.symm ∈ O) hO' x
    have h₃ : #{d : G.Dart | d ∈ O} = #{d : G.Dart | d.symm ∈ O} :=
      card_equiv (Dart.symm_involutive.toPerm _) fun d => by simp
    exact Nat.eq_of_mul_eq_mul_left (Fintype.card_pos_iff.2 ⟨x⟩) (h₁.symm.trans (h₃.trans h₂))
  refine ⟨#{d : G.Dart | d.fst = x ∧ d ∈ O}, ?_⟩
  rw [← dart_fst_fiber_card_eq_degree, ← card_filter_add_card_filter_not (· ∈ O),
    filter_filter, filter_filter, hcount]
  simp_rw [← hsymm]

end Degree

/-- A complete graph is arc-transitive: a permutation can carry any two distinct vertices to any
two distinct vertices. -/
theorem isArcTransitive_top : (⊤ : SimpleGraph V).IsArcTransitive := by
  classical
  rw [isArcTransitive_iff]
  intro x y x' y' hxy hxy'
  -- First move `x` to `x'`, then the image of `y` to `y'` while fixing `x'`.
  let σ : Equiv.Perm V := Equiv.swap x x'
  have hσ : σ y ≠ x' := by
    simpa [σ, Equiv.swap_apply_left] using σ.injective.ne hxy.ne.symm
  refine ⟨Iso.completeGraph (σ.trans (Equiv.swap (σ y) y')), ?_, ?_⟩
  · simp [σ, Equiv.swap_apply_of_ne_of_ne hσ.symm hxy'.ne]
  · simp

end SimpleGraph
