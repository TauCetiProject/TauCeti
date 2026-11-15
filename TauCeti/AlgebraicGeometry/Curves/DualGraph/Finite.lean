/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Iso

/-!
# Finite families of dual-graph types

For a fixed finite marking set and arithmetic genus there are only finitely many stable
connected dual graphs up to isomorphism. This is the discrete finiteness needed when sorting
nodal curves by normalization signature before choosing analytic charts.

`exists_finset_stable_representatives` supplies actual stable graphs, not just a bound on the
numbers of vertices and edges. Its representatives have vertex and edge types in `Type`,
while the graph being represented may live in any universe. Labels are preserved individually;
loops and multiple edges are allowed.

The construction uses the vertex and edge bounds in `DualGraph.Basic` and enumerates the
possible endpoint, genus and marking functions on finite standard carriers. It does not
choose an ordering of the branches invariant under graph automorphisms: the resulting
isomorphisms use the existing unordered-endpoint `DualGraph.Iso`.

## References

* E. Arbarello, M. Cornalba and P. A. Griffiths, *Geometry of Algebraic Curves, Volume II*,
  Chapter X, §2, for stable dual graphs and their finiteness at fixed genus and markings.
-/

public noncomputable section

namespace TauCeti.DualGraph

open Finset

universe u v

variable {ι : Type v}

-- The finite data used to enumerate graphs. Only the connected, nonempty presentations
-- are retained, so every presentation denotes an actual connected dual graph.
private abbrev Presentation (ι : Type v) (n m g : ℕ) : Type v :=
  {d : (Fin m → Fin 2 → Fin n) × (Fin n → Fin (g + 1)) × (ι → Fin n) //
    Nonempty (Fin n) ∧ ∀ x y, Relation.ReflTransGen
      (fun x y ↦ ∃ e, (d.1 e 0 = x ∧ d.1 e 1 = y) ∨
        (d.1 e 0 = y ∧ d.1 e 1 = x)) x y}

private abbrev Presentation.toGraph {n m g : ℕ} (d : Presentation ι n m g) :
    DualGraph.{0} ι where
  Vertex := Fin n
  vertexNonempty := d.property.1
  Edge := Fin m
  endpoint := d.val.1
  genus x := (d.val.2.1 x).val
  marking := d.val.2.2
  connected := d.property.2

private abbrev BoundedPresentation (ι : Type v) (V E g : ℕ) :=
  Σ n : Fin (V + 1), Σ m : Fin (E + 1), Presentation ι n.val m.val g

private abbrev BoundedPresentation.toGraph {V E g : ℕ} (d : BoundedPresentation ι V E g) :
    DualGraph.{0} ι :=
  d.2.2.toGraph

/-- With bounded vertex and edge counts and bounded component genera, a finite family of
standard graphs represents every labelled connected dual graph satisfying those bounds.
The representative has the same counts and genera up to an actual graph isomorphism. -/
theorem exists_finset_representatives_of_bounds [Finite ι] (V E g : ℕ) :
    ∃ S : Finset (DualGraph.{0} ι), ∀ G : DualGraph.{u} ι,
      Fintype.card G.Vertex ≤ V → Fintype.card G.Edge ≤ E →
      (∀ x, G.genus x ≤ g) → ∃ H ∈ S, Nonempty (G.Iso H) := by
  classical
  let S := (Set.finite_range
    (BoundedPresentation.toGraph (ι := ι) (V := V) (E := E) (g := g))).toFinset
  refine ⟨S, fun G hV hE hg ↦ ?_⟩
  let a := Fintype.equivFin G.Vertex
  let b := Fintype.equivFin G.Edge
  let d : Presentation ι (Fintype.card G.Vertex) (Fintype.card G.Edge) g :=
    ⟨(fun e k ↦ a (G.endpoint (b.symm e) k),
      fun x ↦ ⟨G.genus (a.symm x), Nat.lt_succ_of_le (hg _)⟩,
      fun i ↦ a (G.marking i)),
      ⟨⟨a (Classical.arbitrary G.Vertex)⟩, by
        apply G.connected_of_surjective a a.surjective
        intro e
        exact Or.inr ⟨b e, Or.inl ⟨by simp, by simp⟩⟩⟩⟩
  let c : BoundedPresentation ι V E g :=
    ⟨⟨_, Nat.lt_succ_of_le hV⟩, ⟨_, Nat.lt_succ_of_le hE⟩, d⟩
  refine ⟨c.toGraph, ?_, ⟨?_⟩⟩
  · exact (Set.Finite.mem_toFinset _).mpr ⟨c, rfl⟩
  · exact
      { vertexEquiv := a
        edgeEquiv := b
        ends_edgeEquiv := fun e ↦ by
          simp [c, d, BoundedPresentation.toGraph, Presentation.toGraph, ends_def,
            Sym2.map_mk]
        genus_vertexEquiv := fun x ↦ by
          dsimp only [c, d, BoundedPresentation.toGraph, Presentation.toGraph]
          simp
        vertexEquiv_marking := fun i ↦ rfl }

/-- For fixed arithmetic genus and finite marking set, finitely many stable dual graphs
represent all stable graphs up to label-preserving isomorphism. Every representative is
itself stable and has precisely the specified genus. The input graphs may have vertex and
edge types in an arbitrary universe. -/
theorem exists_finset_stable_representatives [Fintype ι] (g : ℕ) :
    ∃ S : Finset (DualGraph.{0} ι),
      (∀ H ∈ S, H.IsStable ∧ H.arithmeticGenus = g) ∧
      ∀ G : DualGraph.{u} ι, G.IsStable → G.arithmeticGenus = g →
        ∃ H ∈ S, Nonempty (G.Iso H) := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_representatives_of_bounds (ι := ι)
    (2 * g + Fintype.card ι - 2) (3 * g + Fintype.card ι - 3) g
  refine ⟨S.filter (fun H ↦ H.IsStable ∧ H.arithmeticGenus = g),
    fun H hH ↦ (mem_filter.mp hH).2, fun G hG hgenus ↦ ?_⟩
  have hV := hG.card_vertex_le
  have hE := hG.card_edge_le
  rw [hgenus] at hV hE
  have hV' : Fintype.card G.Vertex ≤ 2 * g + Fintype.card ι - 2 := by omega
  have hE' : Fintype.card G.Edge ≤ 3 * g + Fintype.card ι - 3 := by omega
  obtain ⟨H, hH, ⟨f⟩⟩ := hS G hV' hE' (fun x ↦ by
    rw [← hgenus]
    exact G.genus_le_arithmeticGenus x)
  exact ⟨H, mem_filter.mpr ⟨hH, f.isStable_iff.mp hG, f.arithmeticGenus_eq.symm.trans hgenus⟩,
    ⟨f⟩⟩

end TauCeti.DualGraph
