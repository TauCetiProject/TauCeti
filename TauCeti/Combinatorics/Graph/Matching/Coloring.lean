/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.LineGraph
public import TauCeti.Combinatorics.Graph.Matching.Basic

/-!
# Edge-colourings and partitions into matchings

For a loopless multigraph, matchings are precisely the independent sets of its line graph.
Consequently the colour classes of a proper edge-colouring form a partition into matchings.
Conversely, a family of matchings containing every actual edge exactly once determines an
edge-colouring, with the family indices as colours. Empty matchings are allowed, so unused
colours are retained and the construction also works with an empty colour type.

`Graph.edgeColoringEquivMatchings` gives both round trips. The existence form
`Graph.nonempty_edgeColoring_iff_exists_matchings` uses pairwise disjointness and coverage;
it converts matching decompositions into edge-colourings without renaming their colours.
No finiteness of vertices, edges, or colours is required. Parallel edges retain their identities.
The loopless hypothesis is essential in the direction from colourings to matchings: a loop can
receive a colour in the line graph, but cannot belong to a matching.
-/

public section

open Set

universe u v w

namespace Graph

variable {α : Type u} {β : Type v} {C : Type w} {G : Graph α β} {M : Set E(G)}

/-- The edges of a matching are independent vertices of the line graph. -/
theorem IsMatching.isIndepSet_lineGraph (hM : G.IsMatching M) : G.lineGraph.IsIndepSet M := by
  intro e he f hf hef hadj
  obtain ⟨_, x, hex, hfx⟩ := lineGraph_adj.1 hadj
  exact hef (hM.eq_of_inc he hf hex hfx)

/-- In a loopless multigraph, an independent set of the line graph is a matching. -/
theorem isMatching_of_isIndepSet_lineGraph [G.Loopless] (hM : G.lineGraph.IsIndepSet M) :
    G.IsMatching M := by
  apply isMatching_def.2
  refine ⟨fun e _ x ↦ G.not_isLoopAt e x, ?_⟩
  intro e he f hf hef x hinc
  exact hM he hf hef (lineGraph_adj.2 ⟨hef, x, hinc⟩)

/-- Matchings in a loopless multigraph are exactly the independent sets of its line graph. -/
theorem isMatching_iff_isIndepSet_lineGraph [G.Loopless] :
    G.IsMatching M ↔ G.lineGraph.IsIndepSet M :=
  ⟨IsMatching.isIndepSet_lineGraph, isMatching_of_isIndepSet_lineGraph⟩

namespace EdgeColoring

/-- Each colour class of a proper edge-colouring of a loopless multigraph is a matching. -/
theorem isMatching_colorClass [G.Loopless] (c : G.EdgeColoring C) (i : C) :
    G.IsMatching (c.colorClass i) :=
  isMatching_of_isIndepSet_lineGraph (c.isIndepSet_colorClass i)

/-- Build an edge-colouring from matchings that contain each actual edge exactly once.
The family may contain empty matchings, and no inhabitant of the colour type is needed. -/
noncomputable def ofMatchings (M : C → Set E(G)) (hM : ∀ i, G.IsMatching (M i))
    (hpart : ∀ e, ∃! i, e ∈ M i) : G.EdgeColoring C :=
  EdgeColoring.mk (fun e ↦ (hpart e).choose) fun {e f} {x} hef hex hfx hcol ↦ by
    have he := (hpart e).choose_spec.1
    have hf := (hpart f).choose_spec.1
    rw [← hcol] at hf
    exact hef ((hM _).eq_of_inc he hf hex hfx)

/-- The colour assigned by a matching partition is its unique index containing the edge. -/
@[simp]
theorem ofMatchings_apply_eq_iff (M : C → Set E(G)) (hM : ∀ i, G.IsMatching (M i))
    (hpart : ∀ e, ∃! i, e ∈ M i) (e : E(G)) (i : C) :
    ofMatchings M hM hpart e = i ↔ e ∈ M i := by
  simp only [ofMatchings, coe_mk]
  exact ⟨fun h ↦ h ▸ (hpart e).choose_spec.1,
    fun h ↦ ((hpart e).choose_spec.2 i h).symm⟩

/-- Reconstructing a colouring from a matching partition recovers every part, including empty
parts. -/
@[simp]
theorem colorClass_ofMatchings (M : C → Set E(G)) (hM : ∀ i, G.IsMatching (M i))
    (hpart : ∀ e, ∃! i, e ∈ M i) (i : C) :
    (ofMatchings M hM hpart).colorClass i = M i := by
  ext e
  exact ofMatchings_apply_eq_iff M hM hpart e i

/-- An edge-colouring is recovered from its colour classes. -/
@[simp]
theorem ofMatchings_colorClass [G.Loopless] (c : G.EdgeColoring C)
    (hpart : ∀ e, ∃! i, e ∈ c.colorClass i) :
    ofMatchings c.colorClass c.isMatching_colorClass hpart = c := by
  ext e
  exact (ofMatchings_apply_eq_iff _ _ _ e (c e)).2 (c.mem_colorClass e)

end EdgeColoring

/-- Edge-colourings of a loopless multigraph correspond to indexed partitions of its actual
edges into matchings. Empty parts are allowed and retain the unused colour labels. -/
noncomputable def edgeColoringEquivMatchings (G : Graph α β) [G.Loopless] (C : Type w) :
    G.EdgeColoring C ≃
      {M : C → Set E(G) // (∀ i, G.IsMatching (M i)) ∧ ∀ e, ∃! i, e ∈ M i} where
  toFun c := ⟨c.colorClass, c.isMatching_colorClass, fun e ↦ ⟨c e, rfl, fun _ h ↦ h.symm⟩⟩
  invFun M := EdgeColoring.ofMatchings M.1 M.2.1 M.2.2
  left_inv c := c.ofMatchings_colorClass _
  right_inv M := by
    apply Subtype.ext
    funext i
    exact EdgeColoring.colorClass_ofMatchings M.1 M.2.1 M.2.2 i

/-- The matching indexed by a colour in the forward correspondence is its colour class. -/
@[simp]
theorem edgeColoringEquivMatchings_apply [G.Loopless] (c : G.EdgeColoring C) (i : C) :
    (edgeColoringEquivMatchings G C c).1 i = c.colorClass i :=
  (rfl)

/-- The inverse correspondence colours an edge by the index of its matching. -/
@[simp]
theorem edgeColoringEquivMatchings_symm_apply_eq_iff [G.Loopless]
    (M : {M : C → Set E(G) // (∀ i, G.IsMatching (M i)) ∧ ∀ e, ∃! i, e ∈ M i})
    (e : E(G)) (i : C) :
    (edgeColoringEquivMatchings G C).symm M e = i ↔ e ∈ M.1 i :=
  EdgeColoring.ofMatchings_apply_eq_iff M.1 M.2.1 M.2.2 e i

/-- A loopless multigraph admits a proper edge-colouring by `C` exactly when its actual edges
are the disjoint union of a `C`-indexed family of matchings. In particular, taking `C = Fin k`
expresses edge-colourability as a partition into `k` matchings, allowing empty colour classes. -/
theorem nonempty_edgeColoring_iff_exists_matchings [G.Loopless] :
    Nonempty (G.EdgeColoring C) ↔
      ∃ M : C → Set E(G), (∀ i, G.IsMatching (M i)) ∧
        (Pairwise fun i j ↦ Disjoint (M i) (M j)) ∧ ⋃ i, M i = univ := by
  constructor
  · rintro ⟨c⟩
    refine ⟨c.colorClass, c.isMatching_colorClass, ?_, ?_⟩
    · exact pairwise_disjoint_fiber c
    · exact Set.iUnion_eq_univ_iff.2 fun e ↦ ⟨c e, c.mem_colorClass e⟩
  · rintro ⟨M, hM, hdisj, hcover⟩
    refine ⟨EdgeColoring.ofMatchings M hM fun e ↦ ?_⟩
    obtain ⟨i, hi⟩ := Set.iUnion_eq_univ_iff.1 hcover e
    refine ⟨i, hi, fun j hj ↦ ?_⟩
    by_contra hji
    exact Set.disjoint_left.1 (hdisj hji) hj hi

end Graph
