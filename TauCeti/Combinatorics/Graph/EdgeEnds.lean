/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Data.Sym.Sym2

/-!
# Endpoints of an actual multigraph edge

This file associates to every actual edge of a multigraph the unordered pair of its actual
vertices. It provides an endpoint interface that retains edge identities for parallel edges.

## Main definition

* `Graph.edgeEnds`: the unordered pair of actual vertices at the ends of an actual edge.
-/

public section

namespace Graph

variable {V E : Type*} (G : Graph V E)

private theorem edgeEnds_spec_nonempty (e : G.edgeSet) :
    Nonempty {p : Sym2 G.vertexSet //
      ∀ x y : G.vertexSet, p = s(x, y) ↔ G.IsLink e.1 x.1 y.1} := by
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet e.property
  refine ⟨⟨s(⟨x, hxy.left_mem⟩, ⟨y, hxy.right_mem⟩), ?_⟩⟩
  intro u v
  rw [Sym2.eq_iff]
  simpa only [Subtype.ext_iff] using hxy.isLink_iff.symm

/-- The unordered pair of actual vertices at the ends of an actual edge. -/
noncomputable def edgeEnds (e : G.edgeSet) : Sym2 G.vertexSet :=
  (Classical.choice (edgeEnds_spec_nonempty G e)).1

/-- `edgeEnds` records exactly the `IsLink` relation of an actual edge. -/
@[simp]
theorem edgeEnds_eq_iff_isLink (e : G.edgeSet) (x y : G.vertexSet) :
    G.edgeEnds e = s(x, y) ↔ G.IsLink e.1 x.1 y.1 := by
  classical
  exact (Classical.choice (edgeEnds_spec_nonempty G e)).2 x y

/-- The vertices in `edgeEnds e` are exactly the vertices incident to `e`. -/
@[simp]
theorem mem_edgeEnds_iff (e : G.edgeSet) (x : G.vertexSet) :
    x ∈ G.edgeEnds e ↔ G.Inc e.1 x.1 := by
  constructor
  · rw [Sym2.mem_iff_exists]
    rintro ⟨y, hy⟩
    exact ((G.edgeEnds_eq_iff_isLink e x y).1 hy).inc_left
  · rintro ⟨y, hxy⟩
    rw [Sym2.mem_iff_exists]
    let y' : G.vertexSet := ⟨y, hxy.right_mem⟩
    exact ⟨y', (G.edgeEnds_eq_iff_isLink e x y').2 hxy⟩

end Graph
