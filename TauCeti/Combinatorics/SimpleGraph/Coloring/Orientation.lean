/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Orientation
import TauCeti.RepresentationTheory.Quiver.Acyclic.FinitePaths

/-!
# The acyclic orientation of a colouring

A colouring `C` of a simple graph by a linearly ordered type of colours orients each edge from its
end of smaller colour to its end of larger colour. Adjacent vertices have distinct colours, so
this chooses exactly one dart over each edge. Colours increase strictly along every directed path
of positive length, so the orientation is acyclic, and with `n` colours every directed path has
fewer than `n` arcs.

Hence a `k`-colourable graph has an acyclic orientation with no directed path of length `k`. This
is the sharpness half of the Gallai-Roy theorem, which says that every orientation of a graph of
chromatic number `k` has a directed path with `k` vertices.

The orientation is the pullback, along `C : G →g ⊤`, of the orientation of the complete graph on
the colours by their linear order, so its path bounds come from the bounds for that orientation.

## Main definitions

* `SimpleGraph.Coloring.orientation`: the orientation of `G` from smaller to larger colour.

## Main statements

* `SimpleGraph.Coloring.lt_of_path_of_length_pos_orientation`: colours increase strictly along
  a directed path of positive length.
* `SimpleGraph.Coloring.isAcyclic_orientation`: the orientation is acyclic.
* `SimpleGraph.Coloring.length_lt_card_of_path_orientation`: with finitely many colours, every
  directed path has fewer arcs than there are colours.
* `SimpleGraph.Coloring.orientation_eq_sourceSink`: for a colouring by `Bool`, the orientation
  is `SimpleGraph.Coloring.sourceSink`.
* `SimpleGraph.exists_isAcyclic_orientation_of_colorable`: a `k`-colourable graph has an acyclic
  orientation in which every directed path has fewer than `k` arcs.

## References

* J. A. Bondy and U. S. R. Murty, *Graph Theory with Applications*, p. 174, the remark after
  Theorem 10.1.
* R. Diestel, *Graph Theory*, Chapter 5, Exercise 18.
-/

public section

open TauCeti.DoubledQuiver

namespace SimpleGraph

variable {V α : Type*} {G : SimpleGraph V}

namespace Coloring

/-- The orientation of `G` defined by a colouring `C` by a linear order: each edge is directed
from its end of smaller colour to its end of larger colour. -/
def orientation [LinearOrder α] (C : G.Coloring α) : Orientation G :=
  (Orientation.ofLinearOrder (⊤ : SimpleGraph α)).comap C

/-- A dart belongs to the orientation of a colouring exactly when the colour of its first end is
smaller than the colour of its second end. -/
@[simp]
theorem mem_orientation_iff [LinearOrder α] (C : G.Coloring α) (d : G.Dart) :
    d ∈ C.orientation ↔ C d.fst < C d.snd := by
  simp [orientation]

/-- A colouring sends each dart of its orientation to a dart of the orientation of `⊤` by the
linear order of the colours. -/
private theorem mapDart_mem_ofLinearOrder [LinearOrder α] (C : G.Coloring α) (d : G.Dart)
    (hd : d ∈ C.orientation) : C.mapDart d ∈ Orientation.ofLinearOrder (⊤ : SimpleGraph α) := by
  simpa using hd

/-- Along a directed path of positive length in the orientation of a colouring, the colour of the
start is smaller than the colour of the end. -/
theorem lt_of_path_of_length_pos_orientation [LinearOrder α] (C : G.Coloring α)
    {a b : OrientedQuiver G C.orientation} (p : Quiver.Path a b) (hp : 0 < p.length) :
    C ((OrientedQuiver.vertexEquiv G C.orientation).symm a) <
      C ((OrientedQuiver.vertexEquiv G C.orientation).symm b) := by
  have h := OrientedQuiver.lt_of_path_of_length_pos_ofLinearOrder (⊤ : SimpleGraph α)
    ((OrientedQuiver.map C (mapDart_mem_ofLinearOrder C)).mapPath p)
    (by rwa [Prefunctor.length_mapPath])
  simpa using h

/-- The orientation of a colouring is acyclic. -/
theorem isAcyclic_orientation [LinearOrder α] (C : G.Coloring α) :
    TauCeti.Quiver.IsAcyclic (OrientedQuiver G C.orientation) :=
  (OrientedQuiver.map C (mapDart_mem_ofLinearOrder C)).isAcyclic_of_codomain
    (OrientedQuiver.isAcyclic_ofLinearOrder ⊤)

/-- In the orientation of a colouring by finitely many colours, every directed path has fewer
arcs than there are colours. -/
theorem length_lt_card_of_path_orientation [LinearOrder α] [Fintype α] (C : G.Coloring α)
    {a b : OrientedQuiver G C.orientation} (p : Quiver.Path a b) :
    p.length < Fintype.card α := by
  have h := (OrientedQuiver.isAcyclic_ofLinearOrder (⊤ : SimpleGraph α)).length_lt_card
    ((OrientedQuiver.map C (mapDart_mem_ofLinearOrder C)).mapPath p)
  rwa [Prefunctor.length_mapPath, Fintype.card_congr (OrientedQuiver.vertexEquiv _ _).symm] at h

/-- For a colouring by `Bool`, the orientation from smaller to larger colour directs each edge
toward its end of colour `true`. -/
theorem orientation_eq_sourceSink (C : G.Coloring Bool) : C.orientation = C.sourceSink := by
  ext d
  have h := C.valid d.adj
  rw [mem_orientation_iff, mem_sourceSink_iff]
  revert h
  cases C d.fst <;> cases C d.snd <;> decide

end Coloring

/-- A `k`-colourable graph has an acyclic orientation in which every directed path has fewer than
`k` arcs. The bound holds for all directed paths, not only for those with distinct vertices; see
`SimpleGraph.Coloring.length_lt_card_of_path_orientation`. -/
theorem exists_isAcyclic_orientation_of_colorable {k : ℕ} (hk : G.Colorable k) :
    ∃ o : Orientation G, TauCeti.Quiver.IsAcyclic (OrientedQuiver G o) ∧
      ∀ (a b : OrientedQuiver G o) (p : Quiver.Path a b), p.vertices.Nodup → p.length < k := by
  obtain ⟨C⟩ := hk
  exact ⟨C.orientation, C.isAcyclic_orientation, fun _ _ p _ ↦ by
    simpa using C.length_lt_card_of_path_orientation p⟩

end SimpleGraph
