/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# The underlying graph of a quiver

The underlying graph of a quiver joins two distinct vertices when an arrow runs between them in
either direction (`TauCeti.Quiver.underlyingGraph`). It forgets loops, the direction of the arrows
and their multiplicity, so it records what orientation-free statements about a quiver, such as
Gabriel's theorem, are phrased in terms of; it depends only on the arrows joining each pair of
vertices, whatever their direction (`TauCeti.Quiver.underlyingGraph_congr`).

## Main definitions

* `TauCeti.Quiver.underlyingGraph`: the simple graph underlying a quiver.

## Main results

* `TauCeti.Quiver.underlyingGraph_adj`: two vertices are adjacent when they are distinct and
  joined by an arrow in one direction or the other.
* `TauCeti.Quiver.underlyingGraph_congr`: two quiver structures joining the same pairs of
  vertices by an arrow, in either direction, have the same underlying graph.
-/

public section

namespace TauCeti

universe u v

variable {V : Type u}

namespace Quiver

section UnderlyingGraph

variable [_root_.Quiver.{v} V]

variable (V) in
/-- The simple graph underlying a quiver: two distinct vertices are adjacent when an arrow runs
between them in either direction. Loops, the direction of the arrows and their multiplicity are
forgotten. -/
def underlyingGraph : SimpleGraph V :=
  SimpleGraph.fromRel fun a b ↦ Nonempty (a ⟶ b)

/-- Two vertices are adjacent in the underlying graph when they are distinct and joined by an
arrow in one direction or the other. -/
@[simp]
theorem underlyingGraph_adj {a b : V} :
    (underlyingGraph V).Adj a b ↔ a ≠ b ∧ (Nonempty (a ⟶ b) ∨ Nonempty (b ⟶ a)) :=
  SimpleGraph.fromRel_adj ..

/-- The two ends of an arrow which is not a loop are adjacent in the underlying graph. -/
theorem underlyingGraph_adj_of_hom {a b : V} (e : a ⟶ b) (hab : a ≠ b) :
    (underlyingGraph V).Adj a b :=
  underlyingGraph_adj.mpr ⟨hab, .inl ⟨e⟩⟩

end UnderlyingGraph

/-- **The underlying graph depends only on which vertices are joined**: two quiver structures
which join the same pairs of vertices by an arrow, in one direction or the other, have the same
underlying graph. -/
theorem underlyingGraph_congr {q q' : _root_.Quiver.{v} V}
    (h : ∀ a b : V, Nonempty (@_root_.Quiver.Hom V q a b ⊕ @_root_.Quiver.Hom V q b a) ↔
      Nonempty (@_root_.Quiver.Hom V q' a b ⊕ @_root_.Quiver.Hom V q' b a)) :
    @underlyingGraph V q = @underlyingGraph V q' := by
  ext a b
  rw [@underlyingGraph_adj V q, @underlyingGraph_adj V q', ← nonempty_sum, ← nonempty_sum]
  exact and_congr_right fun _ ↦ h a b

end Quiver

end TauCeti
