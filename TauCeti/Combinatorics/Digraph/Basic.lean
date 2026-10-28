/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Digraph.Basic

/-!
# Induced digraphs

The digraph `D.induce S` induced by a digraph `D` on a set `S` of its vertices has the vertices of
`S`, two of which are adjacent exactly when they are adjacent in `D`. Inducing on the complement
of a set of vertices deletes those vertices.

## Main definitions

* `Digraph.induce`: the digraph `D.induce S` induced by `D` on a set `S` of vertices.
-/

@[expose] public section

universe u

namespace Digraph

variable {V : Type u}

/-- The digraph induced by `D` on a set `S` of vertices: two vertices of `S` are adjacent when
they are adjacent in `D`. -/
def induce (D : Digraph V) (S : Set V) : Digraph S where
  Adj v w := D.Adj v w

@[simp]
theorem induce_adj {D : Digraph V} {S : Set V} {v w : S} : (D.induce S).Adj v w ↔ D.Adj v w :=
  Iff.rfl

end Digraph
