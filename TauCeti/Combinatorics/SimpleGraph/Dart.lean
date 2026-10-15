/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Dart

/-!
# Darts with a fixed tail

The darts of a simple graph with tail `u` correspond to the neighbours of `u`: a dart is sent to
its head, and a neighbour `w` to the dart `u → w` (`SimpleGraph.dartOfNeighborSet`).

## Main definitions

* `SimpleGraph.dartFstEquivNeighborSet`: the equivalence between the darts with tail `u` and the
  neighbour set of `u`.
-/

@[expose] public section

namespace TauCeti

variable {V : Type*} {G : SimpleGraph V}

/-- The darts with tail `u` are the neighbours of `u`: a dart is sent to its head. -/
def _root_.SimpleGraph.dartFstEquivNeighborSet (u : V) :
    {d : G.Dart // d.fst = u} ≃ G.neighborSet u where
  toFun d := ⟨d.1.snd, (G.mem_neighborSet _ _).2 (Eq.mp (congrArg (G.Adj · d.1.snd) d.2) d.1.adj)⟩
  invFun w := ⟨G.dartOfNeighborSet u w, rfl⟩
  left_inv d := by
    obtain ⟨⟨⟨a, b⟩, h⟩, rfl⟩ := d
    rfl
  right_inv _ := rfl

/-- The neighbour attached to a dart with tail `u` is its head. -/
@[simp]
theorem _root_.SimpleGraph.coe_dartFstEquivNeighborSet_apply (u : V)
    (d : {d : G.Dart // d.fst = u}) :
    (G.dartFstEquivNeighborSet u d : V) = d.1.snd :=
  rfl

/-- The dart attached to a neighbour `w` of `u` is the dart `u → w`. -/
@[simp]
theorem _root_.SimpleGraph.coe_dartFstEquivNeighborSet_symm_apply (u : V) (w : G.neighborSet u) :
    ((G.dartFstEquivNeighborSet u).symm w : G.Dart) = G.dartOfNeighborSet u w :=
  rfl

end TauCeti
