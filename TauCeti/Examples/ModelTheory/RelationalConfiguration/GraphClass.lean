/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Combinatorics.SimpleGraph.Operations
import TauCeti.ModelTheory.RelationalConfiguration.GraphClass

/-!
# Examples of codes of simple graphs

The code of the empty graph on `ℕ` lies in `graphClass`; a code with `adj(0, 0)`, or with
`adj(0, 1)` but not `adj(1, 0)`, does not. The codes of the one-edge graphs on `{0, 1}` and on
`{5, 7}` are isomorphic, and the code of the one-edge graph is not isomorphic to that of the path
`0 - 1 - 2`.
-/

open FirstOrder FirstOrder.Language TauCeti RelationalConfiguration

-- The code of the empty graph is a code of a simple graph.
example : (⊥ : SimpleGraph ℕ).toRelationalConfiguration ∈ graphClass := by
  simp

-- A code with `adj(0, 0)` is not.
example : adjArrayEquiv.symm (fun p => decide (p = (0, 0))) ∉ graphClass := fun h => by
  simpa using (isSimpleGraph_iff.1 (mem_graphClass.1 h)).2 0

-- A code with `adj(0, 1)` but not `adj(1, 0)` is not.
example : adjArrayEquiv.symm (fun p => decide (p = (0, 1))) ∉ graphClass := fun h => by
  simpa using (isSimpleGraph_iff.1 (mem_graphClass.1 h)).1 0 1

-- The codes of the one-edge graphs on `{0, 1}` and on `{5, 7}` are isomorphic.
example : isoSetoid Language.graph ℕ (SimpleGraph.edge 0 1).toRelationalConfiguration
    (SimpleGraph.edge 5 7).toRelationalConfiguration := by
  refine isoSetoid_toRelationalConfiguration_iff.2
    ⟨⟨(Equiv.swap 1 7).trans (Equiv.swap 0 5), fun {a b} => ?_⟩⟩
  simp only [Equiv.trans_apply, SimpleGraph.edge_adj, Equiv.swap_apply_def]
  grind

-- The code of the one-edge graph is not isomorphic to that of the path `0 - 1 - 2`: in the path,
-- `1` has the two neighbours `0` and `2`.
example : ¬isoSetoid Language.graph ℕ (SimpleGraph.edge 0 1).toRelationalConfiguration
    (SimpleGraph.edge 0 1 ⊔ SimpleGraph.edge 1 2).toRelationalConfiguration := by
  rw [isoSetoid_toRelationalConfiguration_iff]
  rintro ⟨f⟩
  have h0 : (SimpleGraph.edge 0 1).Adj (f.symm 1) (f.symm 0) :=
    f.symm.map_adj_iff.2 (by simp [SimpleGraph.edge_adj])
  have h2 : (SimpleGraph.edge 0 1).Adj (f.symm 1) (f.symm 2) :=
    f.symm.map_adj_iff.2 (by simp [SimpleGraph.edge_adj])
  have hne : f.symm 0 ≠ f.symm 2 := fun h => by simpa using f.symm.injective h
  simp only [SimpleGraph.edge_adj] at h0 h2
  omega
