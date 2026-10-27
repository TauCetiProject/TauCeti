/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Combinatorics.SimpleGraph.Operations
import TauCeti.Combinatorics.Regularity.Graph.InducedCount

/-!
# Regression examples: labelled induced three-vertex counts

These examples compute `SimpleGraph.inducedGraphCount3` on three-vertex hosts, through public
statements only. They test the nonedge conditions and the labelled-count convention:

* the edgeless pattern has no induced copy in the complete graph, since nonedges must go to
  nonedges;
* the triangle has `6` labelled induced copies in itself, one for each automorphism;
* one edge plus an isolated vertex has `2` labelled induced copies in itself: the isolated vertex
  is fixed and the edge may be flipped.
-/

open SimpleGraph

-- The edgeless pattern has no induced copy in the complete graph on three vertices.
example : (⊥ : SimpleGraph (Fin 3)).inducedGraphCount3 (⊤ : SimpleGraph (Fin 3)) = 0 := by
  rw [inducedGraphCount3_def]
  decide

-- The triangle has six labelled induced copies in itself.
example : (⊤ : SimpleGraph (Fin 3)).inducedGraphCount3 (⊤ : SimpleGraph (Fin 3)) = 6 := by
  rw [inducedGraphCount3_def]
  decide

-- The same count, read through the graph embeddings of the triangle into itself.
example : Fintype.card ((⊤ : SimpleGraph (Fin 3)) ↪g (⊤ : SimpleGraph (Fin 3))) = 6 := by
  rw [← inducedGraphCount3_eq_card_embedding, inducedGraphCount3_def]
  decide

-- One edge plus an isolated vertex has two labelled induced copies in itself. Mathlib's
-- decidability instance for `edge` does not reduce, so a reducing one is used for the count.
example : (edge (0 : Fin 3) 1).inducedGraphCount3 (edge (0 : Fin 3) 1) = 2 := by
  let _ : DecidableRel (edge (0 : Fin 3) 1).Adj := fun v w ↦
    decidable_of_iff _ (edge_adj 0 1 v w).symm
  convert (by rw [inducedGraphCount3_def]; decide :
    (edge (0 : Fin 3) 1).inducedGraphCount3 (edge (0 : Fin 3) 1) = 2)
