/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Combinatorics.SimpleGraph.CutMinimal.Basic
public import TauCeti.Combinatorics.SimpleGraph.OddTriple.Counting

/-!
# Odd-triple count of small cut-minimal graphs

On a finite vertex type of cardinality at most four, every cut-minimal graph has maximum degree at
most `1` (`SimpleGraph.IsCutMinimal.degree_le_one_of_card_le_four`), so the number of `3`-vertex
subsets spanning an odd number of edges is `(Fintype.card V - 2) * #G.edgeFinset`
(`SimpleGraph.IsCutMinimal.card_oddTripleFinset_of_card_le_four`).
-/

public section

open Finset

namespace SimpleGraph

variable {V : Type*}

/-- On a vertex type of size at most four, a cut-minimal graph has
`(Fintype.card V - 2) * #G.edgeFinset` odd triples. -/
theorem IsCutMinimal.card_oddTripleFinset_of_card_le_four [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] [Fintype G.edgeSet]
    (hG : G.IsCutMinimal) (hV : Fintype.card V ≤ 4) :
    #G.oddTripleFinset = (Fintype.card V - 2) * #G.edgeFinset :=
  G.card_oddTripleFinset_of_degree_le_one fun v ↦ hG.degree_le_one_of_card_le_four hV v

end SimpleGraph
