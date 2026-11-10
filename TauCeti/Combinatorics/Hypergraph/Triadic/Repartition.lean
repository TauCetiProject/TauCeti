/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Repartition
public import TauCeti.Combinatorics.Hypergraph.Triadic.PairRecoloring

/-!
# Top regularity after rebalancing vertex cells

Match the cells of two triadic complexes injectively, and likewise their pair palettes.
Suppose every vertex outside `B` remains in its matched cell and every ordered pair outside
`E` retains its mapped color. Top regularity over most polyads survives this change: the
exceptional support proportion increases by at most

`(1 + 2 / η) (3 |B| |V|² + 3 |E| |V|) / (|V|)₃`,

provided the old and new regularity tolerances satisfy `δ + 2η + η / ε ≤ ε`.
The denominator is the number of ordered injective triples, not `|V|³`.

In particular, rebalancing the vertex partition without changing pair colors costs only the
vertex term (`E = ∅`). Equitability is not needed for this stability estimate; a bound on the
vertices leaving their matched cells is enough. Neither a bound on individual cell losses nor
a factor depending on the number of polyads is required.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), the padding-and-rebalancing setting.
-/

public section

open Finset

namespace TauCeti.Colored3Graph

variable {κ V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]
  {H : Colored3Graph κ V} {C D : TriadicComplex3 V} {δ ε η ε₀ : ℝ} {r : ℕ}

/-- Top regularity over most polyads survives moving the vertices of `B` out of their matched
cells and recoloring the ordered pairs of `E`. The matchings of cells and palettes need only
be injective. Empty hosts and repeated vertex cells in polyads are allowed. -/
theorem TopRegularOverMostPolyads.of_repartition
    (h : H.TopRegularOverMostPolyads C δ ε₀ r) (hC : C.IsPolyadDecomposition)
    (hD : D.IsPolyadDecomposition)
    (f : C.skeleton.vertexPart.parts ↪ D.skeleton.vertexPart.parts)
    (g : Fin C.pairColorCount ↪ Fin D.pairColorCount)
    (B : Finset V) (E : Finset {p : V × V // p.1 ≠ p.2})
    (hcell : ∀ v ∉ B, v ∈ (f ⟨C.skeleton.vertexPart.part v,
      C.skeleton.vertexPart.part_mem.2 (mem_univ _)⟩).val)
    (hcolor : ∀ p ∉ E, D.skeleton.pairColors.color p = g (C.skeleton.pairColors.color p))
    (hε : 0 < ε) (hη : 0 < η) (hbudget : δ + 2 * η + η / ε ≤ ε) :
    H.TopRegularOverMostPolyads D ε
      (ε₀ + (1 + 2 / η) *
        (3 * #B * Fintype.card V ^ 2 + 3 * #E * Fintype.card V : ℕ) /
          (Fintype.card V).descFactorial 3) r := by
  rw [topRegularOverMostPolyads_iff] at h ⊢
  refine (exceptionalPolyadMass_le_of_injective hC hD
    (Polyad3.mapData_injective f.injective g.injective) hε hη hbudget).trans
      (add_le_add h ?_)
  -- The density import changes the side goals of bare `gcongr`; stop at the cardinal
  -- comparison explicitly so the proof is independent of automatic positivity discharge.
  gcongr (1 + 2 / η) * ?_ / _
  exact_mod_cast Polyad3.card_filter_ofTriple_ne_mapData_ofTriple_le f g B E hcell hcolor

end TauCeti.Colored3Graph
