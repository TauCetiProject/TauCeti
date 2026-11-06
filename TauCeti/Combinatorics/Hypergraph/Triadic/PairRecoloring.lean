/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Coarsening
public import TauCeti.Combinatorics.Hypergraph.Polyad.SupportStability
public import TauCeti.Combinatorics.Hypergraph.Triadic.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-!
# Exceptional polyad mass after recoloring the pairs

A regular lower skeleton can be obtained from an arbitrary one by recoloring some of its pairs,
for instance the pairs inside the vertex cells and those between cells forming an irregular pair.
This file shows that a coloring `H` of the triples stays top-regular over most polyads of the
recolored skeleton, provided few pairs are recolored.

Fix lower skeletons `S` and `T` and an injective map `f` from polyads over `S` to polyads over
`T`. A triple is *moved* if its polyad over `T` is not the image under `f` of its polyad
over `S`. The support of the irregular polyads over `T` is at most that over `S` plus
`(1 + 2 / η)` times the number of moved triples
(`Colored3Graph.sum_card_support_not_isTopRegularOverPolyad_le_of_injective` in
`Polyad/SupportStability.lean`).

When `T` has the vertex cells of `S` and its pair colors are obtained by an injective map `g`
except on a set `E` of ordered pairs, taking `f P` to be the polyad with the same cells and the
colors mapped by `g` moves at most `3 |E| |V|` triples
(`Polyad3.card_filter_ofTriple_ne_coarsen_ofTriple_le` in `Polyad/Coarsening.lean`). The new
pair palette may be larger, for example by a fresh color for the pairs inside the cells. For
polyad decompositions of triadic complexes this yields
`Colored3Graph.TopRegularOverMostPolyads.of_pairRecoloring`.

## Main results

* `TauCeti.Colored3Graph.exceptionalPolyadMass_le_of_injective`: the exceptional mass of
  polyad decompositions grows by at most a multiple of the proportion of moved triples.
* `TauCeti.Colored3Graph.TopRegularOverMostPolyads.of_pairRecoloring`: top regularity over
  most polyads survives recoloring few pairs of the lower skeleton.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset

namespace TauCeti

variable {κ V : Type*} [Fintype V] [DecidableEq V]

namespace Colored3Graph

variable [DecidableEq κ] {H : Colored3Graph κ V} {δ ε η : ℝ} {r : ℕ}

open Classical in
/-- **Exceptional mass after recoloring the pairs.** For polyad decompositions `C` and `D` and
an injective map `f` from polyads over the skeleton of `C` to polyads over that of `D`,
the exceptional mass grows by at most `(1 + 2 / η)` times the proportion of moved triples among
all `|V| (|V| - 1) (|V| - 2)` injective triples, when `δ + 2η + η / ε ≤ ε`. -/
theorem exceptionalPolyadMass_le_of_injective {C D : TriadicComplex3 V}
    (hC : C.IsPolyadDecomposition) (hD : D.IsPolyadDecomposition)
    {f : Polyad3 C.skeleton → Polyad3 D.skeleton} (hf : Function.Injective f)
    (hε : 0 < ε) (hη : 0 < η) (hbudget : δ + 2 * η + η / ε ≤ ε) :
    H.exceptionalPolyadMass D ε r ≤ H.exceptionalPolyadMass C δ r +
      (1 + 2 / η) * #{x | Polyad3.ofTriple D.skeleton x ≠ f (Polyad3.ofTriple C.skeleton x)} /
        (Fintype.card V).descFactorial 3 := by
  rw [exceptionalPolyadMass_eq_sum_div hD, exceptionalPolyadMass_eq_sum_div hC, ← add_div]
  exact div_le_div_of_nonneg_right
    (sum_card_support_not_isTopRegularOverPolyad_le_of_injective hf hε hη hbudget)
    (Nat.cast_nonneg _)

/-- **Top regularity after recoloring few pairs.** Let `C` and `D` be polyad decompositions on
the same vertex cells, and suppose the pair colors of `D` are those of `C` mapped by an injective
`g`, except on a set `E` of ordered pairs. If `H` is `(δ, r)`-top-regular over all but an
`ε₀`-proportion of the polyads of `C`, then it is `(ε, r)`-top-regular over all but an
`ε₀ + (1 + 2 / η) 3 |E| |V| / (|V| (|V| - 1) (|V| - 2))`-proportion of those of `D`, provided
`δ + 2η + η / ε ≤ ε`. -/
theorem TopRegularOverMostPolyads.of_pairRecoloring {C D : TriadicComplex3 V} {ε₀ : ℝ}
    (h : H.TopRegularOverMostPolyads C δ ε₀ r) (hC : C.IsPolyadDecomposition)
    (hD : D.IsPolyadDecomposition) (hV : C.skeleton.vertexPart = D.skeleton.vertexPart)
    {g : Fin C.pairColorCount → Fin D.pairColorCount} (hg : Function.Injective g)
    (hε : 0 < ε) (hη : 0 < η) (hbudget : δ + 2 * η + η / ε ≤ ε) :
    H.TopRegularOverMostPolyads D ε (ε₀ + (1 + 2 / η) *
      (3 * #{p | D.skeleton.pairColors.color p ≠ g (C.skeleton.pairColors.color p)} *
        Fintype.card V : ℕ) / (Fintype.card V).descFactorial 3) r := by
  rw [topRegularOverMostPolyads_iff] at h ⊢
  refine (exceptionalPolyadMass_le_of_injective hC hD (Polyad3.coarsen_injective hV hg)
    hε hη hbudget).trans (add_le_add h ?_)
  gcongr
  exact Polyad3.card_filter_ofTriple_ne_coarsen_ofTriple_le hV.le g

end Colored3Graph

end TauCeti
