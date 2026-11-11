/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Triadic.PairRecoloring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-!
# Top regularity after moving vertices between matched cells

Rebalancing a vertex partition changes the cells while preserving pair colors up to injective
relabeling. Match the old cells injectively to the new cells, and suppose only vertices in `B`
leave their matched cell.
A triple whose polyad is not preserved must meet `B`, so at most `3 |B| |V|²` triples move.
Combining this count with support stability bounds the new irregular support by the old
irregular support plus `(1 + 2 / η) 3 |B| |V|²`, independently of the palette size.

The final theorem expresses this bound as top regularity over most polyads of the new
partition. No equitability is assumed: the estimate can be applied to the output of any
rebalancing construction with a bound on the moved vertex set. It includes repeated cells,
empty hosts, and arbitrary ranks, and does not change the triple coloring.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), the padding-and-rebalancing setting.
-/

public section

open Finset

namespace TauCeti.Colored3Graph

variable {κ V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]
  {H : Colored3Graph κ V} {δ ε η : ℝ} {r : ℕ}

/-- Top regularity over most polyads survives moving only the vertices of `B` between matched
cells of polyad decompositions `C` and `D`, with pair colors preserved up to an injective
relabeling `g`. The error charge is normalized by the original number of ordered injective
triples; when that number is zero, both exceptional masses and the charge are zero. -/
theorem TopRegularOverMostPolyads.of_vertexRepartition {C D : TriadicComplex3 V} {ε₀ : ℝ}
    (h : H.TopRegularOverMostPolyads C δ ε₀ r) (hC : C.IsPolyadDecomposition)
    (hD : D.IsPolyadDecomposition)
    (f : C.skeleton.vertexPart.parts ↪ D.skeleton.vertexPart.parts)
    {g : Fin C.pairColorCount → Fin D.pairColorCount} (hg : Function.Injective g)
    (hcolors : ∀ p, g (C.skeleton.pairColors.color p) = D.skeleton.pairColors.color p)
    (B : Finset V)
    (hcells : ∀ v ∉ B, (f ⟨C.skeleton.vertexPart.part v,
      C.skeleton.vertexPart.part_mem.2 (mem_univ _)⟩ : Finset V) = D.skeleton.vertexPart.part v)
    (hε : 0 < ε) (hη : 0 < η) (hbudget : δ + 2 * η + η / ε ≤ ε) :
    H.TopRegularOverMostPolyads D ε
      (ε₀ + (1 + 2 / η) * (3 * #B * (Fintype.card V : ℝ) ^ 2) /
        (Fintype.card V).descFactorial 3) r := by
  classical
  rw [topRegularOverMostPolyads_iff] at h ⊢
  refine (exceptionalPolyadMass_le_of_injective hC hD
    (Polyad3.map_injective f.injective hg)
    hε hη hbudget).trans (add_le_add h ?_)
  gcongr
  exact_mod_cast Polyad3.card_ofTriple_ne_map_le (S := C.skeleton) (T := D.skeleton)
    f g hcolors B hcells

end TauCeti.Colored3Graph
