/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.SeededRegularization
import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise

/-!
# An equitable regularity lemma for pair-color systems

Let `S` be a pair-color system with a finite palette on a finite vertex type `V`. For `ε > 0` and
`l ≤ |V|`, there is an equipartition of the vertices into at least `l` and at most
`equitablePairColorRegularityBound ε l` parts such that the ordered pairs `(A, B)` of distinct
parts that are not `ε`-regular for `S` cover at most `ε |V|²` ordered pairs of vertices
(`TauCeti.PairColorSystem.exists_equipartition_sum_irregularPairs_le`). The bound depends only on
`ε` and `l`. Regularity is coordinatewise, `TauCeti.PairColorSystem.IsRegularPair`, and colors
need not be symmetric. This is the equitable form of
`TauCeti.PairColorSystem.exists_refinement_sum_irregularPairs_le`, in the shape of Mathlib's
`szemeredi_regularity`. A regular lower skeleton over cells of equal size is what the
counting lemmas for colored three-graphs need, since equal cells make the repeated-cell
placements negligible.

The result follows from seed-preserving equitable regularity by choosing an initial
equipartition into `max l 1` parts. The empty host uses the singleton partition as its seed.
Refinement can only increase the number of parts.

## Main results

* `TauCeti.PairColorSystem.exists_equipartition_sum_irregularPairs_le`: the equitable regularity
  lemma.

## References

* E. Szemerédi, *Regular partitions of graphs* (1978).
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), where equitable vertex partitions with regular pair
  partitions underlie the regularity lemma for three-uniform hypergraphs.
* Y. Dillies and B. Mehta, *Formalising Szemerédi's Regularity Lemma in Lean*, ITP 2022: the
  statement shape and the use of `Finpartition.equitabilise` follow Mathlib's
  `szemeredi_regularity`.
-/

public section

open Finset Finpartition

namespace TauCeti.PairColorSystem

variable {κ V : Type*} [Fintype V] [DecidableEq V] (S : PairColorSystem κ V)

/-- **Equitable regularity lemma for pair-color systems.** For `ε > 0` and `l ≤ |V|`, there is an
equipartition of the vertices into at least `l` and at most `equitablePairColorRegularityBound ε l`
parts such that the ordered pairs `(A, B)` of distinct parts that are not `ε`-regular for `S`
cover at most `ε |V|²` ordered pairs of vertices. The bound depends only on `ε` and `l`. -/
theorem exists_equipartition_sum_irregularPairs_le [Finite κ] {ε : ℝ} (hε : 0 < ε) {l : ℕ}
    (hl : l ≤ Fintype.card V) :
    ∃ P : Finpartition (univ : Finset V), P.IsEquipartition ∧ l ≤ #P.parts ∧
      #P.parts ≤ equitablePairColorRegularityBound ε l ∧
      ∑ AB ∈ S.irregularPairs ε P, (#AB.1 * #AB.2 : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  by_cases hsize : max l 1 ≤ Fintype.card V
  · obtain ⟨P₀, hP₀, hcard⟩ := exists_equipartition_card_eq (univ : Finset V)
      (by positivity : max l 1 ≠ 0) (by rwa [card_univ])
    obtain ⟨P, hPP₀, hP, hbound, hgood⟩ :=
      S.exists_refining_equipartition_sum_irregularPairs_le P₀ hP₀ hε
    refine ⟨P, hP, (le_max_left l 1).trans (hcard ▸ card_mono hPP₀), ?_, hgood⟩
    simpa [hcard, equitablePairColorRegularityBound_def, max_assoc] using hbound
  · have hn : Fintype.card V = 0 := by omega
    have hl0 : l = 0 := by omega
    obtain ⟨P, -, hP, hbound, hgood⟩ := S.exists_refining_equipartition_sum_irregularPairs_le
      ⊥ (bot_isEquipartition _) hε
    refine ⟨P, hP, by omega, ?_, hgood⟩
    simpa [card_bot, card_univ, hn, hl0] using hbound

end TauCeti.PairColorSystem
