/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Triadic.Basic
import TauCeti.Combinatorics.Hypergraph.Polyad.Rank

/-!
# Amplifying top regularity from rank one on triadic complexes

This file lifts single-polyad rank amplification
(`Colored3Graph.IsTopRegularOverPolyad.of_rank_one`) to triadic complexes. Whenever `0 < δ` and
`2 ^ r * δ₁ ≤ δ ^ 2`, every `(δ₁, 1)`-top-regular polyad is `(δ, r)`-top-regular, so the
`(δ, r)`-exceptional polyad mass is at most the `(δ₁, 1)`-exceptional mass
(`Colored3Graph.exceptionalPolyadMass_le_of_rank_one`), and rank-one top regularity over most
polyads amplifies to rank `r` (`Colored3Graph.TopRegularOverMostPolyads.of_rank_one`).

## Main results

* `TauCeti.Colored3Graph.exceptionalPolyadMass_le_of_rank_one`: rank-`r` exceptional polyad mass
  is bounded by rank-one exceptional polyad mass when `2 ^ r * δ₁ ≤ δ ^ 2`.
* `TauCeti.Colored3Graph.TopRegularOverMostPolyads.of_rank_one`: rank-one top regularity over most
  polyads implies rank-`r` top regularity over most polyads.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset

namespace TauCeti.Colored3Graph

variable {κ V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]

/-- **Rank amplification for exceptional polyad mass.** Every polyad that is rank-one top-regular
at tolerance `δ₁` is rank-`r` top-regular at tolerance `δ` whenever `0 < δ` and
`2 ^ r * δ₁ ≤ δ ^ 2`, so the rank-`r` exceptional mass is at most the rank-one exceptional
mass. -/
theorem exceptionalPolyadMass_le_of_rank_one (H : Colored3Graph κ V)
    (C : TriadicComplex3 V) {δ₁ δ : ℝ} {r : ℕ}
    (hδ : 0 < δ) (hδε : (2 : ℝ) ^ r * δ₁ ≤ δ ^ 2) :
    H.exceptionalPolyadMass C δ r ≤ H.exceptionalPolyadMass C δ₁ 1 := by
  classical
  rw [exceptionalPolyadMass_def, exceptionalPolyadMass_def]
  refine div_le_div_of_nonneg_right (sum_le_sum_of_subset_of_nonneg ?_
    fun _ _ _ ↦ Nat.cast_nonneg _) (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
  intro P
  simp only [mem_filter]
  exact fun ⟨hP, hreg⟩ ↦ ⟨hP, fun h1 ↦ hreg (h1.of_rank_one hδ hδε)⟩

/-- **Rank amplification on a triadic complex.** Rank-one top regularity over most polyads at
tolerance `δ₁` implies rank-`r` top regularity over most polyads at tolerance `δ` whenever `0 < δ`
and `2 ^ r * δ₁ ≤ δ ^ 2`. -/
theorem TopRegularOverMostPolyads.of_rank_one {H : Colored3Graph κ V}
    {C : TriadicComplex3 V} {δ₁ δ ε : ℝ} {r : ℕ}
    (h : H.TopRegularOverMostPolyads C δ₁ ε 1) (hδ : 0 < δ) (hδε : (2 : ℝ) ^ r * δ₁ ≤ δ ^ 2) :
    H.TopRegularOverMostPolyads C δ ε r :=
  topRegularOverMostPolyads_iff.2
    ((H.exceptionalPolyadMass_le_of_rank_one C hδ hδε).trans (topRegularOverMostPolyads_iff.1 h))

end TauCeti.Colored3Graph
