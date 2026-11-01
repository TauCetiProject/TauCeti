/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Triadic.CountingParameters
public import TauCeti.Combinatorics.Hypergraph.Triadic.ErrorDecomposition
public import TauCeti.Combinatorics.Hypergraph.Triadic.PlacedCounting
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Induced counting over a regular triadic complex

Let `C` be a triadic complex on `V` whose selected polyads decompose the injective triples, and
let `F` be a colored three-uniform pattern on `k = F.k` vertices. This file proves the induced
counting lemma for colorings of the triples of `V` that are approximated by a coloring `H'`
which is regular over `C`: the induced count of `F` in `H` is within `ε |V| ^ k` of the
prediction `H'.expectedInducedCount C F` computed from the cells, pair-color densities and
relative top densities of `H'` over `C`.

The regularity required is quantified by the host-independent parameters of
`TauCeti.Combinatorics.Hypergraph.Triadic.CountingParameters`:

* `H` approximates `H'` within `inducedCountingParameter3 k ε`: their edit discrepancy, six
  times the number of unordered triples on which they disagree divided by `|V| ^ 3`, is at most
  `inducedCountingParameter3 k ε`;
* the lower skeleton of `C` is regular for the schedule `inducedCountingSchedule3 k ε`, evaluated
  at the number of vertex cells plus the number of pair colors;
* `H'` is top-regular, at the tolerance `inducedCountingSchedule3 k ε C.complexity` and at a
  positive rank, over all polyads of `C` except an `inducedCountingParameter3 k ε` proportion
  of their support;
* the vertex cells of `C` form an equipartition into at least `diagonalControl3 k ε` cells.

Rank one suffices, so any positive rank is allowed. The error is split into six charges, each
at most `ε / 6` times `|V| ^ k`: the local counting errors along top-regular routes of
transversal placements, the actual and the predicted copies through exceptional polyads, the
pair-counting error inside the exceptional prediction, the nontransversal placements, and the
edit from `H` to `H'`.

## Main results

* `TauCeti.Colored3Graph.abs_placedInducedCopyCount_sub_expectedInducedCountAt_le_routeBudget3`:
  at the counting schedule, the placed count along a top-regular route of a transversal
  placement is within the per-route budget `routeBudget3 C k (ε / 6)` times the cell-size product
  of its prediction.
* `TauCeti.Colored3Graph.abs_inducedCopyCount_sub_expectedInducedCount_le_of_topRegular`: the
  induced counting lemma over a regular triadic complex, with error `ε |V| ^ k`.

## References

* B. Nagle, V. Rödl and M. Schacht, *The counting lemma for regular k-uniform hypergraphs*,
  Random Structures Algorithms 28 (2006).
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: counting lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset

namespace TauCeti

namespace Colored3Graph

variable {κ V : Type*} [DecidableEq κ] [Fintype V] [DecidableEq V] {C : TriadicComplex3 V}
  {F : FiniteColored3Pattern κ} {H H' : Colored3Graph κ V}

/-- **Local induced counting at the counting schedule.** Let `φ` be a transversal placement of a
pattern `F` on `k` vertices into a triadic complex `C` whose lower skeleton is regular for the
schedule `inducedCountingSchedule3 k ε`, and let `ψ` be a route over `φ` along which `H` is
top-regular at tolerance `inducedCountingSchedule3 k ε C.complexity` and a positive rank. Then the
placed count of `F` in `H` differs from its prediction by at most the per-route budget
`routeBudget3 C k (ε / 6)` times the cell-size product. -/
theorem abs_placedInducedCopyCount_sub_expectedInducedCountAt_le_routeBudget3
    {φ : PatternPlacement3 C F} (hφ : φ.Transversal) {ψ : PairColorPlacement3 φ} {ε : ℝ}
    (hε : 0 ≤ ε) (hlower : C.skeleton.LowerSkeletonRegular (inducedCountingSchedule3 F.k ε))
    {r : ℕ} (hr : 1 ≤ r)
    (hroute : ψ.IsTopRegularRoute H (inducedCountingSchedule3 F.k ε C.complexity) r) :
    |(H.placedInducedCopyCount φ ψ : ℝ) - H.expectedInducedCountAt φ ψ| ≤
      routeBudget3 C F.k (ε / 6) * ∏ i, (#(φ.vertexCell i) : ℝ) := by
  set n := #C.skeleton.vertexPart.parts + C.pairColorCount
  have hreg : C.skeleton.IsPairColorRegular (inducedCountingSchedule3 F.k ε n) := by
    simpa [PairSkeleton3.lowerSkeletonRegular_iff, n] using hlower
  refine (abs_placedInducedCopyCount_sub_expectedInducedCountAt_le hφ hreg
    (hroute.of_rank_le hr)).trans (mul_le_mul_of_nonneg_right ?_
      (prod_nonneg fun _ _ ↦ Nat.cast_nonneg _))
  have hpair := choose_mul_inducedCountingSchedule3_le_routeBudget3 C F.k one_le_two
    (by norm_num) hε (n := n) (Nat.le_add_left _ _)
  have htop := choose_mul_inducedCountingSchedule3_le_routeBudget3 C F.k (by norm_num) le_rfl
    hε C.pairColorCount_le_complexity
  have hbudget : routeBudget3 C F.k (ε / 6) = 2 * routeBudget3 C F.k (ε / 12) := by
    rw [routeBudget3_def, routeBudget3_def]
    ring
  linarith

/-- **Induced counting over a regular triadic complex.** Let `C` be a polyad decomposition on
`V`, let `F` be a pattern on `k` vertices, and let `0 < ε`. Suppose that

* `H` approximates `H'` within `inducedCountingParameter3 k ε`,
* the lower skeleton of `C` is regular for the schedule `inducedCountingSchedule3 k ε`,
* `H'` is top-regular, at tolerance `inducedCountingSchedule3 k ε C.complexity` and a positive
  rank `r`, over all polyads of `C` except an `inducedCountingParameter3 k ε` proportion, and
* the vertex cells of `C` form an equipartition into at least `diagonalControl3 k ε` cells.

Then the induced count of `F` in `H` differs from the prediction `H'.expectedInducedCount C F` by
at most `ε |V| ^ k`. -/
theorem abs_inducedCopyCount_sub_expectedInducedCount_le_of_topRegular
    (hC : C.IsPolyadDecomposition) {ε : ℝ} (hε : 0 < ε)
    (hedit : H.Approximates3 H' (inducedCountingParameter3 F.k ε))
    (hlower : C.skeleton.LowerSkeletonRegular (inducedCountingSchedule3 F.k ε))
    {r : ℕ} (hr : 1 ≤ r)
    (htop : H'.TopRegularOverMostPolyads C (inducedCountingSchedule3 F.k ε C.complexity)
      (inducedCountingParameter3 F.k ε) r)
    (hcells : C.VertexCellsControlled (diagonalControl3 F.k ε)) :
    |(H.inducedCopyCount F : ℝ) - H'.expectedInducedCount C F| ≤
      ε * (Fintype.card V : ℝ) ^ F.k := by
  set n := #C.skeleton.vertexPart.parts + C.pairColorCount
  have hn : C.pairColorCount ≤ n := Nat.le_add_left _ _
  have hreg : C.skeleton.IsPairColorRegular (inducedCountingSchedule3 F.k ε n) := by
    simpa [PairSkeleton3.lowerSkeletonRegular_iff, n] using hlower
  have hmain := abs_inducedCopyCount_sub_expectedInducedCount_le_of_placed_le (H := H)
    (H' := H') hC (inducedCountingSchedule3_nonneg F.k hε.le n) hreg hε hcells
    (routeBudget3_nonneg C F.k (by positivity : (0 : ℝ) ≤ ε / 6)) fun _ hφ _ hψ ↦
      abs_placedInducedCopyCount_sub_expectedInducedCountAt_le_routeBudget3 hφ hε.le hlower hr hψ
  -- The six charges: edits, local counting, actual and predicted exceptional copies,
  -- pair counting inside the exceptional prediction, and nontransversal placements.
  have hedit' : (F.k.choose 3 : ℝ) * H.editDiscrepancy3 H' ≤ ε / 6 :=
    (mul_le_mul_of_nonneg_left ((approximates3_iff H H' _).1 hedit) (Nat.cast_nonneg _)).trans
      (inducedCountingParameter3_choose_charge F.k hε.le)
  have hlocal := routeBudget3_charge C F.k (by positivity : (0 : ℝ) ≤ ε / 6)
  have hmass : (F.k.choose 3 : ℝ) *
      H'.exceptionalPolyadMass C (inducedCountingSchedule3 F.k ε C.complexity) r ≤ ε / 6 :=
    (mul_le_mul_of_nonneg_left (topRegularOverMostPolyads_iff.1 htop) (Nat.cast_nonneg _)).trans
      (inducedCountingParameter3_choose_charge F.k hε.le)
  have hpair := pairColorCount_pow_mul_choose_two_mul_inducedCountingSchedule3_le C F.k hε.le hn
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  linarith

end Colored3Graph

end TauCeti
