/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import TauCeti.KnotTheory.Grid.DifferentialSupport

/-!
# Cardinality bounds for the fully blocked grid differential support

The fully blocked grid differential is already known to be supported on the
column-swap neighbours of a grid state. This file makes that computability statement
quantitative: those neighbours are the image of Mathlib's off-diagonal finite set of
ordered distinct column pairs, so each generator has at most `n * (n - 1)` possible
targets.

The same estimate extends to arbitrary finitely supported chains by taking the finite
union of the neighbour sets attached to the input support. These bounds are the
finite-row bookkeeping needed before the `∂² = 0` rectangle-pairing proof and before
evaluating the fully blocked complex on small explicit grids.

## Main results

* `TauCeti.GridState.columnSwapNeighbors_eq_offDiag_image`: column-swap neighbours are
  the image of the off-diagonal of the column set.
* `TauCeti.GridState.card_columnSwapNeighbors_le`: at most `n * (n - 1)` neighbours.
* `TauCeti.GridDiagram.fullyBlockedDifferentialOnGenerator_support_card_le_mul_pred`:
  the same bound for the support of a differential row.
* `TauCeti.GridDiagram.fullyBlockedDifferential_support_subset_biUnion` and
  `TauCeti.GridDiagram.fullyBlockedDifferential_support_card_le`:
  support and cardinality bounds for the differential of an arbitrary chain.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`,
Lane G.3, "The complexes and `∂² = 0`", and for the roadmap's standing requirement that
the grid differential compute on explicit small grids. The column-transposition support
condition follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters
3 and 4.
-/

public section

namespace TauCeti

namespace GridState

variable {n : ℕ} (x : GridState n)

/-- The finite set of column-swap neighbours is the image of the off-diagonal of the
column set: an ordered pair of distinct columns gives the state obtained by swapping
those columns. -/
theorem columnSwapNeighbors_eq_offDiag_image :
    x.columnSwapNeighbors =
      (Finset.univ : Finset (Fin n)).offDiag.image fun p => x.swapColumns p.1 p.2 := by
  ext y
  simp [columnSwapNeighbors, Finset.mem_offDiag]

/-- The off-diagonal of the column set has cardinality `n * (n - 1)`. This counts
ordered pairs of distinct columns. -/
theorem card_univ_offDiag_fin :
    ((Finset.univ : Finset (Fin n)).offDiag).card = n * (n - 1) := by
  rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
  calc
    n * n - n = n * n - n * 1 := by rw [Nat.mul_one]
    _ = n * (n - 1) := (Nat.mul_sub_left_distrib n n 1).symm

/-- A grid state has at most `n * (n - 1)` column-swap neighbours.

The bound counts ordered pairs of distinct columns. It is deliberately an upper bound,
because the two orders of a pair produce the same column transposition. -/
theorem card_columnSwapNeighbors_le : x.columnSwapNeighbors.card ≤ n * (n - 1) := by
  rw [x.columnSwapNeighbors_eq_offDiag_image, ← card_univ_offDiag_fin (n := n)]
  exact Finset.card_image_le

/-- A grid state on a grid of size `0` has no column-swap neighbours. -/
@[simp]
theorem columnSwapNeighbors_eq_empty_of_zero (x : GridState 0) :
    x.columnSwapNeighbors = ∅ := by
  apply Finset.card_eq_zero.mp
  exact Nat.eq_zero_of_le_zero (by simpa using x.card_columnSwapNeighbors_le)

/-- A grid state on a grid of size `1` has no column-swap neighbours. -/
@[simp]
theorem columnSwapNeighbors_eq_empty_of_one (x : GridState 1) :
    x.columnSwapNeighbors = ∅ := by
  apply Finset.card_eq_zero.mp
  exact Nat.eq_zero_of_le_zero (by simpa using x.card_columnSwapNeighbors_le)

end GridState

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The support of the fully blocked differential of one generator has at most
`n * (n - 1)` states. This is the quantitative form of the column-transposition
support theorem. -/
theorem fullyBlockedDifferentialOnGenerator_support_card_le_mul_pred (x : GridState n) :
    (G.fullyBlockedDifferentialOnGenerator x).support.card ≤ n * (n - 1) :=
  (G.fullyBlockedDifferentialOnGenerator_support_card_le x).trans x.card_columnSwapNeighbors_le

/-- The support of the fully blocked differential of one generator is empty in grid
size `0`. -/
theorem fullyBlockedDifferentialOnGenerator_support_eq_empty_of_zero (G : GridDiagram 0)
    (x : GridState 0) :
    (G.fullyBlockedDifferentialOnGenerator x).support = ∅ := by
  apply Finset.card_eq_zero.mp
  exact Nat.eq_zero_of_le_zero
    (by simpa using G.fullyBlockedDifferentialOnGenerator_support_card_le_mul_pred x)

/-- The support of the fully blocked differential of one generator is empty in grid
size `1`. -/
theorem fullyBlockedDifferentialOnGenerator_support_eq_empty_of_one (G : GridDiagram 1)
    (x : GridState 1) :
    (G.fullyBlockedDifferentialOnGenerator x).support = ∅ := by
  apply Finset.card_eq_zero.mp
  exact Nat.eq_zero_of_le_zero
    (by simpa using G.fullyBlockedDifferentialOnGenerator_support_card_le_mul_pred x)

/-- The fully blocked differential of a generator is zero in grid size `0`. -/
@[simp]
theorem fullyBlockedDifferentialOnGenerator_eq_zero_of_zero (G : GridDiagram 0)
    (x : GridState 0) :
    G.fullyBlockedDifferentialOnGenerator x = 0 :=
  Finsupp.support_eq_empty.mp (G.fullyBlockedDifferentialOnGenerator_support_eq_empty_of_zero x)

/-- The fully blocked differential of a generator is zero in grid size `1`. -/
@[simp]
theorem fullyBlockedDifferentialOnGenerator_eq_zero_of_one (G : GridDiagram 1)
    (x : GridState 1) :
    G.fullyBlockedDifferentialOnGenerator x = 0 :=
  Finsupp.support_eq_empty.mp (G.fullyBlockedDifferentialOnGenerator_support_eq_empty_of_one x)

/-- The support of the fully blocked differential of a chain is contained in the union
of the column-swap neighbour sets of the states appearing in the input chain. -/
theorem fullyBlockedDifferential_support_subset_biUnion (c : GridChain (ZMod 2) n) :
    (G.fullyBlockedDifferential c).support ⊆
      c.support.biUnion fun x : GridState n => x.columnSwapNeighbors := by
  rw [fullyBlockedDifferential_apply]
  refine Finsupp.support_sum.trans ?_
  intro y hy
  rw [Finset.mem_biUnion] at hy ⊢
  obtain ⟨x, hx, hyx⟩ := hy
  refine ⟨x, hx, ?_⟩
  exact G.fullyBlockedDifferentialOnGenerator_support_subset x (Finsupp.support_smul hyx)

/-- The support of the fully blocked differential of an arbitrary chain has cardinality
at most the size of the input support times `n * (n - 1)`. -/
theorem fullyBlockedDifferential_support_card_le (c : GridChain (ZMod 2) n) :
    (G.fullyBlockedDifferential c).support.card ≤ c.support.card * (n * (n - 1)) :=
  (Finset.card_le_card (G.fullyBlockedDifferential_support_subset_biUnion c)).trans
    (Finset.card_biUnion_le_card_mul c.support (fun x : GridState n => x.columnSwapNeighbors)
      (n * (n - 1)) fun x _ => x.card_columnSwapNeighbors_le)

/-- The fully blocked differential is zero on every chain in grid size `0`. -/
theorem fullyBlockedDifferential_eq_zero_of_zero (G : GridDiagram 0) :
    G.fullyBlockedDifferential = (0 : GridChain (ZMod 2) 0 →ₗ[ZMod 2] GridChain (ZMod 2) 0) := by
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro y
  have hsupport : (G.fullyBlockedDifferential c).support = ∅ := by
    apply Finset.card_eq_zero.mp
    exact Nat.eq_zero_of_le_zero (by simpa using G.fullyBlockedDifferential_support_card_le c)
  exact Finsupp.notMem_support_iff.mp (by rw [hsupport]; simp)

/-- The fully blocked differential is zero on every chain in grid size `1`. -/
theorem fullyBlockedDifferential_eq_zero_of_one (G : GridDiagram 1) :
    G.fullyBlockedDifferential = (0 : GridChain (ZMod 2) 1 →ₗ[ZMod 2] GridChain (ZMod 2) 1) := by
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro y
  have hsupport : (G.fullyBlockedDifferential c).support = ∅ := by
    apply Finset.card_eq_zero.mp
    exact Nat.eq_zero_of_le_zero (by simpa using G.fullyBlockedDifferential_support_card_le c)
  exact Finsupp.notMem_support_iff.mp (by rw [hsupport]; simp)

end GridDiagram

end TauCeti
