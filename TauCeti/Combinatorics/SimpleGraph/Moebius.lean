/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Finite
public import TauCeti.Data.Finset.Basic
public import Mathlib.Data.Matrix.Mul

/-!
# The Möbius function of the lattice of graphs on a fixed vertex set

The simple graphs on a finite vertex set `V` form a Boolean lattice, isomorphic through the edge
set to the lattice of subsets of the non-diagonal pairs `Sym2 V`.  Its Möbius function is therefore
the signed count `(-1)^{e(H) - e(F)}` on an interval `[F, H]`, where `e(·)` counts edges.  The two
lemmas here are the cancellation laws that drive Möbius inversion over graphs, as in the transform
between a graph parameter and its "contains exactly" coefficients.

## Main results

* `SimpleGraph.sum_neg_one_pow_ncard_edgeSet_sub_left` — the signed sum
  `∑_{F ≤ G ≤ H} (-1)^{e(G) - e(F)}` is `1` if `F = H` and `0` otherwise;
* `SimpleGraph.sum_neg_one_pow_ncard_edgeSet_sub_right` — the same for `(-1)^{e(H) - e(G)}`.

They are the graph counterparts of `Finset.sum_Icc_neg_one_pow_card_sub_card_left` and
`Finset.sum_Icc_neg_one_pow_card_sub_card_right`, to which
`SimpleGraph.sum_filter_le_le_eq_sum_Icc_edgeFinset` identifies them.

In matrix form, the two cancellation laws say that the **zeta matrix** `Z(G, H) = [G ≤ H]` of the
lattice and its **Möbius matrix** `M(G, H) = [G ≤ H] (-1)^{e(H) - e(G)}` are inverse to each other,
on either side.  Expanding a function of graphs in the "contains" basis is multiplication by `Z`,
and recovering its "contains exactly" coefficients is multiplication by `M`.

## Main definitions

* `SimpleGraph.zetaMatrix` — the zeta matrix of the lattice of graphs on `V`;
* `SimpleGraph.mobiusMatrix` — its Möbius matrix.

## Main results

* `SimpleGraph.mobiusMatrix_mul_zetaMatrix` and `SimpleGraph.zetaMatrix_mul_mobiusMatrix` — the two
  matrices are inverse to each other.
-/

public section

open Finset

namespace SimpleGraph

variable {V R : Type*} [Fintype V] [DecidableEq V] [Ring R]

/-- **The Möbius function of the lattice of graphs, measured from the bottom.** The signed sum
`∑_{F ≤ G ≤ H} (-1)^{e(G) - e(F)}` is `1` if `F = H` and `0` otherwise. -/
@[simp]
theorem sum_neg_one_pow_ncard_edgeSet_sub_left (F H : SimpleGraph V)
    [DecidablePred fun G : SimpleGraph V => F ≤ G ∧ G ≤ H] [Decidable (F = H)] :
    ∑ G with F ≤ G ∧ G ≤ H, (-1 : R) ^ (G.edgeSet.ncard - F.edgeSet.ncard) =
      if F = H then 1 else 0 := by
  classical
  simp only [← coe_edgeFinset, Set.ncard_coe_finset]
  rw [sum_filter_le_le_eq_sum_Icc_edgeFinset F H fun s => (-1 : R) ^ (#s - #F.edgeFinset),
    sum_Icc_neg_one_pow_card_sub_card_left]
  exact if_congr edgeFinset_inj rfl rfl

/-- **The Möbius function of the lattice of graphs, measured from the top.** The signed sum
`∑_{F ≤ G ≤ H} (-1)^{e(H) - e(G)}` is `1` if `F = H` and `0` otherwise. -/
@[simp]
theorem sum_neg_one_pow_ncard_edgeSet_sub_right (F H : SimpleGraph V)
    [DecidablePred fun G : SimpleGraph V => F ≤ G ∧ G ≤ H] [Decidable (F = H)] :
    ∑ G with F ≤ G ∧ G ≤ H, (-1 : R) ^ (H.edgeSet.ncard - G.edgeSet.ncard) =
      if F = H then 1 else 0 := by
  classical
  simp only [← coe_edgeFinset, Set.ncard_coe_finset]
  rw [sum_filter_le_le_eq_sum_Icc_edgeFinset F H fun s => (-1 : R) ^ (#H.edgeFinset - #s),
    sum_Icc_neg_one_pow_card_sub_card_right]
  exact if_congr edgeFinset_inj rfl rfl

/-! ### The zeta and Möbius matrices -/

section Matrix

omit [Ring R] in
variable (V R) [Zero R] [One R] in
open Classical in
/-- The **zeta matrix** of the lattice of graphs on `V`: its `(G, H)` entry is `1` when `G ≤ H` and
`0` otherwise. -/
noncomputable def zetaMatrix : Matrix (SimpleGraph V) (SimpleGraph V) R :=
  Matrix.of fun G H => if G ≤ H then 1 else 0

variable (V R) in
open Classical in
/-- The **Möbius matrix** of the lattice of graphs on `V`: its `(G, H)` entry is the Möbius function
`(-1)^{e(H) - e(G)}` of the interval `[G, H]` when `G ≤ H`, and `0` otherwise.  It is the inverse
of `SimpleGraph.zetaMatrix`. -/
noncomputable def mobiusMatrix : Matrix (SimpleGraph V) (SimpleGraph V) R :=
  Matrix.of fun G H => if G ≤ H then (-1) ^ (H.edgeSet.ncard - G.edgeSet.ncard) else 0

omit [Fintype V] [DecidableEq V] [Ring R] in
variable [Zero R] [One R] in
/-- The entries of the zeta matrix. -/
@[simp]
theorem zetaMatrix_apply (G H : SimpleGraph V) [Decidable (G ≤ H)] :
    zetaMatrix V R G H = if G ≤ H then 1 else 0 := by
  simp only [zetaMatrix, Matrix.of_apply]
  congr

omit [Fintype V] [DecidableEq V] in
/-- The entries of the Möbius matrix. -/
@[simp]
theorem mobiusMatrix_apply (G H : SimpleGraph V) [Decidable (G ≤ H)] :
    mobiusMatrix V R G H = if G ≤ H then (-1) ^ (H.edgeSet.ncard - G.edgeSet.ncard) else 0 := by
  simp only [mobiusMatrix, Matrix.of_apply]
  congr

/-- **Möbius inversion, matrix form.** The Möbius matrix is a left inverse of the zeta matrix: this
is the cancellation law `SimpleGraph.sum_neg_one_pow_ncard_edgeSet_sub_left`. -/
@[simp]
theorem mobiusMatrix_mul_zetaMatrix [DecidableEq (SimpleGraph V)] :
    mobiusMatrix V R * zetaMatrix V R = 1 := by
  classical
  ext F H
  rw [Matrix.mul_apply, Matrix.one_apply, ← sum_neg_one_pow_ncard_edgeSet_sub_left F H, sum_filter]
  refine sum_congr rfl fun G _ => ?_
  rw [mobiusMatrix_apply, zetaMatrix_apply]
  by_cases hF : F ≤ G <;> by_cases hH : G ≤ H <;> simp [hF, hH]

/-- **Möbius inversion, matrix form.** The Möbius matrix is a right inverse of the zeta matrix: this
is the cancellation law `SimpleGraph.sum_neg_one_pow_ncard_edgeSet_sub_right`. -/
@[simp]
theorem zetaMatrix_mul_mobiusMatrix [DecidableEq (SimpleGraph V)] :
    zetaMatrix V R * mobiusMatrix V R = 1 := by
  classical
  ext F H
  rw [Matrix.mul_apply, Matrix.one_apply, ← sum_neg_one_pow_ncard_edgeSet_sub_right F H,
    sum_filter]
  refine sum_congr rfl fun G _ => ?_
  rw [mobiusMatrix_apply, zetaMatrix_apply]
  by_cases hF : F ≤ G <;> by_cases hH : G ≤ H <;> simp [hF, hH]

end Matrix

end SimpleGraph
