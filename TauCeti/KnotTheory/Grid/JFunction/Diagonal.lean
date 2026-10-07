/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.JFunction.Center

/-!
# Pairing the diagonal state against markings

The diagonal grid state pairs against a marked square `(c, r)` with numerator
`min c r + 1 + (n - 1 - max c r)`. Reversing both square coordinates preserves this
number. Thus the diagonal state provides a normalization point for comparing Alexander
gradings under the half-turn of the torus.

The pairing convention is that of Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Section 4.3: states occupy grid points and markings occupy square centers.
-/

public section

namespace TauCeti.GridState

variable {n : ℕ}

/-- The marking-pairing numerator of the diagonal state is the sum of the numbers of diagonal
points weakly southwest and strictly northeast of each marking. -/
theorem JNumCenter_diagonal_pointSet_eq_sum (m : GridState n) :
    GridPoint.JNumCenter (GridState.mk 1).pointSet m.pointSet =
      ∑ c : Fin n, ((min c (m c) : Fin n).val + 1 +
        (n - 1 - (max c (m c) : Fin n).val)) := by
  have hdiag (c : Fin n) : (GridState.mk 1 : GridState n) c = c := rfl
  rw [JNumCenter_pointSet_eq_card]
  simp_rw [hdiag]
  rw [Finset.card_filter, Finset.card_filter, Fintype.sum_prod_type,
    Fintype.sum_prod_type]
  dsimp only
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hle : (Finset.univ.filter fun d : Fin n => d ≤ c ∧ d ≤ m c) =
      Finset.Iic (min c (m c)) := by ext d; simp
  have hlt : (Finset.univ.filter fun d : Fin n => c < d ∧ m c < d) =
      Finset.Ioi (max c (m c)) := by ext d; simp [max_lt_iff]
  rw [← Finset.card_filter, ← Finset.card_filter, hle, hlt, Fin.card_Iic, Fin.card_Ioi]

/-- Reversing the marking-square coordinates preserves their pairing with the diagonal state.
This concerns the diagonal state only, not simultaneous coordinate reversal of arbitrary
states and markings. -/
theorem JNumCenter_diagonal_rotate (m : GridState n) :
    GridPoint.JNumCenter (GridState.mk 1).pointSet m.rotate.pointSet =
      GridPoint.JNumCenter (GridState.mk 1).pointSet m.pointSet := by
  rw [JNumCenter_diagonal_pointSet_eq_sum, JNumCenter_diagonal_pointSet_eq_sum]
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun c => ?_)
  simp only [Fin.revPerm_apply, rotate_apply]
  have hc := c.isLt
  have hm := (m c).isLt
  simp only [Fin.val_min, Fin.val_max, Fin.val_rev]
  omega

/-- The rational marking pairing with the diagonal state is unchanged by reversing the
marking-square coordinates. -/
theorem JCenter_diagonal_rotate (m : GridState n) :
    GridPoint.JCenter (GridState.mk 1).pointSet m.rotate.pointSet =
      GridPoint.JCenter (GridState.mk 1).pointSet m.pointSet := by
  rw [GridPoint.JCenter_def, GridPoint.JCenter_def, JNumCenter_diagonal_rotate]

end TauCeti.GridState
