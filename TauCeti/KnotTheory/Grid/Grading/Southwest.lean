/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Grading.Integer
import Mathlib.Tactic.Linarith

/-!
# The Alexander grading as a sum of southwest marking counts

The pairing of a grid point `(c, r)` against the squares occupied by a grid state `m`
(`GridState.JNumCenterAt`) counts the points of `m` weakly northeast of `(c, r)` together with
those strictly southwest of it. Since `m` occupies one point in every column and every row, the
northeast count is determined by the southwest count: writing `southwestCount m c r` for the
number of columns `d < c` with `m d < r`,

`JNumCenterAt m c r + c + r = n + 2 · southwestCount m c r`
(`GridState.JNumCenterAt_add_add`).

Substituting this into the two marking pairings of the Alexander grading formula, the terms that
do not involve the markings cancel between the `O`- and `X`-pairings, and the doubled integer
Alexander grading of a grid state `x` becomes a sum over its columns
(`GridDiagram.alexanderTwoℤ_eq_sum_southwestCount`):

`2 A(x) = 2 ∑_c (southwestCount 𝕏 c (x c) - southwestCount 𝕆 c (x c))
  + ∑_c southwestCount 𝕆 c (𝕆 c) - ∑_c southwestCount 𝕏 c (𝕏 c) - (n - 1)`.

The summands `southwestCount 𝕏 c (x c) - southwestCount 𝕆 c (x c)` are, up to sign, the winding
numbers of the link diagram around the points of `x`; the two remaining sums are the numbers of
non-inversions of the marking permutations (`GridState.I_self_pointSet_eq_sum_southwestCount`).
This is the form in which the Alexander grading of a grid state is compared with that of a
distinguished state, since each summand is bounded by `min c (x c)`
(`GridState.southwestCount_le_min`), with equality for the identity state
(`GridState.southwestCount_of_apply_eq`).

## Main definitions

* `TauCeti.GridState.southwestCount`: the number of points of a grid state strictly southwest of
  a grid point.

## Main results

* `TauCeti.GridState.JNumCenterAt_add_add`: the marking pairing of a point is determined by the
  southwest count.
* `TauCeti.GridState.I_self_pointSet_eq_sum_southwestCount`: the non-inversion count of a grid
  state is the sum over its columns of the southwest counts at its own points.
* `TauCeti.GridDiagram.alexanderTwoℤ_eq_sum_southwestCount`: the doubled Alexander grading as a
  sum over columns.

## References

The winding-number form of the Alexander grading is Ozsváth--Stipsicz--Szabó, *Grid Homology for
Knots and Links*, Section 4.7, Proposition 4.7.2. The column-sum form above is that formula with
each winding number written as a difference of southwest counts and with the constant term kept
as the non-inversion counts of the marking permutations.
-/

public section

namespace TauCeti

namespace GridState

variable {n : ℕ} (m : GridState n) (c r : Fin n)

/-- The number of points of the grid state `m` strictly southwest of the grid point `(c, r)`: the
columns `d < c` whose point lies in a row below `r`. -/
def southwestCount : ℕ :=
  (Finset.univ.filter fun d : Fin n => d < c ∧ m d < r).card

/-- The southwest count as the cardinality of the set of columns it counts. -/
theorem southwestCount_def :
    m.southwestCount c r = (Finset.univ.filter fun d : Fin n => d < c ∧ m d < r).card :=
  (rfl)

/-- The southwest count of `(c, r)` is at most the number `c` of columns to the left of `c`. -/
theorem southwestCount_le_left : m.southwestCount c r ≤ c := by
  rw [southwestCount_def, ← Fin.card_Iio c]
  exact Finset.card_le_card fun d hd => Finset.mem_Iio.mpr (Finset.mem_filter.mp hd).2.1

/-- A grid state has exactly `r` points in the rows below `r`. -/
theorem card_filter_apply_lt : (Finset.univ.filter fun d : Fin n => m d < r).card = r := by
  rw [← Fin.card_Iio r]
  refine Finset.card_bij (fun d _ => m d) (fun d hd => ?_) (fun a _ b _ h => m.toPerm.injective h)
    fun b hb => ⟨m.toPerm.symm b, ?_, m.toPerm.apply_symm_apply b⟩
  · exact Finset.mem_Iio.mpr (Finset.mem_filter.mp hd).2
  · simpa using Finset.mem_Iio.mp hb

/-- The southwest count of `(c, r)` is at most the number `r` of rows below `r`. -/
theorem southwestCount_le_right : m.southwestCount c r ≤ r := by
  rw [southwestCount_def, ← m.card_filter_apply_lt r]
  exact Finset.card_le_card (Finset.monotone_filter_right _ fun d _ h => h.2)

/-- The southwest count of `(c, r)` is at most `min c r`. -/
theorem southwestCount_le_min : m.southwestCount c r ≤ min (c : ℕ) r :=
  le_min (m.southwestCount_le_left c r) (m.southwestCount_le_right c r)

/-- The southwest counts of the identity state, whose points lie on the diagonal, are
`min c r`. -/
theorem southwestCount_of_apply_eq (hm : ∀ d, m d = d) :
    m.southwestCount c r = min (c : ℕ) r := by
  rw [southwestCount_def, ← Fin.val_min, ← Fin.card_Iio]
  congr 1
  ext d
  simp [hm, lt_min_iff]

/-- The marking pairing of the grid point `(c, r)` against the squares of `m` is determined by
the southwest count: `JNumCenterAt m c r + c + r = n + 2 · southwestCount m c r`. The northeast
count is the `n - c` columns from `c` on, minus those whose point lies below `r`, and the latter
are the `r` points below `r` minus the southwest count. -/
theorem JNumCenterAt_add_add : m.JNumCenterAt c r + c + r = n + 2 * m.southwestCount c r := by
  classical
  rw [JNumCenterAt_eq_card, southwestCount_def]
  have h1 := Finset.card_filter_add_card_filter_not (s := Finset.Ici c) fun d => r ≤ m d
  have h2 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun d : Fin n => m d < r) fun d => d < c
  rw [Fin.card_Ici] at h1
  rw [m.card_filter_apply_lt r, Finset.filter_filter, Finset.filter_filter] at h2
  have e1 : (Finset.Ici c).filter (fun d => r ≤ m d) =
      Finset.univ.filter fun d : Fin n => c ≤ d ∧ r ≤ m d := by
    ext d
    simp
  have e2 : (Finset.Ici c).filter (fun d => ¬r ≤ m d) =
      Finset.univ.filter fun d : Fin n => m d < r ∧ ¬d < c := by
    ext d
    simp [and_comm]
  have e3 : (Finset.univ.filter fun d : Fin n => m d < r ∧ d < c) =
      Finset.univ.filter fun d : Fin n => d < c ∧ m d < r := by
    ext d
    simp [and_comm]
  rw [e1, e2] at h1
  rw [e3] at h2
  have hc := c.isLt
  omega

/-- The number of non-inversions of a grid state is the sum over its columns of the southwest
counts at its own points. -/
theorem I_self_pointSet_eq_sum_southwestCount :
    GridPoint.I m.pointSet m.pointSet = ∑ c, m.southwestCount c (m c) := by
  rw [I_self_pointSet_eq_card, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => by rw [southwestCount_def, Finset.card_filter]

/-- The marking pairing of a grid state against a marking state, as a sum of southwest counts:
the terms not involving the markings are the same for every marking state. -/
theorem JNumCenter_pointSet_eq_sum_southwestCount (x m : GridState n) :
    (GridPoint.JNumCenter x.pointSet m.pointSet : ℤ) =
      ∑ c : Fin n, ((n : ℤ) + 2 * m.southwestCount c (x c) - c - x c) := by
  rw [GridState.JNumCenter_pointSet_eq_sum]
  push_cast
  exact Finset.sum_congr rfl fun c _ => by
    have h := m.JNumCenterAt_add_add c (x c)
    have h' : (m.JNumCenterAt c (x c) : ℤ) + c + x c = n + 2 * m.southwestCount c (x c) := by
      exact_mod_cast h
    linarith

end GridState

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- **The Alexander grading as a sum over columns.** Twice the integer Alexander grading of a
grid state `x` is twice the sum over the columns `c` of the differences of the southwest counts
of `(c, x c)` for the `X`- and the `O`-markings, corrected by the non-inversion counts of the two
marking states and the normalization shift. -/
theorem alexanderTwoℤ_eq_sum_southwestCount (x : GridState n) :
    G.alexanderTwoℤ x =
      2 * ∑ c : Fin n, ((G.X.southwestCount c (x c) : ℤ) - G.O.southwestCount c (x c)) +
        ∑ c : Fin n, (G.O.southwestCount c (G.O c) : ℤ) -
          ∑ c : Fin n, (G.X.southwestCount c (G.X c) : ℤ) - ((n : ℤ) - 1) := by
  simp only [alexanderTwoℤ_def, maslovOℤ_def, maslovXℤ_def, OSet_def, XSet_def,
    GridState.I_self_pointSet_eq_sum_southwestCount,
    GridState.JNumCenter_pointSet_eq_sum_southwestCount, Nat.cast_sum, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end GridDiagram

end TauCeti
