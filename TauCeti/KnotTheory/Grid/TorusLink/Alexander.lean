/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.TorusLink.Basic
public import TauCeti.KnotTheory.Grid.Grading.Southwest
public import TauCeti.KnotTheory.Grid.Grading.Parity
import TauCeti.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# The Alexander grading of the `X`-marking state of a torus link grid

In the standard torus link grid `torusLink p q` of grid number `n = (p + 1) + (q + 1)`, the
`X`-marking in column `c` sits in row `c + (q + 1)` taken modulo `n`: in row `c + q + 1` for
`c ≤ p` and in row `c - (p + 1)` for `c > p` (`torusLink_X_val_of_le`, `torusLink_X_val_of_lt`).
This file computes the Alexander grading of the `X`-marking state `G.X` and shows that no grid
state has a larger one.

Both facts come from the column-sum form of the Alexander grading
(`GridDiagram.alexanderTwoℤ_eq_sum_southwestCount`): twice the Alexander grading of a state `x`
is, up to a constant depending only on the diagram, twice the sum over the columns `c` of
`southwestCount 𝕏 c (x c) - min c (x c)`. Each summand is at most zero
(`GridState.southwestCount_le_min`), and at the `X`-marking state every summand vanishes
(`southwestCount_X_torusLink_X`): the `X`-markings southwest of an `X`-corner are exactly those of
the columns to its left in the same block of the shifted diagonal. Hence
`A(x) ≤ A(G.X)` for every grid state `x` (`alexanderTwoℤ_le_torusLink_X`), and evaluating the
constant gives `2 A(G.X) = p q` (`alexanderTwoℤ_torusLink_X`).

When `p + 1` and `q + 1` are coprime the diagram is a knot grid and its Alexander grading is
integral; then `A(G.X) = p q / 2`, which is the Seifert genus `(p q) / 2` of the `(p + 1, q + 1)`
torus knot (`two_mul_alexanderℤ_torusLink_X`, `alexanderℤ_le_torusLink_X`).

## Main results

* `TauCeti.GridDiagram.southwestCount_X_torusLink_X`: at an `X`-corner of a torus link grid the
  southwest count of the `X`-markings is `min c (𝕏 c)`.
* `TauCeti.GridDiagram.alexanderTwoℤ_torusLink_X`: `2 A(G.X) = p q`.
* `TauCeti.GridDiagram.alexanderTwoℤ_le_torusLink_X`: the `X`-marking state has the largest
  Alexander grading among the grid states.
* `TauCeti.GridDiagram.two_mul_alexanderℤ_torusLink_X` and
  `TauCeti.GridDiagram.alexanderℤ_le_torusLink_X`: the integer forms on a torus knot grid.

## References

The Alexander grading of the canonical generator of the torus knot grid is computed in
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 6.
-/

public section

namespace TauCeti

namespace GridDiagram

variable (p q : ℕ)

/-! ### The rows of the `X`-markings -/

/-- The row of the `X`-marking of a torus link grid in a column `c`, as a natural number: the
column index shifted by `q + 1` modulo the grid number. -/
theorem torusLink_X_val (c : Fin (p + 1 + (q + 1))) :
    ((torusLink p q).X c : ℕ) = (c + (q + 1)) % (p + 1 + (q + 1)) := by
  rw [torusLink_X_apply, Fin.coe_finRotate_pow]

/-- In the first `p + 1` columns of a torus link grid the `X`-marking sits `q + 1` rows above the
diagonal. -/
theorem torusLink_X_val_of_le {c : Fin (p + 1 + (q + 1))} (hc : (c : ℕ) ≤ p) :
    ((torusLink p q).X c : ℕ) = c + (q + 1) := by
  rw [torusLink_X_val, Nat.mod_eq_of_lt]
  omega

/-- In the last `q + 1` columns of a torus link grid the `X`-marking sits `p + 1` rows below the
diagonal. -/
theorem torusLink_X_val_of_lt {c : Fin (p + 1 + (q + 1))} (hc : p < c) :
    ((torusLink p q).X c : ℕ) = c - (p + 1) := by
  rw [torusLink_X_val]
  have h : (c : ℕ) + (q + 1) = (c - (p + 1)) + (p + 1 + (q + 1)) := by omega
  rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt]
  have := c.isLt
  omega

/-! ### Southwest counts at the `X`-corners -/

/-- At an `X`-corner `(c, 𝕏 c)` of a torus link grid, the `X`-markings strictly southwest are
exactly those of the columns to the left of `c` in the same block of the shifted diagonal, so
their number is `min c (𝕏 c)`. -/
theorem southwestCount_X_torusLink_X (c : Fin (p + 1 + (q + 1))) :
    (torusLink p q).X.southwestCount c ((torusLink p q).X c) =
      min (c : ℕ) ((torusLink p q).X c) := by
  rw [GridState.southwestCount_def]
  rcases le_or_gt (c : ℕ) p with hc | hc
  · have hXc := torusLink_X_val_of_le p q hc
    rw [min_eq_left (by omega), ← Fin.card_Iio c]
    congr 1
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_def]
    refine ⟨fun h => h.1, fun hd => ⟨hd, ?_⟩⟩
    rw [torusLink_X_val_of_le p q (by omega), hXc]
    omega
  · have hXc := torusLink_X_val_of_lt p q hc
    rw [min_eq_right (by omega), hXc, ← Fin.card_Ico (⟨p + 1, by omega⟩ : Fin (p + 1 + (q + 1))) c]
    congr 1
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico, Fin.lt_def, Fin.le_def]
    constructor
    · rintro ⟨hdc, hX⟩
      refine ⟨?_, hdc⟩
      by_contra hd
      rw [torusLink_X_val_of_le p q (by omega), hXc] at hX
      have := c.isLt
      omega
    · rintro ⟨hpd, hdc⟩
      refine ⟨hdc, ?_⟩
      rw [torusLink_X_val_of_lt p q (by omega), hXc]
      omega

/-- The sum over the columns of a torus link grid of `min c (𝕏 c)` is
`p (p + 1) / 2 + q (q + 1) / 2`: each block of the shifted diagonal contributes the sum of its
column indices within the block. -/
theorem two_mul_sum_min_torusLink_X :
    2 * ∑ c : Fin (p + 1 + (q + 1)), min (c : ℕ) ((torusLink p q).X c) =
      p * (p + 1) + q * (q + 1) := by
  rw [Fin.sum_univ_add]
  have h1 : ∀ i : Fin (p + 1),
      min ((Fin.castAdd (q + 1) i : Fin (p + 1 + (q + 1))) : ℕ)
        ((torusLink p q).X (Fin.castAdd (q + 1) i)) = i := fun i => by
    rw [torusLink_X_val_of_le p q (by rw [Fin.val_castAdd]; omega), Fin.val_castAdd]
    omega
  have h2 : ∀ j : Fin (q + 1),
      min ((Fin.natAdd (p + 1) j : Fin (p + 1 + (q + 1))) : ℕ)
        ((torusLink p q).X (Fin.natAdd (p + 1) j)) = j := fun j => by
    rw [torusLink_X_val_of_lt p q (by rw [Fin.val_natAdd]; omega), Fin.val_natAdd]
    omega
  simp only [h1, h2]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) (p + 1),
    Fin.sum_univ_eq_sum_range (fun i => i) (q + 1)]
  have hp := Finset.sum_range_id_mul_two (p + 1)
  have hq := Finset.sum_range_id_mul_two (q + 1)
  rw [Nat.add_sub_cancel, Nat.mul_comm (p + 1) p] at hp
  rw [Nat.add_sub_cancel, Nat.mul_comm (q + 1) q] at hq
  omega

/-! ### The Alexander grading -/

/-- The southwest counts of the `O`-markings of a torus link grid, which lie on the diagonal, are
`min c r`. -/
@[simp]
theorem southwestCount_O_torusLink (c r : Fin (p + 1 + (q + 1))) :
    (torusLink p q).O.southwestCount c r = min (c : ℕ) r :=
  GridState.southwestCount_of_apply_eq _ c r (torusLink_O_apply p q)

/-- **The Alexander grading of the `X`-marking state of a torus link grid**: twice the Alexander
grading of `G.X` is `p q`. -/
theorem alexanderTwoℤ_torusLink_X :
    (torusLink p q).alexanderTwoℤ (torusLink p q).X = p * q := by
  rw [alexanderTwoℤ_eq_sum_southwestCount]
  simp only [southwestCount_O_torusLink, southwestCount_X_torusLink_X, torusLink_O_apply,
    min_self, sub_self, Finset.sum_const_zero, mul_zero, zero_add]
  have hA : 2 * ∑ c : Fin (p + 1 + (q + 1)), ((c : ℕ) : ℤ) =
      (p + 1 + (q + 1) : ℕ) * ((p + 1 + (q + 1) : ℕ) - 1 : ℕ) := by
    have h := Finset.sum_range_id_mul_two (p + 1 + (q + 1))
    rw [← Fin.sum_univ_eq_sum_range (fun i => i), mul_comm] at h
    exact_mod_cast h
  have hB : 2 * ∑ c : Fin (p + 1 + (q + 1)), ((min (c : ℕ) ((torusLink p q).X c) : ℕ) : ℤ) =
      p * (p + 1) + q * (q + 1) := by
    exact_mod_cast two_mul_sum_min_torusLink_X p q
  have hn : ((p + 1 + (q + 1) : ℕ) - 1 : ℕ) = p + q + 1 := by omega
  rw [hn] at hA
  push_cast at hA hB ⊢
  refine mul_left_cancel₀ (two_ne_zero' ℤ) ?_
  linear_combination hA - hB

/-- Every grid state of a torus link grid has Alexander grading at most that of the `X`-marking
state. -/
theorem alexanderTwoℤ_le_torusLink_X (x : GridState (p + 1 + (q + 1))) :
    (torusLink p q).alexanderTwoℤ x ≤ (torusLink p q).alexanderTwoℤ (torusLink p q).X := by
  rw [alexanderTwoℤ_eq_sum_southwestCount, alexanderTwoℤ_eq_sum_southwestCount]
  simp only [southwestCount_O_torusLink, southwestCount_X_torusLink_X, sub_self,
    Finset.sum_const_zero, mul_zero, zero_add]
  have hle : ∀ c : Fin (p + 1 + (q + 1)),
      ((torusLink p q).X.southwestCount c (x c) : ℤ) - ((min (c : ℕ) (x c) : ℕ) : ℤ) ≤ 0 :=
    fun c => sub_nonpos.mpr (by exact_mod_cast (torusLink p q).X.southwestCount_le_min c (x c))
  have hsum := Finset.sum_nonpos fun c (_ : c ∈ Finset.univ) => hle c
  linarith

section Knot

variable {p q} (h : (p + 1).Coprime (q + 1))

/-- On a torus knot grid, twice the integer Alexander grading of the `X`-marking state is `p q`:
the state sits in Alexander degree `p q / 2`, the Seifert genus of the `(p + 1, q + 1)` torus
knot. -/
theorem two_mul_alexanderℤ_torusLink_X :
    2 * ((isKnot_torusLink_iff p q).mpr h).toOddComponentGridDiagram.alexanderℤ
      (torusLink p q).X = p * q := by
  rw [OddComponentGridDiagram.two_mul_alexanderℤ]
  exact alexanderTwoℤ_torusLink_X p q

/-- On a torus knot grid, the `X`-marking state has the largest integer Alexander grading among
the grid states. -/
theorem alexanderℤ_le_torusLink_X (x : GridState (p + 1 + (q + 1))) :
    ((isKnot_torusLink_iff p q).mpr h).toOddComponentGridDiagram.alexanderℤ x ≤
      ((isKnot_torusLink_iff p q).mpr h).toOddComponentGridDiagram.alexanderℤ
        (torusLink p q).X := by
  have hx : 2 * ((isKnot_torusLink_iff p q).mpr h).toOddComponentGridDiagram.alexanderℤ x =
      (torusLink p q).alexanderTwoℤ x :=
    OddComponentGridDiagram.two_mul_alexanderℤ _ x
  have hX : 2 * ((isKnot_torusLink_iff p q).mpr h).toOddComponentGridDiagram.alexanderℤ
      (torusLink p q).X = (torusLink p q).alexanderTwoℤ (torusLink p q).X :=
    OddComponentGridDiagram.two_mul_alexanderℤ _ (torusLink p q).X
  have := alexanderTwoℤ_le_torusLink_X p q x
  omega

end Knot

end GridDiagram

end TauCeti
