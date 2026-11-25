/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
public import TauCeti.KnotTheory.Grid.Diagram.Components
public import TauCeti.KnotTheory.Grid.Grading.MarkingCount

/-!
# The Alexander multigrading of a grid diagram

A grid diagram `G` of size `n` presenting an `ℓ`-component link has one Alexander grading for each
link component. For a component `q`, write `𝕏_q` and `𝕆_q` for the `X`- and `O`-markings on `q`
and `n_q` for the number of `O`-markings on `q`. The `q`-th Alexander grading of a grid state `x`
is

`A_q(x) = J(x - ½(𝕏 + 𝕆), 𝕏_q - 𝕆_q) - (n_q - 1) / 2`,

with `J` extended bilinearly to formal sums of grid points and marked squares
(`GridDiagram.componentAlexander`). In the formula, `J(x, 𝕏_q)` pairs the points of `x` with the
centres of the marked squares, which is `GridPoint.JCenter`, while the pairings among markings
compare marked squares with marked squares and so may use their lower-left corners.

The multigrading refines the single Alexander grading `GridDiagram.alexander` of
`Gradings.lean`, but with the link normalization: the sum of the component gradings is

`∑_q A_q(x) = J(x - ½(𝕏 + 𝕆), 𝕏 - 𝕆) - (n - ℓ) / 2 = A(x) + (ℓ - 1) / 2`

(`GridDiagram.sum_componentAlexander`), since `A` carries the knot shift `(n - 1) / 2`. For a knot
there is a single component and `A_q = A` (`GridDiagram.IsKnot.componentAlexander_eq`).

Across a rectangle `r` from `x` to `y` the `q`-th grading changes by the markings of `q` that `r`
covers, `A_q(x) - A_q(y) = #(𝕏_q ∩ r) - #(𝕆_q ∩ r)`
(`GridDiagram.componentAlexander_sub_componentAlexander_eq_card_sub_card`). Each column and each
row carries either no marking of `q` or exactly one `X`-marking and one `O`-marking of `q`,
because the component permutation `c ↦ X⁻¹(O(c))` stays on `q`; so the weight `𝕏_q - 𝕆_q` has
vanishing column and row sums, and `GridRectangleBetween.JWeight_sub_JWeight_eq_sum` applies.

The gradings are rational and, for a link, need not be integers (Manolescu, Ozsváth, Szabó and
Thurston place `A_q` in `ℤ + lk(L_q, L ∖ L_q) / 2`), so they are valued in `ℚ` and no integrality
is claimed here. Their extension to the unblocked complex `GC⁻` is in
`Grading/Unblocked/Component.lean`.

## Main definitions

* `TauCeti.GridDiagram.componentAlexander`: the Alexander grading `A_q` of a link component `q`.

## Main results

* `TauCeti.GridDiagram.sum_componentAlexander`: the component gradings sum to the Alexander
  grading plus `(ℓ - 1) / 2`.
* `TauCeti.GridDiagram.IsKnot.componentAlexander_eq`: for a knot the component grading is the
  Alexander grading.
* `TauCeti.GridDiagram.componentAlexander_sub_componentAlexander_eq_card_sub_card`: the change of
  a component grading across a rectangle counts the covered markings of that component.

## References

* C. Manolescu, P. Ozsváth, Z. Szabó, D. Thurston, *On combinatorial link Floer homology*,
  Geom. Topol. 11 (2007), [arXiv:math/0610559](https://arxiv.org/abs/math/0610559), Section 2:
  the Alexander multigrading `A_i` of a grid state.
* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Section 11.1: the Alexander multigrading of a grid state of a link
  and its relation to the single Alexander grading.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- A pairing that is the sum of its values on the single points of a point set is the sum of its
values on the parts of the point set lying over each component. -/
private theorem sum_filter_componentOfColumn (F : Finset (Fin n × Fin n) → ℚ)
    (hF : ∀ t, F t = ∑ p ∈ t, F {p}) (t : Finset (Fin n × Fin n)) :
    ∑ q, F (t.filter fun p => G.componentOfColumn p.1 = q) = F t := by
  rw [Finset.sum_congr rfl fun q _ => hF _, hF t]
  exact Finset.sum_fiberwise t (fun p => G.componentOfColumn p.1) fun p => F {p}

/-- The `J`-pairing with the `X`-markings is the sum of the pairings with the `X`-markings of each
component. -/
theorem sum_J_componentXSet (s : Finset (Fin n × Fin n)) :
    ∑ q, GridPoint.J s (G.componentXSet q) = GridPoint.J s G.XSet := by
  simp only [componentXSet_def]
  exact G.sum_filter_componentOfColumn _ (GridPoint.J_eq_sum_singleton_right s) _

/-- The `J`-pairing with the `O`-markings is the sum of the pairings with the `O`-markings of each
component. -/
theorem sum_J_componentOSet (s : Finset (Fin n × Fin n)) :
    ∑ q, GridPoint.J s (G.componentOSet q) = GridPoint.J s G.OSet := by
  simp only [componentOSet_def]
  exact G.sum_filter_componentOfColumn _ (GridPoint.J_eq_sum_singleton_right s) _

/-- The pairing of a point set with the centres of the `X`-markings is the sum of its pairings with
the `X`-markings of each component. -/
theorem sum_JCenter_componentXSet (s : Finset (Fin n × Fin n)) :
    ∑ q, GridPoint.JCenter s (G.componentXSet q) = GridPoint.JCenter s G.XSet := by
  simp only [componentXSet_def]
  exact G.sum_filter_componentOfColumn _ (GridPoint.JCenter_eq_sum_singleton_right s) _

/-- The pairing of a point set with the centres of the `O`-markings is the sum of its pairings with
the `O`-markings of each component. -/
theorem sum_JCenter_componentOSet (s : Finset (Fin n × Fin n)) :
    ∑ q, GridPoint.JCenter s (G.componentOSet q) = GridPoint.JCenter s G.OSet := by
  simp only [componentOSet_def]
  exact G.sum_filter_componentOfColumn _ (GridPoint.JCenter_eq_sum_singleton_right s) _

/-! ### The component Alexander gradings -/

/-- The Alexander grading of the link component `q`,
`A_q(x) = J(x - ½(𝕏 + 𝕆), 𝕏_q - 𝕆_q) - (n_q - 1) / 2`.

The points of `x` are paired with the centres of the marked squares of `q`
(`GridPoint.JCenter`); the markings are paired with each other through the lower-left corners of
their squares, which gives the same value since both are translated by the same vector. -/
def componentAlexander (q : G.Components) (x : GridState n) : ℚ :=
  GridPoint.JCenter x.pointSet (G.componentXSet q) -
      GridPoint.JCenter x.pointSet (G.componentOSet q) -
    (GridPoint.J G.XSet (G.componentXSet q) - GridPoint.J G.XSet (G.componentOSet q) +
        GridPoint.J G.OSet (G.componentXSet q) - GridPoint.J G.OSet (G.componentOSet q)) / 2 -
    (((G.componentColumns q).card : ℚ) - 1) / 2

/-- The component Alexander grading as its defining formula. -/
theorem componentAlexander_def (q : G.Components) (x : GridState n) :
    G.componentAlexander q x =
      GridPoint.JCenter x.pointSet (G.componentXSet q) -
          GridPoint.JCenter x.pointSet (G.componentOSet q) -
        (GridPoint.J G.XSet (G.componentXSet q) - GridPoint.J G.XSet (G.componentOSet q) +
            GridPoint.J G.OSet (G.componentXSet q) - GridPoint.J G.OSet (G.componentOSet q)) / 2 -
        (((G.componentColumns q).card : ℚ) - 1) / 2 :=
  (rfl)

/-- **The component gradings sum to the Alexander grading with the link normalization.** The sum
of the Alexander gradings of the components is `J(x - ½(𝕏 + 𝕆), 𝕏 - 𝕆) - (n - ℓ) / 2`, which is
the Alexander grading `A(x)`, normalized by the knot shift `(n - 1) / 2`, plus `(ℓ - 1) / 2`. -/
theorem sum_componentAlexander (x : GridState n) :
    ∑ q, G.componentAlexander q x = G.alexander x + ((G.componentCount : ℚ) - 1) / 2 := by
  have hcard : ∑ q, (((G.componentColumns q).card : ℚ) - 1) = (n : ℚ) - G.componentCount := by
    rw [Finset.sum_sub_distrib, ← Nat.cast_sum, sum_card_componentColumns, Finset.sum_const,
      Finset.card_univ, card_components, nsmul_eq_mul, mul_one]
  simp only [componentAlexander_def, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_div, sum_JCenter_componentXSet, sum_JCenter_componentOSet, sum_J_componentXSet,
    sum_J_componentOSet, hcard]
  rw [alexander_eq, JX_def, JO_def, GridState.J_def, GridState.J_def, ← XSet_def, ← OSet_def,
    GridPoint.J_comm G.XSet G.OSet]
  push_cast
  ring

/-- **For a knot the component grading is the Alexander grading.** A knot grid has a single
component, whose Alexander grading is `A`. -/
theorem IsKnot.componentAlexander_eq {G : GridDiagram n} (hG : G.IsKnot) (q : G.Components)
    (x : GridState n) : G.componentAlexander q x = G.alexander x := by
  have hcard : Fintype.card G.Components = 1 := by
    rw [card_components]
    exact (G.isKnot_def).mp hG
  have : Subsingleton G.Components := Fintype.card_le_one_iff_subsingleton.mp hcard.le
  have h := G.sum_componentAlexander x
  rw [Fintype.sum_subsingleton _ q, (G.isKnot_def).mp hG] at h
  rw [h]
  norm_num

/-! ### The change across a rectangle -/

/-- The weight `𝕏_q - 𝕆_q` of a component on the squares of the grid. -/
private def componentWeight (q : G.Components) (p : Fin n × Fin n) : ℤ :=
  (if p ∈ G.componentXSet q then 1 else 0) - (if p ∈ G.componentOSet q then 1 else 0)

/-- Every column carries the same number of `X`- and `O`-markings of a component. -/
private theorem sum_componentWeight_column (q : G.Components) (c : Fin n) :
    ∑ r, G.componentWeight q (c, r) = 0 := by
  simp [componentWeight, Finset.sum_sub_distrib, ite_and]

/-- Every row carries the same number of `X`- and `O`-markings of a component. -/
private theorem sum_componentWeight_row (q : G.Components) (r : Fin n) :
    ∑ c, G.componentWeight q (c, r) = 0 := by
  have h := G.componentOfColumn_X_transpose r
  simp only [componentWeight, mem_componentXSet, GridState.apply_eq_iff_eq_transpose,
    GridState.transpose_apply, ite_and, mem_componentOSet, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  simp only [GridState.transpose_apply] at h
  rw [h, sub_self]

/-- The pairing of a grid state with the component weight is the difference of its pairings with
the `X`- and `O`-markings of the component. -/
private theorem JWeight_componentWeight (q : G.Components) (x : GridState n) :
    x.JWeight (G.componentWeight q) =
      GridPoint.JCenter x.pointSet (G.componentXSet q) -
        GridPoint.JCenter x.pointSet (G.componentOSet q) := by
  rw [GridState.JWeight_def, GridPoint.JCenter_eq_sum_singleton_right _ (G.componentXSet q),
    GridPoint.JCenter_eq_sum_singleton_right _ (G.componentOSet q)]
  simp only [componentWeight, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero, sub_mul,
    ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter]

/-- **The change of a component grading across a rectangle.** If `r` is a rectangle from `x` to
`y`, then `A_q(x) - A_q(y)` is the number of `X`-markings of `q` that `r` covers minus the number
of `O`-markings of `q` that it covers. -/
theorem componentAlexander_sub_componentAlexander_eq_card_sub_card (q : G.Components)
    {x y : GridState n} (R : GridRectangleBetween x y) :
    G.componentAlexander q x - G.componentAlexander q y =
      ((G.componentXSet q ∩ R.toGridRectangle.coveredSquares).card : ℚ) -
        ((G.componentOSet q ∩ R.toGridRectangle.coveredSquares).card : ℚ) := by
  have h := R.JWeight_sub_JWeight_eq_sum (G.sum_componentWeight_column q)
    (G.sum_componentWeight_row q)
  rw [JWeight_componentWeight, JWeight_componentWeight] at h
  have hsum : ∑ p ∈ R.toGridRectangle.coveredSquares, (G.componentWeight q p : ℚ) =
      ((G.componentXSet q ∩ R.toGridRectangle.coveredSquares).card : ℚ) -
        ((G.componentOSet q ∩ R.toGridRectangle.coveredSquares).card : ℚ) := by
    simp only [componentWeight, Int.cast_sub, Finset.sum_sub_distrib, Int.cast_ite, Int.cast_one,
      Int.cast_zero, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_comm]
  rw [componentAlexander_def, componentAlexander_def, ← hsum, ← h]
  ring

end GridDiagram

end TauCeti
