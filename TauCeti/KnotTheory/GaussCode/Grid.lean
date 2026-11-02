/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Dist
public import TauCeti.KnotTheory.GaussCode.Basic
public import TauCeti.KnotTheory.Grid.Diagram.Components
public import TauCeti.KnotTheory.Grid.Diagram.Crossing

/-!
# The Gauss code of a grid knot

A grid diagram `G` is drawn as a planar link diagram (`TauCeti.GridDiagram.crossings`), with
vertical segments oriented from `X` to `O`, horizontal segments from `O` to `X`, and vertical
segments crossing over horizontal ones. When `G` represents a knot (`TauCeti.GridDiagram.IsKnot`),
traversing this diagram from a base point and recording the crossings in the order met gives a
based oriented Gauss code, `TauCeti.GridDiagram.gaussCode`. It joins the grid presentation of a
knot to its diagram presentations: `TauCeti.BasedOrientedGaussCode.toOrientedPDCode` turns it into
an oriented PD-code.

The base point is the `X` marking of a chosen column `c₀`. From there the traversal runs along the
vertical segment of `c₀` to its `O` marking, then along the horizontal segment of that row to the
next `X` marking, and so on: step `t` runs along the vertical segment of the column
`TauCeti.GridDiagram.IsKnot.traversal hG c₀ t = componentPerm ^ t c₀` and then along the
horizontal segment of the row of its `O` marking. Number the segments in this order, the vertical
segment of step `t` as `2 t` and the horizontal one as `2 t + 1`. A crossing in the square
`(c, r)` is visited twice (`TauCeti.GridDiagram.CrossingVisit`):

* over, along the vertical segment of column `c`, at distance `|r - X c|` from its start;
* under, along the horizontal segment of row `r`, at distance `|c - O.transpose r|` from its start.

The visits are met in the lexicographic order of their segment index and their distance along the
segment (`TauCeti.GridDiagram.CrossingVisit.position`). The code records at each visit whether it
passes over, and gives each crossing its sign `TauCeti.GridDiagram.crossingSign`
(`TauCeti.GridDiagram.gaussCode_over`, `TauCeti.GridDiagram.gaussCode_sign_visit`). So its writhe
is the sum of the crossing signs of the grid (`TauCeti.GridDiagram.gaussCode_writhe`).

That this diagram is planar, and that grid moves change it by Reidemeister moves (Cromwell's
theorem), are not proved here.

## Main definitions

* `TauCeti.GridDiagram.CrossingVisit hG c₀`: the visits of the traversal from `c₀` to the
  crossings of a knot grid, ordered along the traversal.
* `TauCeti.GridDiagram.CrossingVisit.position`: the segment index and the distance along the
  segment of a visit.
* `TauCeti.GridDiagram.visitOrderIso hG c₀`: the visits, enumerated in the order met.
* `TauCeti.GridDiagram.gaussCode hG c₀`: the based oriented Gauss code of a knot grid.

## Main results

* `TauCeti.GridDiagram.gaussCode_visit_eq_visit_iff`: two visits carry the same crossing label
  exactly when they visit the same crossing of the grid.
* `TauCeti.GridDiagram.visitOrderIso_partner`: the partner of a visit is the other visit of its
  crossing.
* `TauCeti.GridDiagram.gaussCode_visit_lt_visit_iff`: crossings are numbered in the order of
  their first visits.
* `TauCeti.GridDiagram.gaussCode_over`: a visit passes over exactly when it runs along a vertical
  segment.
* `TauCeti.GridDiagram.gaussCode_sign_visit`: the sign of a crossing label is the crossing sign of
  the grid.
* `TauCeti.GridDiagram.gaussCode_writhe`: the writhe of the code is the sum of the crossing signs
  of the grid.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical
  Surveys and Monographs 208 (2015), Section 3.1, for the planar diagram of a grid diagram.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1, for
  Gauss codes and crossing signs.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} {G : GridDiagram n}

/-- A visit of the traversal from the column `c₀` of a knot grid to one of its crossings: the
crossing, and whether the visit runs along the vertical segment of the crossing, passing over, or
along its horizontal segment, passing under. The visits are ordered along the traversal, by
`TauCeti.GridDiagram.CrossingVisit.position`. -/
@[ext]
structure CrossingVisit (hG : G.IsKnot) (c₀ : Fin n) where
  /-- The crossing visited, as the square `(c, r)` at whose centre it lies. -/
  crossing : G.crossings
  /-- Whether the visit runs along the vertical segment of the crossing, passing over. -/
  isOver : Bool

namespace CrossingVisit

variable {hG : G.IsKnot} {c₀ : Fin n}

/-- A visit is a crossing together with the strand, vertical or horizontal, along which it is
visited. -/
def equivProd (hG : G.IsKnot) (c₀ : Fin n) : CrossingVisit hG c₀ ≃ G.crossings × Bool where
  toFun v := (v.crossing, v.isOver)
  invFun p := ⟨p.1, p.2⟩

instance : Fintype (CrossingVisit hG c₀) :=
  Fintype.ofEquiv _ (equivProd hG c₀).symm

/-- Every crossing is visited twice. -/
theorem card_eq (hG : G.IsKnot) (c₀ : Fin n) :
    Fintype.card (CrossingVisit hG c₀) = 2 * G.crossings.card := by
  rw [Fintype.card_congr (equivProd hG c₀), Fintype.card_prod, Fintype.card_coe,
    Fintype.card_bool, mul_comm]

/-- Summing over the visits counts every crossing twice. -/
theorem sum_crossing {M : Type*} [AddCommMonoid M] (f : Fin n × Fin n → M) :
    ∑ v : CrossingVisit hG c₀, f v.crossing.1 = 2 • ∑ p ∈ G.crossings, f p := by
  rw [← (equivProd hG c₀).symm.sum_comp, Fintype.sum_prod_type, ← Finset.sum_coe_sort G.crossings,
    Finset.smul_sum]
  simp [equivProd]

/-- The **position** of a visit along the traversal from `c₀`: the index of the segment it runs
along, followed by the distance travelled along that segment. The vertical segment of the column
reached at step `t` of the traversal has index `2 t` and starts at the `X` marking of that column;
the horizontal segment of the row of its `O` marking has index `2 t + 1` and starts at that `O`
marking. -/
noncomputable def position (v : CrossingVisit hG c₀) : ℕ ×ₗ ℕ :=
  if v.isOver then
    toLex (2 * (hG.traversal c₀).symm v.crossing.1.1,
      Nat.dist v.crossing.1.2 (G.X v.crossing.1.1))
  else
    toLex (2 * (hG.traversal c₀).symm (G.O.transpose v.crossing.1.2) + 1,
      Nat.dist v.crossing.1.1 (G.O.transpose v.crossing.1.2))

/-- The over-visit of the crossing `(c, r)` runs along the vertical segment of column `c`, at
distance `|r - X c|` from its start. -/
@[simp]
theorem position_mk_true (p : G.crossings) :
    position (⟨p, true⟩ : CrossingVisit hG c₀) =
      toLex (2 * ((hG.traversal c₀).symm p.1.1 : ℕ), Nat.dist p.1.2 (G.X p.1.1)) := by
  simp [position]

/-- The under-visit of the crossing `(c, r)` runs along the horizontal segment of row `r`, at
distance `|c - O.transpose r|` from its start. -/
@[simp]
theorem position_mk_false (p : G.crossings) :
    position (⟨p, false⟩ : CrossingVisit hG c₀) =
      toLex (2 * ((hG.traversal c₀).symm (G.O.transpose p.1.2) : ℕ) + 1,
        Nat.dist p.1.1 (G.O.transpose p.1.2)) := by
  simp [position]

/-- Distinct visits have distinct positions: a segment index determines the column of a vertical
segment or the row of a horizontal one, and a distance along the segment determines the point of
the segment. -/
theorem position_injective : Function.Injective (position (hG := hG) (c₀ := c₀)) := by
  -- A segment index determines the step of the traversal, hence the column or row.
  have hτ {a b : Fin n} (h : ((hG.traversal c₀).symm a : ℕ) = (hG.traversal c₀).symm b) : a = b :=
    (hG.traversal c₀).symm.injective (Fin.ext h)
  -- Two points strictly between `a` and `b` at the same distance from `a` are equal.
  have hdist {a b x y : Fin n} (hx : x ∈ Set.uIoo a b) (hy : y ∈ Set.uIoo a b)
      (h : Nat.dist x a = Nat.dist y a) : x = y := by
    rw [Fin.mem_uIoo_iff_val] at hx hy
    unfold Nat.dist at h
    ext
    omega
  rintro ⟨⟨⟨c, r⟩, hp⟩, _ | _⟩ ⟨⟨⟨c', r'⟩, hp'⟩, _ | _⟩ h <;>
    simp only [position_mk_true, position_mk_false, toLex_inj, Prod.mk.injEq] at h
  · rw [mem_crossings, isCrossing_iff] at hp hp'
    have hr : r = r' := by
      have := hτ (by omega : ((hG.traversal c₀).symm (G.O.transpose r) : ℕ) =
        (hG.traversal c₀).symm (G.O.transpose r'))
      rw [← G.O.apply_transpose_apply r, this, G.O.apply_transpose_apply]
    subst hr
    obtain rfl := hdist hp.2 hp'.2 h.2
    rfl
  · omega
  · omega
  · rw [mem_crossings, isCrossing_iff] at hp hp'
    obtain rfl : c = c' := hτ (by omega)
    obtain rfl := hdist hp.1 hp'.1 h.2
    rfl

/-- The visits are ordered along the traversal, by their positions. -/
noncomputable instance : LinearOrder (CrossingVisit hG c₀) :=
  LinearOrder.lift' position position_injective

/-- One visit comes before another exactly when its position does. -/
theorem lt_iff_position_lt {v w : CrossingVisit hG c₀} : v < w ↔ v.position < w.position :=
  Iff.rfl

/-- One visit comes no later than another exactly when its position does. -/
theorem le_iff_position_le {v w : CrossingVisit hG c₀} : v ≤ w ↔ v.position ≤ w.position :=
  Iff.rfl

end CrossingVisit

/-- The two visits of each crossing, paired. -/
private def visitMatching (hG : G.IsKnot) (c₀ : Fin n) : PerfectMatching (CrossingVisit hG c₀) :=
  .mk ⟨fun v ↦ ⟨v.crossing, !v.isOver⟩, fun v ↦ ⟨v.crossing, !v.isOver⟩,
      fun v ↦ CrossingVisit.ext rfl (Bool.not_not v.isOver),
      fun v ↦ CrossingVisit.ext rfl (Bool.not_not v.isOver)⟩
    (fun v ↦ CrossingVisit.ext rfl (Bool.not_not v.isOver))
    (fun v h ↦ Bool.not_ne_self v.isOver (congrArg CrossingVisit.isOver h))

private theorem visitMatching_apply (hG : G.IsKnot) (c₀ : Fin n) (v : CrossingVisit hG c₀) :
    (visitMatching hG c₀).val v = ⟨v.crossing, !v.isOver⟩ := by
  rw [visitMatching, PerfectMatching.val_mk, Equiv.coe_fn_mk]

/-- The **Gauss code of a knot grid**, read from the base point at the `X` marking of the column
`c₀`: the visits of the traversal to the crossings of the planar diagram, in the order met, with a
visit over exactly when it runs along a vertical segment, and with the crossing signs of the grid.
Crossings are labelled in the order of their first visits. -/
noncomputable def gaussCode (hG : G.IsKnot) (c₀ : Fin n) :
    BasedOrientedGaussCode G.crossings.card :=
  BasedOrientedGaussCode.ofPerfectMatching (CrossingVisit.card_eq hG c₀) (visitMatching hG c₀)
    CrossingVisit.isOver (fun v ↦ by rw [visitMatching_apply])
    (fun v ↦ G.crossingSign v.crossing.1.1 v.crossing.1.2)

/-- The visits of the traversal from `c₀` of a knot grid to its crossings, enumerated in the order
met: the `i`-th visit of `TauCeti.GridDiagram.gaussCode hG c₀`. -/
noncomputable def visitOrderIso (hG : G.IsKnot) (c₀ : Fin n) :
    Fin (2 * G.crossings.card) ≃o CrossingVisit hG c₀ :=
  Fintype.orderIsoFinOfCardEq _ (CrossingVisit.card_eq hG c₀)

variable (hG : G.IsKnot) (c₀ : Fin n)

/-- **The over/under convention.** A visit passes over exactly when it runs along a vertical
segment. -/
@[simp]
theorem gaussCode_over (i : Fin (2 * G.crossings.card)) :
    (gaussCode hG c₀).over i = (visitOrderIso hG c₀ i).isOver := by
  rw [gaussCode, visitOrderIso, BasedOrientedGaussCode.ofPerfectMatching_over]

/-- The partner of a visit is the other visit of the same crossing. -/
@[simp]
theorem visitOrderIso_partner (i : Fin (2 * G.crossings.card)) :
    visitOrderIso hG c₀ ((gaussCode hG c₀).partner.val i) =
      ⟨(visitOrderIso hG c₀ i).crossing, !(visitOrderIso hG c₀ i).isOver⟩ := by
  rw [visitOrderIso, gaussCode,
    BasedOrientedGaussCode.orderIsoFinOfCardEq_ofPerfectMatching_partner, visitMatching_apply]

/-- Two visits carry the same crossing label exactly when they visit the same crossing of the
grid. -/
theorem gaussCode_visit_eq_visit_iff (i j : Fin (2 * G.crossings.card)) :
    (gaussCode hG c₀).visit i = (gaussCode hG c₀).visit j ↔
      (visitOrderIso hG c₀ i).crossing = (visitOrderIso hG c₀ j).crossing := by
  rw [BasedOrientedGaussCode.visit_eq_iff, ← (visitOrderIso hG c₀).injective.eq_iff,
    ← (visitOrderIso hG c₀).injective.eq_iff, visitOrderIso_partner]
  generalize visitOrderIso hG c₀ i = v
  generalize visitOrderIso hG c₀ j = w
  rcases v with ⟨p, _ | _⟩ <;> rcases w with ⟨q, _ | _⟩ <;> simp [CrossingVisit.ext_iff, eq_comm]

/-- **Crossings are numbered in the order of their first visits.** The crossing met at visit `i`
has a smaller label than the one met at visit `j` exactly when the first visit to the first
crossing comes before the first visit to the second. -/
theorem gaussCode_visit_lt_visit_iff (i j : Fin (2 * G.crossings.card)) :
    (gaussCode hG c₀).visit i < (gaussCode hG c₀).visit j ↔
      min (visitOrderIso hG c₀ i) (visitOrderIso hG c₀ ((gaussCode hG c₀).partner.val i)) <
        min (visitOrderIso hG c₀ j) (visitOrderIso hG c₀ ((gaussCode hG c₀).partner.val j)) := by
  rw [visitOrderIso_partner, visitOrderIso_partner, gaussCode, visitOrderIso,
    BasedOrientedGaussCode.ofPerfectMatching_visit_lt_visit_iff, visitMatching_apply,
    visitMatching_apply]

/-- **The sign of a crossing.** The sign of the crossing label met at visit `i` is the crossing
sign of the grid at the crossing visited. -/
theorem gaussCode_sign_visit (i : Fin (2 * G.crossings.card)) :
    (gaussCode hG c₀).sign ((gaussCode hG c₀).visit i) =
      G.crossingSign (visitOrderIso hG c₀ i).crossing.1.1
        (visitOrderIso hG c₀ i).crossing.1.2 := by
  rw [gaussCode, visitOrderIso, BasedOrientedGaussCode.ofPerfectMatching_sign_visit _ _ _ _ _
    (fun v ↦ by rw [visitMatching_apply]) i]

/-- The writhe of the Gauss code of a knot grid is the sum of the crossing signs of the grid. -/
theorem gaussCode_writhe :
    (gaussCode hG c₀).writhe = ∑ p ∈ G.crossings, (G.crossingSign p.1 p.2 : ℤ) := by
  -- Sum the signs over all visits in two ways: every crossing label (`sum_sign_visit`), and every
  -- crossing of the grid, is visited exactly twice.
  have hgrid : ∑ i, ((gaussCode hG c₀).sign ((gaussCode hG c₀).visit i) : ℤ) =
      2 • ∑ p ∈ G.crossings, (G.crossingSign p.1 p.2 : ℤ) := by
    simp only [gaussCode_sign_visit]
    exact ((visitOrderIso hG c₀).toEquiv.sum_comp _).trans
      (CrossingVisit.sum_crossing fun p ↦ (G.crossingSign p.1 p.2 : ℤ))
  rw [nsmul_eq_mul, Nat.cast_ofNat] at hgrid
  exact mul_left_cancel₀ two_ne_zero ((gaussCode hG c₀).sum_sign_visit.symm.trans hgrid)

end GridDiagram

end TauCeti
