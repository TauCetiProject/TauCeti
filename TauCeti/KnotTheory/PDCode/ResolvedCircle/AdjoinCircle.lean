/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Circle
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Saddle

/-!
# The circles of a code with an adjoined circle

Adjoining a crossing-free circle to a PD-code (`TauCeti.PDCode.adjoinCircle`) keeps the
crossings, arcs and smoothings, and adds one crossing-free component, labelled last. So in every
smoothing `s` the circles of `D.adjoinCircle` are those of `D` together with one new circle
(`TauCeti.PDCode.adjoinCircleResolvedCircleEquiv`): the circle through a half-edge goes to the
circle through the same half-edge, the crossing-free labels of `D` keep their labels, and the
new label goes to the extra point `()`.

The new circle meets no crossing, so it is untouched by every saddle: along an edge of the cube of
resolutions, the saddle correspondence of `D.adjoinCircle` is that of `D` together with the
identity on the new circle
(`TauCeti.PDCode.adjoinCircleResolvedCircleEquiv_saddleResolvedCircleMap`).
This is the combinatorial input for splitting the Khovanov complex of `D.adjoinCircle` into two
copies of that of `D`.

## Main definitions

* `TauCeti.PDCode.adjoinCircleCrossingCircleEquiv`: the circles meeting a crossing are unchanged.
* `TauCeti.PDCode.adjoinCircleResolvedCircleEquiv`: all circles of `D.adjoinCircle` smoothed by `s`
  are those of `D` and one more.

## Main results

* `TauCeti.PDCode.card_circlesAt_adjoinCircle`: the same number of circles passes through each
  crossing.
* `TauCeti.PDCode.adjoinCircleResolvedCircleEquiv_saddleResolvedCircleMap`: the saddle
  correspondences agree, and fix the new circle.
-/

public section

namespace TauCeti.PDCode

open Finset

variable {n : ℕ} (D : PDCode n)

/-- Adjoining a circle does not change the relation generating the circles that meet a
crossing. -/
@[simp]
theorem circleStep_adjoinCircle (s : Fin n → Bool) :
    D.adjoinCircle.CircleStep s = D.CircleStep s := by
  funext x y
  simp only [circleStep_iff, adjoinCircle_edgePair, smoothingChoice_adjoinCircle,
    smoothingTurn_adjoinCircle]

/-- The circles meeting a crossing are unchanged by adjoining a circle: the circle through a
half-edge corresponds to the circle through the same half-edge. -/
def adjoinCircleCrossingCircleEquiv (s : Fin n → Bool) :
    D.adjoinCircle.CrossingCircle s ≃ D.CrossingCircle s :=
  Quotient.congr (Equiv.refl _) fun x y ↦ by
    rw [Equiv.refl_apply, Equiv.refl_apply, circleStep_adjoinCircle]

/-- The correspondence of circles meeting a crossing sends the circle through a half-edge to
the circle through the same half-edge. -/
@[simp]
theorem adjoinCircleCrossingCircleEquiv_mk (s : Fin n → Bool) (x : Fin (4 * n)) :
    D.adjoinCircleCrossingCircleEquiv s ⟦x⟧ = ⟦x⟧ :=
  (rfl)

/-- The circles of `D.adjoinCircle` smoothed by `s` are the circles of `D` smoothed by `s`,
together with the adjoined circle `()`. The crossing-free labels of `D` keep their labels, and
the last label is the adjoined circle. -/
def adjoinCircleResolvedCircleEquiv (s : Fin n → Bool) :
    D.adjoinCircle.ResolvedCircle s ≃ D.ResolvedCircle s ⊕ Unit :=
  ((D.adjoinCircleCrossingCircleEquiv s).sumCongr
    ((finCongr (adjoinCircle_crossinglessComponentCount D)).trans
      (finSumFinEquiv.symm.trans ((Equiv.refl _).sumCongr finOneEquiv)))).trans
    (Equiv.sumAssoc _ _ _).symm

/-- A circle meeting a crossing corresponds to the circle through the same half-edge. -/
@[simp]
theorem adjoinCircleResolvedCircleEquiv_inl_mk (s : Fin n → Bool) (x : Fin (4 * n)) :
    D.adjoinCircleResolvedCircleEquiv s (.inl ⟦x⟧) = .inl (.inl ⟦x⟧) :=
  (rfl)

/-- The crossing-free circles of `D` keep their labels in `D.adjoinCircle`. -/
@[simp]
theorem adjoinCircleResolvedCircleEquiv_symm_inl_inr (s : Fin n → Bool)
    (i : Fin D.crossinglessComponentCount) :
    (D.adjoinCircleResolvedCircleEquiv s).symm (.inl (.inr i)) =
      .inr (Fin.cast (adjoinCircle_crossinglessComponentCount D).symm i.castSucc) := by
  rw [Equiv.symm_apply_eq]
  simp [adjoinCircleResolvedCircleEquiv]

/-- The adjoined circle has the last crossing-free label of `D.adjoinCircle`. -/
@[simp]
theorem adjoinCircleResolvedCircleEquiv_symm_inr (s : Fin n → Bool) :
    (D.adjoinCircleResolvedCircleEquiv s).symm (.inr ()) =
      .inr (Fin.cast (adjoinCircle_crossinglessComponentCount D).symm
        (Fin.last D.crossinglessComponentCount)) := by
  rw [Equiv.symm_apply_eq]
  simp [adjoinCircleResolvedCircleEquiv]

/-- The same number of circles passes through each crossing after adjoining a circle. -/
@[simp]
theorem card_circlesAt_adjoinCircle (s : Fin n → Bool) (c : Fin n) :
    #(D.adjoinCircle.circlesAt s c) = #(D.circlesAt s c) := by
  rw [← card_map (D.adjoinCircleCrossingCircleEquiv s).toEmbedding]
  congr 1
  ext C
  simp [mem_circlesAt, Equiv.eq_symm_apply]

variable {s t : Fin n → Bool} {c : Fin n} (hst : ∀ j, j ≠ c → s j = t j)

/-- **The adjoined circle is untouched by every saddle.** Along an edge of the cube of
resolutions, the saddle correspondence of `D.adjoinCircle` is that of `D` on the circles of `D`,
and the identity on the adjoined circle. -/
theorem adjoinCircleResolvedCircleEquiv_saddleResolvedCircleMap
    (ht : #(D.circlesAt t c) = 1) (ht' : #(D.adjoinCircle.circlesAt t c) = 1)
    (C : D.adjoinCircle.ResolvedCircle s) :
    D.adjoinCircleResolvedCircleEquiv t (D.adjoinCircle.saddleResolvedCircleMap hst ht' C) =
      Sum.map (D.saddleResolvedCircleMap hst ht) id (D.adjoinCircleResolvedCircleEquiv s C) := by
  rcases C with C | i
  · induction C using Quotient.ind
    simp
  · simp only [adjoinCircleResolvedCircleEquiv, saddleResolvedCircleMap_inr, Equiv.trans_apply,
      Equiv.sumCongr_apply, Sum.map_inr]
    rcases finSumFinEquiv.symm (finCongr (adjoinCircle_crossinglessComponentCount D) i) with
      j | j <;> simp

end TauCeti.PDCode
