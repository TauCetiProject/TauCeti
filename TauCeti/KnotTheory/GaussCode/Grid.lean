/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.GaussCode.Basic
public import TauCeti.KnotTheory.Grid.TorusLink.Crossings
public import TauCeti.KnotTheory.Grid.Unknot.Crossings

/-!
# The Gauss code of a grid knot

A grid diagram `G` of grid number `n` is drawn in the plane as follows (Ozsváth–Stipsicz–Szabó,
Section 3.1). In each column a vertical segment joins the `X`-marking to the `O`-marking, and in
each row a horizontal segment joins the `O`-marking to the `X`-marking; the link is oriented from
`X` to `O` along the columns and from `O` to `X` along the rows, which is the traversal recorded
by `TauCeti.GridDiagram.componentPerm`. Wherever a vertical segment meets a horizontal one away
from the markings, the vertical segment crosses over the horizontal one. This file reads off the
diagram of a knot grid as a based oriented Gauss code, the grid-to-diagram correspondence of the
knot presentations.

* **Crossings and signs.** The crossings of the planar diagram
  (`TauCeti.GridDiagram.crossings`) and their signs (`TauCeti.GridDiagram.crossingSign`) are
  defined in `TauCeti.KnotTheory.Grid.Diagram.Crossings`.
* **The traversal.** For a knot grid, start at the `X`-marking of a column `c₀`. The traversal
  runs along the vertical segment of `c₀` to its `O`-marking, along the horizontal segment of that
  row to its `X`-marking, in the column `componentPerm c₀`, and so on. If `c` is reached after
  `k` steps of the component permutation (`TauCeti.GridDiagram.IsKnot.traversalIndex`, defined in
  `TauCeti.KnotTheory.Grid.Diagram.Components`), then the vertical segment of column `c` is the
  segment number `2 k` of the traversal and the horizontal segment leaving its `O`-marking the
  segment number `2 k + 1`. A crossing is passed twice, once on
  its vertical segment, over, and once on its horizontal segment, under; the time of a pass
  (`TauCeti.GridDiagram.IsKnot.visitTime`) is the index of its segment together with the distance
  travelled along that segment, ordered lexicographically. Distinct passes have distinct times
  (`TauCeti.GridDiagram.IsKnot.visitTime_injective`).

Listing the passes by increasing time (`TauCeti.GridDiagram.IsKnot.visitEquiv`) gives the based
oriented Gauss code `TauCeti.GridDiagram.IsKnot.gaussCode`, built with
`TauCeti.BasedOrientedGaussCode.ofPerfectMatching`; its writhe is the sum of the crossing signs
(`TauCeti.GridDiagram.IsKnot.writhe_gaussCode`). It can be passed on to an oriented PD-code by
`TauCeti.BasedOrientedGaussCode.toOrientedPDCode`. The construction adapts that of
`Polygon.gaussCode` in `TauCeti.KnotTheory.GaussCode.Polygon.Basic`, the Gauss code of a projected
polygonal knot, whose crossing passes are likewise listed by increasing time.

Two families of grids check the conventions. The standard unknot grids have no crossings at all
(`TauCeti.GridDiagram.crossings_unknot`), so their Gauss code is the crossing-free code
(`TauCeti.GridDiagram.sigma_mk_gaussCode_unknot`). Every crossing of the standard torus link grid
`TauCeti.GridDiagram.torusLink p q` is negative (`TauCeti.GridDiagram.crossingSign_torusLink`), so
the writhe of its Gauss code is minus the number of crossings; on the `5 × 5` trefoil grid there
are three crossings and the writhe is `-3`
(`TauCeti.GridDiagram.writhe_gaussCode_torusLink_one_two`). These are the signs of the left-handed
trefoil, the mirror of the positive torus knot, consistent with the value `τ = -1` of that grid.

That the based code depends on the base column only through a cyclic rotation, and that grid moves
change the code by Reidemeister moves, are not proved here.

## Main definitions

* `TauCeti.GridDiagram.IsKnot.visitTime`: the time at which the traversal passes a crossing.
* `TauCeti.GridDiagram.IsKnot.visitEquiv`: the passes of the traversal, in order.
* `TauCeti.GridDiagram.IsKnot.gaussCode`: the based oriented Gauss code of a knot grid.

## Main results

* `TauCeti.GridDiagram.IsKnot.strictMono_visitTime_visitEquiv`: the passes are listed in the order
  of the traversal.
* `TauCeti.GridDiagram.IsKnot.gaussCode_over`,
  `TauCeti.GridDiagram.IsKnot.gaussCode_visit_eq_visit_iff`,
  `TauCeti.GridDiagram.IsKnot.gaussCode_sign_visit`: the over passes are the vertical ones, two
  passes share a crossing label exactly when they pass the same crossing, and the sign of a
  crossing label is the sign of its crossing.
* `TauCeti.GridDiagram.IsKnot.gaussCode_visit_lt_visit_iff`: crossings are labelled in the order
  of their first passes.
* `TauCeti.GridDiagram.IsKnot.writhe_gaussCode`: the writhe is the sum of the crossing signs.
* `TauCeti.GridDiagram.sigma_mk_gaussCode_unknot`: the unknot grids have the crossing-free code.
* `TauCeti.GridDiagram.writhe_gaussCode_torusLink`: the writhe of a torus knot grid is minus its
  number of crossings.
* `TauCeti.GridDiagram.writhe_gaussCode_torusLink_one_two`: the trefoil grid has writhe `-3`.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical
  Surveys and Monographs 208, 2015, Section 3.1, for the planar diagram of a grid diagram.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1, for
  Gauss codes and crossing signs.
-/

public section

noncomputable section

open Set Function

namespace TauCeti

namespace GridDiagram

variable {n : ℕ}

/-! ### The traversal of a knot grid -/

variable {G : GridDiagram n} (hG : G.IsKnot) (c₀ : Fin n)

/-- The **time** at which the traversal of a knot grid, starting at the `X`-marking of column
`c₀`, passes a crossing `p`: vertically (`b = true`) or horizontally (`b = false`). It is the
pair, ordered lexicographically, of the index of the segment carrying the pass and the distance
travelled along that segment. The vertical segment of column `c`, run from its `X`-marking to its
`O`-marking, has index `2 k`, and the horizontal segment leaving that `O`-marking has index
`2 k + 1`, where `k` is the traversal index of `c`. -/
def IsKnot.visitTime (v : G.crossings × Bool) : ℕ ×ₗ ℕ :=
  if v.2 then toLex (2 * hG.traversalIndex c₀ v.1.1.1,
    max (G.X v.1.1.1 : ℕ) v.1.1.2 - min (G.X v.1.1.1 : ℕ) v.1.1.2)
  else toLex (2 * hG.traversalIndex c₀ (G.O.transpose v.1.1.2) + 1,
    max (G.O.transpose v.1.1.2 : ℕ) v.1.1.1 - min (G.O.transpose v.1.1.2 : ℕ) v.1.1.1)

/-- The time of the vertical pass of a crossing in column `c`: the segment of index `2 k`, at the
distance of the crossing from the `X`-marking of column `c`. -/
@[simp]
theorem IsKnot.visitTime_true (p : G.crossings) :
    hG.visitTime c₀ (p, true) =
      toLex (2 * hG.traversalIndex c₀ p.1.1,
        max (G.X p.1.1 : ℕ) p.1.2 - min (G.X p.1.1 : ℕ) p.1.2) :=
  (rfl)

/-- The time of the horizontal pass of a crossing in row `r`: the segment of index `2 k + 1`
leaving the `O`-marking of row `r`, at the distance of the crossing from that marking. -/
@[simp]
theorem IsKnot.visitTime_false (p : G.crossings) :
    hG.visitTime c₀ (p, false) =
      toLex (2 * hG.traversalIndex c₀ (G.O.transpose p.1.2) + 1,
        max (G.O.transpose p.1.2 : ℕ) p.1.1 - min (G.O.transpose p.1.2 : ℕ) p.1.1) :=
  (rfl)

/-- **Distinct passes happen at distinct times.** -/
theorem IsKnot.visitTime_injective : Injective (hG.visitTime c₀) := by
  rintro ⟨⟨⟨c, r⟩, hp⟩, b⟩ ⟨⟨⟨c', r'⟩, hp'⟩, b'⟩ h
  have hx := (G.mem_crossings.mp hp)
  have hx' := (G.mem_crossings.mp hp')
  rw [isCrossing_iff] at hx hx'
  cases b <;> cases b' <;>
    simp only [visitTime_true, visitTime_false, toLex_inj, Prod.mk.injEq] at h
  · -- Two horizontal passes: the rows, then the columns along the row agree.
    obtain ⟨h₁, h₂⟩ := h
    have hrow : G.O.transpose r = G.O.transpose r' :=
      hG.traversalIndex_injective c₀ (by omega)
    obtain rfl : r = r' := by
      rw [← G.O.apply_transpose_apply r, hrow, G.O.apply_transpose_apply]
    have hc := hx.2
    have hc' := hx'.2
    simp only [mem_uIoo, Fin.lt_def] at hc hc'
    obtain rfl : c = c' := Fin.ext (by omega)
    rfl
  · omega
  · omega
  · -- Two vertical passes: the columns, then the rows along the column agree.
    obtain ⟨h₁, h₂⟩ := h
    obtain rfl : c = c' := hG.traversalIndex_injective c₀ (by omega)
    have hr := hx.1
    have hr' := hx'.1
    simp only [mem_uIoo, Fin.lt_def] at hr hr'
    obtain rfl : r = r' := Fin.ext (by omega)
    rfl

/-! ### The Gauss code -/

/-- The times of all passes of the traversal. -/
private def crossingTimes : Finset (ℕ ×ₗ ℕ) :=
  Finset.univ.image (hG.visitTime c₀)

/-- The passes of the traversal are in bijection with their times. -/
private def visitTimeEquiv : G.crossings × Bool ≃ crossingTimes hG c₀ :=
  Equiv.ofBijective (fun v => ⟨hG.visitTime c₀ v, Finset.mem_image_of_mem _ (Finset.mem_univ v)⟩)
    ⟨fun _ _ h => hG.visitTime_injective c₀ (congrArg Subtype.val h), by
      rintro ⟨t, ht⟩
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp ht
      exact ⟨v, rfl⟩⟩

private theorem coe_visitTimeEquiv (v : G.crossings × Bool) :
    (visitTimeEquiv hG c₀ v : ℕ ×ₗ ℕ) = hG.visitTime c₀ v :=
  rfl

private theorem card_crossingTimes :
    Fintype.card (crossingTimes hG c₀) = 2 * G.crossings.card := by
  rw [← Fintype.card_congr (visitTimeEquiv hG c₀), Fintype.card_prod, Fintype.card_coe,
    Fintype.card_bool, Nat.mul_comm]

variable (G) in
/-- The perfect matching exchanging the two passes of each crossing. -/
private def passPartner : PerfectMatching (G.crossings × Bool) :=
  PerfectMatching.mk
    { toFun v := (v.1, !v.2)
      invFun v := (v.1, !v.2)
      left_inv v := by simp
      right_inv v := by simp }
    (fun v => by simp) (fun v h => Bool.not_ne_self v.2 (congrArg Prod.snd h))

private theorem passPartner_apply (v : G.crossings × Bool) :
    (passPartner G).val v = (v.1, !v.2) := by
  rw [passPartner, PerfectMatching.val_mk]
  -- The underlying function of the equivalence built in `passPartner` is `v ↦ (v.1, !v.2)`.
  rfl

/-- The **based oriented Gauss code of a knot grid**, read from the traversal starting at the
`X`-marking of the column `c₀`. Its visits are the passes of the traversal through the crossings
of the planar diagram, in the order of their times, the vertical passes over and the horizontal
ones under; the sign of a crossing is `TauCeti.GridDiagram.crossingSign`. Crossings are labelled
in the order of their first passes. -/
def IsKnot.gaussCode : BasedOrientedGaussCode G.crossings.card :=
  BasedOrientedGaussCode.ofPerfectMatching (card_crossingTimes hG c₀)
    (PerfectMatching.congr (visitTimeEquiv hG c₀) (passPartner G))
    (fun t => ((visitTimeEquiv hG c₀).symm t).2)
    (fun t => by simp [passPartner_apply])
    (fun t => G.crossingSign ((visitTimeEquiv hG c₀).symm t).1)

/-- The passes of the traversal of a knot grid, listed in the order in which the traversal from
the `X`-marking of column `c₀` meets them. The `i`-th visit of
`TauCeti.GridDiagram.IsKnot.gaussCode` is the pass `visitEquiv i`. -/
def IsKnot.visitEquiv : Fin (2 * G.crossings.card) ≃ G.crossings × Bool :=
  (Fintype.orderIsoFinOfCardEq _ (card_crossingTimes hG c₀)).toEquiv.trans
    (visitTimeEquiv hG c₀).symm

private theorem visitTime_visitEquiv (i : Fin (2 * G.crossings.card)) :
    hG.visitTime c₀ (hG.visitEquiv c₀ i) =
      (Fintype.orderIsoFinOfCardEq _ (card_crossingTimes hG c₀) i : ℕ ×ₗ ℕ) := by
  rw [IsKnot.visitEquiv, Equiv.trans_apply, ← coe_visitTimeEquiv, Equiv.apply_symm_apply]
  -- Both sides are the value of the `i`-th element of `crossingTimes`; the coercion of an order
  -- isomorphism to an equivalence does not change the function.
  rfl

/-- **The passes are listed in the order of the traversal**: the time of the `i`-th pass increases
with `i`. -/
theorem IsKnot.strictMono_visitTime_visitEquiv :
    StrictMono fun i => hG.visitTime c₀ (hG.visitEquiv c₀ i) := fun i j hij => by
  simp only [visitTime_visitEquiv]
  exact Subtype.coe_lt_coe.mpr ((Fintype.orderIsoFinOfCardEq _ _).strictMono hij)

/-- The pass at the `i`-th visit comes before the pass at the `j`-th exactly when `i < j`. -/
theorem IsKnot.visitTime_visitEquiv_lt_visitTime_visitEquiv_iff
    {i j : Fin (2 * G.crossings.card)} :
    hG.visitTime c₀ (hG.visitEquiv c₀ i) < hG.visitTime c₀ (hG.visitEquiv c₀ j) ↔ i < j :=
  (hG.strictMono_visitTime_visitEquiv c₀).lt_iff_lt

/-- The traversal passes over a crossing exactly on its vertical segment. -/
@[simp]
theorem IsKnot.gaussCode_over (i : Fin (2 * G.crossings.card)) :
    (hG.gaussCode c₀).over i = (hG.visitEquiv c₀ i).2 := by
  rw [IsKnot.gaussCode, BasedOrientedGaussCode.ofPerfectMatching_over]
  -- Both sides read the pass at the `i`-th time, which is how `visitEquiv` is defined.
  rfl

/-- The partner of a visit is the other pass through the same crossing. -/
@[simp]
theorem IsKnot.visitEquiv_gaussCode_partner (i : Fin (2 * G.crossings.card)) :
    hG.visitEquiv c₀ ((hG.gaussCode c₀).partner.val i) =
      ((hG.visitEquiv c₀ i).1, !(hG.visitEquiv c₀ i).2) := by
  rw [IsKnot.visitEquiv, Equiv.trans_apply, OrderIso.coe_toEquiv, IsKnot.gaussCode,
    BasedOrientedGaussCode.orderIsoFinOfCardEq_ofPerfectMatching_partner,
    PerfectMatching.congr_val_apply, Equiv.symm_apply_apply, passPartner_apply]
  -- The left side is the pass at the `i`-th time with its direction flipped, as on the right.
  rfl

/-- **Two visits carry the same crossing label exactly when they pass the same crossing.** -/
theorem IsKnot.gaussCode_visit_eq_visit_iff {i j : Fin (2 * G.crossings.card)} :
    (hG.gaussCode c₀).visit i = (hG.gaussCode c₀).visit j ↔
      (hG.visitEquiv c₀ i).1 = (hG.visitEquiv c₀ j).1 := by
  rw [BasedOrientedGaussCode.visit_eq_iff]
  constructor
  · rintro (rfl | rfl)
    · rfl
    · rw [hG.visitEquiv_gaussCode_partner]
  · intro h
    by_cases hb : (hG.visitEquiv c₀ i).2 = (hG.visitEquiv c₀ j).2
    · exact .inl ((hG.visitEquiv c₀).injective (Prod.ext h hb)).symm
    · refine .inr ((hG.visitEquiv c₀).injective ?_)
      rw [hG.visitEquiv_gaussCode_partner]
      exact Prod.ext h.symm (by cases h₁ : (hG.visitEquiv c₀ i).2 <;> simp_all)

/-- **Crossings are labelled in the order of their first passes.** The crossing met at the `i`-th
visit has a smaller label than the one met at the `j`-th visit exactly when the earlier of the two
passes through the first crossing comes before the earlier of the two passes through the
second. -/
theorem IsKnot.gaussCode_visit_lt_visit_iff (i j : Fin (2 * G.crossings.card)) :
    (hG.gaussCode c₀).visit i < (hG.gaussCode c₀).visit j ↔
      min (hG.visitTime c₀ (hG.visitEquiv c₀ i))
          (hG.visitTime c₀ (hG.visitEquiv c₀ ((hG.gaussCode c₀).partner.val i))) <
        min (hG.visitTime c₀ (hG.visitEquiv c₀ j))
          (hG.visitTime c₀ (hG.visitEquiv c₀ ((hG.gaussCode c₀).partner.val j))) := by
  simp only [visitTime_visitEquiv]
  rw [IsKnot.gaussCode, BasedOrientedGaussCode.ofPerfectMatching_visit_lt_visit_iff,
    BasedOrientedGaussCode.orderIsoFinOfCardEq_ofPerfectMatching_partner,
    BasedOrientedGaussCode.orderIsoFinOfCardEq_ofPerfectMatching_partner,
    ← (Subtype.mono_coe _).map_min, ← (Subtype.mono_coe _).map_min, Subtype.coe_lt_coe]

/-- **The sign of a crossing label is the sign of its crossing.** -/
theorem IsKnot.gaussCode_sign_visit (i : Fin (2 * G.crossings.card)) :
    (hG.gaussCode c₀).sign ((hG.gaussCode c₀).visit i) =
      G.crossingSign (hG.visitEquiv c₀ i).1 := by
  rw [IsKnot.gaussCode, BasedOrientedGaussCode.ofPerfectMatching_sign_visit]
  · -- The sign at the `i`-th time is that of the crossing of the pass `visitEquiv i`.
    rfl
  · intro t
    simp [passPartner_apply]

/-- **The writhe of the Gauss code of a knot grid is the sum of the signs of its crossings.** -/
theorem IsKnot.writhe_gaussCode :
    (hG.gaussCode c₀).writhe = ∑ p ∈ G.crossings, (G.crossingSign p : ℤ) := by
  set D := hG.gaussCode c₀
  -- Summing the sign of the crossing met at each of the `2 m` visits counts every crossing twice,
  -- both when the visits are read as Gauss-code labels and when they are read as passes.
  have hcode := D.sum_sign_visit
  have hgrid :
      ∑ i, (D.sign (D.visit i) : ℤ) = 2 * ∑ p ∈ G.crossings, (G.crossingSign p : ℤ) := by
    simp only [D, hG.gaussCode_sign_visit]
    rw [(hG.visitEquiv c₀).sum_comp (fun v => (G.crossingSign v.1 : ℤ)), Fintype.sum_prod_type,
      ← Finset.sum_coe_sort G.crossings, Finset.mul_sum]
    simp [two_mul]
  omega

/-! ### Unknot and torus link grids -/

/-- **The Gauss code of an unknot grid is the crossing-free code**, from every base column. -/
theorem sigma_mk_gaussCode_unknot (n : ℕ) (c₀ : Fin (n + 2)) :
    (⟨_, (isKnot_unknot n).gaussCode c₀⟩ : Σ m, BasedOrientedGaussCode m) =
      ⟨0, BasedOrientedGaussCode.empty⟩ := by
  generalize (isKnot_unknot n).gaussCode c₀ = D
  revert D
  rw [card_crossings_unknot]
  intro D
  rw [D.eq_empty]

/-- The writhe of the Gauss code of a torus knot grid is minus its number of crossings. -/
theorem writhe_gaussCode_torusLink {p q : ℕ} (h : (torusLink p q).IsKnot)
    (c₀ : Fin (p + 1 + (q + 1))) :
    (h.gaussCode c₀).writhe = -((torusLink p q).crossings.card : ℤ) := by
  rw [h.writhe_gaussCode, Finset.sum_congr rfl fun x hx => by
    rw [crossingSign_torusLink p q hx]]
  simp

/-- **The writhe of the trefoil grid is `-3`**, from every base column. -/
theorem writhe_gaussCode_torusLink_one_two (c₀ : Fin (1 + 1 + (2 + 1))) :
    (isKnot_torusLink_one_two.gaussCode c₀).writhe = -3 := by
  rw [writhe_gaussCode_torusLink, card_crossings_torusLink_one_two]
  norm_num

end GridDiagram

end TauCeti
