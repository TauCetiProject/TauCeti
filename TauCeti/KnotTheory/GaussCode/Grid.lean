/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Set.UnorderedInterval
public import TauCeti.KnotTheory.GaussCode.Basic
public import TauCeti.KnotTheory.Grid.TorusLink.Basic

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

* **Crossings.** The vertical segment of column `c` and the horizontal segment of row `r` meet in
  the square `(c, r)` exactly when `r` lies strictly between the rows of the two markings of
  column `c` and `c` strictly between the columns of the two markings of row `r`
  (`TauCeti.GridDiagram.IsCrossing`); the segments of a column and of a row sharing a marking meet
  only at that marking, which is a corner of the diagram rather than a crossing. The crossings form
  the finite set `TauCeti.GridDiagram.crossings`.
* **Signs.** The vertical strand at a crossing passes over, so the crossing is positive, in the
  right-handed convention of Lickorish, exactly when a counterclockwise quarter turn takes the
  direction of the vertical strand to that of the horizontal one: the vertical strand runs up and
  the horizontal one to the left, or down and to the right (`TauCeti.GridDiagram.crossingSign`).
* **The traversal.** For a knot grid, start at the `X`-marking of a column `c₀`. The traversal
  runs along the vertical segment of `c₀` to its `O`-marking, along the horizontal segment of that
  row to its `X`-marking, in the column `componentPerm c₀`, and so on. If `c` is reached after
  `k` steps of the component permutation (`TauCeti.GridDiagram.IsKnot.traversalIndex`), then the
  vertical segment of column `c` is the segment number `2 k` of the traversal and the horizontal
  segment leaving its `O`-marking the segment number `2 k + 1`. A crossing is passed twice, once on
  its vertical segment, over, and once on its horizontal segment, under; the time of a pass
  (`TauCeti.GridDiagram.IsKnot.visitTime`) is the index of its segment together with the distance
  travelled along that segment, ordered lexicographically. Distinct passes have distinct times
  (`TauCeti.GridDiagram.IsKnot.visitTime_injective`).

Listing the passes by increasing time (`TauCeti.GridDiagram.IsKnot.visitEquiv`) gives the based
oriented Gauss code `TauCeti.GridDiagram.IsKnot.gaussCode`, built with
`TauCeti.BasedOrientedGaussCode.ofPerfectMatching`; its writhe is the sum of the crossing signs
(`TauCeti.GridDiagram.IsKnot.writhe_gaussCode`). It can be passed on to an oriented PD-code by
`TauCeti.BasedOrientedGaussCode.toOrientedPDCode`.

Two families of grids check the conventions. The standard unknot grids have no crossings at all,
so their Gauss code is the crossing-free code
(`TauCeti.GridDiagram.sigma_mk_gaussCode_unknot`). Every crossing of the standard torus link grid
`TauCeti.GridDiagram.torusLink p q` is negative (`TauCeti.GridDiagram.crossingSign_torusLink`); on
the `5 × 5` trefoil grid there are three crossings and the writhe is `-3`
(`TauCeti.GridDiagram.writhe_gaussCode_torusLink_one_two`). These are the signs of the left-handed
trefoil, the mirror of the positive torus knot, consistent with the value `τ = -1` of that grid.

That the based code depends on the base column only through a cyclic rotation, and that grid moves
change the code by Reidemeister moves, are not proved here.

## Main definitions

* `TauCeti.GridDiagram.IsCrossing`, `TauCeti.GridDiagram.crossings`: the crossings of the planar
  diagram of a grid.
* `TauCeti.GridDiagram.crossingSign`: the sign of a crossing.
* `TauCeti.GridDiagram.IsKnot.traversalIndex`: the number of steps of the component permutation
  from the base column to a column.
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
* `TauCeti.GridDiagram.IsKnot.writhe_gaussCode`: the writhe is the sum of the crossing signs.
* `TauCeti.GridDiagram.crossings_unknot`, `TauCeti.GridDiagram.sigma_mk_gaussCode_unknot`: the
  unknot grids have the crossing-free code.
* `TauCeti.GridDiagram.crossingSign_torusLink`, `TauCeti.GridDiagram.writhe_gaussCode_torusLink`:
  the torus link grids have only negative crossings.
* `TauCeti.GridDiagram.crossings_torusLink_one_two`,
  `TauCeti.GridDiagram.writhe_gaussCode_torusLink_one_two`: the trefoil grid has three crossings
  and writhe `-3`.

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

/-- Membership in an open unordered interval of `Fin n`, in terms of values. -/
private theorem mem_uIoo_iff_val {a b x : Fin n} :
    x ∈ uIoo a b ↔ (a : ℕ) < x ∧ (x : ℕ) < b ∨ (b : ℕ) < x ∧ (x : ℕ) < a := by
  rcases le_total a b with hab | hab
  · rw [uIoo_of_le hab, mem_Ioo, Fin.lt_def, Fin.lt_def]
    have : (a : ℕ) ≤ b := hab
    omega
  · rw [uIoo_of_ge hab, mem_Ioo, Fin.lt_def, Fin.lt_def]
    have : (b : ℕ) ≤ a := hab
    omega

/-- Two points strictly between `a` and `b` at the same distance from the endpoint `b` agree. -/
private theorem eq_of_dist_eq_of_mem_uIoo {a b x y : Fin n} (hx : x ∈ uIoo a b)
    (hy : y ∈ uIoo a b) (h : max (b : ℕ) x - min (b : ℕ) x = max (b : ℕ) y - min (b : ℕ) y) :
    x = y := by
  rw [mem_uIoo_iff_val] at hx hy
  exact Fin.ext (by omega)

variable (G : GridDiagram n)

/-! ### Crossings -/

/-- The square `(c, r)` is a **crossing** of the planar diagram of the grid diagram `G`: the row
`r` lies strictly between the rows of the `O`- and `X`-markings of column `c`, so that the
vertical segment of column `c` runs through the square, and the column `c` lies strictly between
the columns of the two markings of row `r`, so that the horizontal segment of row `r` runs
through it. -/
def IsCrossing (p : Fin n × Fin n) : Prop :=
  p.2 ∈ uIoo (G.O p.1) (G.X p.1) ∧ p.1 ∈ uIoo (G.O.transpose p.2) (G.X.transpose p.2)

instance : DecidablePred G.IsCrossing := fun p =>
  inferInstanceAs (Decidable (p.2 ∈ Ioo (G.O p.1 ⊓ G.X p.1) (G.O p.1 ⊔ G.X p.1) ∧
    p.1 ∈ Ioo (G.O.transpose p.2 ⊓ G.X.transpose p.2) (G.O.transpose p.2 ⊔ G.X.transpose p.2)))

/-- The defining property of a crossing. -/
theorem isCrossing_iff {p : Fin n × Fin n} :
    G.IsCrossing p ↔
      p.2 ∈ uIoo (G.O p.1) (G.X p.1) ∧ p.1 ∈ uIoo (G.O.transpose p.2) (G.X.transpose p.2) :=
  Iff.rfl

/-- The crossings of the planar diagram of a grid diagram. -/
def crossings : Finset (Fin n × Fin n) :=
  {p | G.IsCrossing p}

@[simp]
theorem mem_crossings {p : Fin n × Fin n} : p ∈ G.crossings ↔ G.IsCrossing p := by
  simp [crossings]

/-- The **sign** of the crossing in the square `(c, r)`. The vertical strand of column `c`, running
from the `X`-marking to the `O`-marking, passes over the horizontal strand of row `r`, running
from the `O`-marking to the `X`-marking. The crossing is positive when the vertical strand runs up
and the horizontal one to the left, or down and to the right, and negative otherwise. -/
def crossingSign (p : Fin n × Fin n) : ℤˣ :=
  if (G.X p.1 < G.O p.1 ↔ G.X.transpose p.2 < G.O.transpose p.2) then 1 else -1

/-- A crossing is positive exactly when its vertical strand runs up while its horizontal strand
runs to the left, or down while it runs to the right. -/
theorem crossingSign_eq_one_iff {p : Fin n × Fin n} :
    G.crossingSign p = 1 ↔ (G.X p.1 < G.O p.1 ↔ G.X.transpose p.2 < G.O.transpose p.2) := by
  unfold crossingSign
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by decide) h

/-- A crossing is negative exactly when it is not positive. -/
theorem crossingSign_eq_neg_one_iff {p : Fin n × Fin n} :
    G.crossingSign p = -1 ↔ ¬(G.X p.1 < G.O p.1 ↔ G.X.transpose p.2 < G.O.transpose p.2) := by
  unfold crossingSign
  split_ifs with h
  · exact iff_of_false (by decide) (not_not_intro h)
  · exact iff_of_true rfl h

/-! ### The traversal of a knot grid -/

variable {G}

/-- On a knot grid the component permutation, a single cycle through all columns, leads from any
column to any other. -/
theorem IsKnot.exists_pow_componentPerm_apply_eq (hG : G.IsKnot) (c₀ c : Fin n) :
    ∃ k : ℕ, (G.componentPerm ^ k) c₀ = c :=
  (G.isKnot_iff_componentPerm_isCycle.mp hG).exists_pow_eq (G.componentPerm_apply_ne_self c₀)
    (G.componentPerm_apply_ne_self c)

/-- The **traversal index** of a column `c` from a base column `c₀` of a knot grid: the least
number of steps of the component permutation leading from `c₀` to `c`. -/
def IsKnot.traversalIndex (hG : G.IsKnot) (c₀ c : Fin n) : ℕ :=
  Nat.find (hG.exists_pow_componentPerm_apply_eq c₀ c)

variable (hG : G.IsKnot) (c₀ : Fin n)

/-- The component permutation leads from the base column to `c` in `traversalIndex c₀ c` steps. -/
@[simp]
theorem IsKnot.pow_traversalIndex_apply (c : Fin n) :
    (G.componentPerm ^ hG.traversalIndex c₀ c) c₀ = c :=
  Nat.find_spec (hG.exists_pow_componentPerm_apply_eq c₀ c)

/-- The traversal index is at most any number of steps leading from the base column to `c`. -/
theorem IsKnot.traversalIndex_le {c : Fin n} {k : ℕ} (hk : (G.componentPerm ^ k) c₀ = c) :
    hG.traversalIndex c₀ c ≤ k :=
  Nat.find_min' _ hk

/-- The base column has traversal index `0`. -/
@[simp]
theorem IsKnot.traversalIndex_self : hG.traversalIndex c₀ c₀ = 0 :=
  Nat.le_zero.mp (hG.traversalIndex_le c₀ (pow_zero G.componentPerm ▸ rfl))

/-- The traversal index is less than the grid number. -/
theorem IsKnot.traversalIndex_lt (c : Fin n) : hG.traversalIndex c₀ c < n := by
  have hcyc := G.isKnot_iff_componentPerm_isCycle.mp hG
  have horder : orderOf G.componentPerm = n := by
    rw [hcyc.orderOf, support_componentPerm, Finset.card_univ, Fintype.card_fin]
  have hn : 0 < n := Nat.pos_of_ne_zero hG.ne_zero
  have hk := hG.pow_traversalIndex_apply c₀ c
  rw [← pow_mod_orderOf, horder] at hk
  exact (hG.traversalIndex_le c₀ hk).trans_lt (Nat.mod_lt _ hn)

/-- Distinct columns have distinct traversal indices. -/
theorem IsKnot.traversalIndex_injective : Injective (hG.traversalIndex c₀) := fun c c' h => by
  rw [← hG.pow_traversalIndex_apply c₀ c, ← hG.pow_traversalIndex_apply c₀ c', h]

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
    rw [uIoo_comm] at hc hc'
    obtain rfl : c = c' := eq_of_dist_eq_of_mem_uIoo hc hc' h₂
    rfl
  · omega
  · omega
  · -- Two vertical passes: the columns, then the rows along the column agree.
    obtain ⟨h₁, h₂⟩ := h
    obtain rfl : c = c' := hG.traversalIndex_injective c₀ (by omega)
    obtain rfl : r = r' := eq_of_dist_eq_of_mem_uIoo hx.1 hx'.1 h₂
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
  have hcode : ∑ i, (D.sign (D.visit i) : ℤ) = 2 * D.writhe := by
    rw [← D.visitDataEquiv.symm.sum_comp, Fintype.sum_prod_type,
      BasedOrientedGaussCode.writhe_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hvisit (b : Bool) : D.visit (D.visitDataEquiv.symm (c, b)) = c := by
      have h := D.visitDataEquiv.apply_symm_apply (c, b)
      rw [BasedOrientedGaussCode.visitDataEquiv_apply] at h
      exact congrArg Prod.fst h
    simp [hvisit, two_mul]
  have hgrid :
      ∑ i, (D.sign (D.visit i) : ℤ) = 2 * ∑ p ∈ G.crossings, (G.crossingSign p : ℤ) := by
    simp only [D, hG.gaussCode_sign_visit]
    rw [(hG.visitEquiv c₀).sum_comp (fun v => (G.crossingSign v.1 : ℤ)), Fintype.sum_prod_type,
      ← Finset.sum_coe_sort G.crossings, Finset.mul_sum]
    simp [two_mul]
  omega

/-! ### Unknot and torus link grids -/

/-- The standard unknot grids have no crossings: the vertical segment of every column but the last
spans no row, and the only row whose horizontal segment spans a column is the bottom one, which
meets the vertical segment of the last column only at its `X`-marking. -/
@[simp]
theorem crossings_unknot (n : ℕ) : (unknot n).crossings = ∅ := by
  ext ⟨c, r⟩
  simp only [mem_crossings, isCrossing_iff, Finset.notMem_empty, iff_false, not_and]
  intro hr hc
  -- The `X`-marking of a column `y` sits one row up, except in the last column.
  have hX (y : Fin (n + 2)) :
      ((unknot n).X y : ℕ) = y + 1 ∧ (y : ℕ) < n + 1 ∨
        ((unknot n).X y : ℕ) = 0 ∧ (y : ℕ) = n + 1 := by
    rw [unknot_X_apply_eq_add_one, Fin.val_add_one]
    split_ifs with h
    · exact .inr ⟨rfl, by simp [h]⟩
    · exact .inl ⟨rfl, by have := Fin.val_lt_last h; simpa using this⟩
  have hOt : (unknot n).O.transpose r = r := by
    simpa using (unknot n).O.transpose_apply_apply r
  have hXt := hX ((unknot n).X.transpose r)
  rw [(unknot n).X.apply_transpose_apply] at hXt
  rw [hOt] at hc
  rw [mem_uIoo_iff_val] at hr hc
  simp only [unknot_O_apply] at hr
  rcases hX c with hXc | hXc <;> omega

/-- The unknot grids have no crossings. -/
theorem card_crossings_unknot (n : ℕ) : (unknot n).crossings.card = 0 := by
  simp

/-- **The Gauss code of an unknot grid is the crossing-free code**, from every base column. -/
theorem sigma_mk_gaussCode_unknot (n : ℕ) (c₀ : Fin (n + 2)) :
    (⟨_, (isKnot_unknot n).gaussCode c₀⟩ : Σ m, BasedOrientedGaussCode m) =
      ⟨0, BasedOrientedGaussCode.empty⟩ := by
  generalize (isKnot_unknot n).gaussCode c₀ = D
  revert D
  rw [card_crossings_unknot]
  intro D
  rw [D.eq_empty]

/-- **Every crossing of a torus link grid is negative.** In the first `p + 1` columns the vertical
segment runs down from the `X`-marking `q + 1` rows above the diagonal, and every crossing on it
lies in a row whose horizontal segment runs to the right; in the last `q + 1` columns the vertical
segment runs up, and every crossing on it lies in a row whose horizontal segment runs to the
left. -/
theorem crossingSign_torusLink (p q : ℕ) {x : Fin (p + 1 + (q + 1)) × Fin (p + 1 + (q + 1))}
    (hx : x ∈ (torusLink p q).crossings) : (torusLink p q).crossingSign x = -1 := by
  obtain ⟨c, r⟩ := x
  rw [mem_crossings, isCrossing_iff] at hx
  rw [crossingSign_eq_neg_one_iff]
  set d := (torusLink p q).X.transpose r
  have hOt : (torusLink p q).O.transpose r = r := by
    simpa using (torusLink p q).O.transpose_apply_apply r
  -- The rows of the `X`-markings of `c` and of `d`, whose `X`-marking lies in row `r`.
  have hX (y : Fin (p + 1 + (q + 1))) :
      ((torusLink p q).X y : ℕ) = y + (q + 1) ∧ (y : ℕ) ≤ p ∨
        ((torusLink p q).X y : ℕ) = y - (p + 1) ∧ p < (y : ℕ) := by
    rcases le_or_gt (y : ℕ) p with hy | hy
    · exact .inl ⟨torusLink_X_val_of_le p q hy, hy⟩
    · exact .inr ⟨torusLink_X_val_of_lt p q hy, hy⟩
  have hXd := hX d
  rw [(torusLink p q).X.apply_transpose_apply] at hXd
  have hXc := hX c
  rw [hOt] at hx ⊢
  simp only [torusLink_O_apply, mem_uIoo_iff_val] at hx ⊢
  simp only [Fin.lt_def]
  have := c.isLt
  have := d.isLt
  omega

/-- The writhe of the Gauss code of a torus knot grid is minus its number of crossings. -/
theorem writhe_gaussCode_torusLink {p q : ℕ} (h : (torusLink p q).IsKnot)
    (c₀ : Fin (p + 1 + (q + 1))) :
    (h.gaussCode c₀).writhe = -((torusLink p q).crossings.card : ℤ) := by
  rw [h.writhe_gaussCode, Finset.sum_congr rfl fun x hx => by
    rw [crossingSign_torusLink p q hx]]
  simp

/-- The crossings of the `5 × 5` trefoil grid: the squares `(1, 3)`, `(2, 1)` and `(3, 2)`. -/
theorem crossings_torusLink_one_two :
    (torusLink 1 2).crossings = {(1, 3), (2, 1), (3, 2)} := by
  ext ⟨c, r⟩
  simp only [mem_crossings, isCrossing_iff, uIoo, GridState.transpose_apply, torusLink_O_toPerm,
    torusLink_X_toPerm]
  -- The marking permutations are explicit, so `decide` evaluates every square.
  revert c r
  decide

/-- The `5 × 5` trefoil grid has three crossings. -/
theorem card_crossings_torusLink_one_two : (torusLink 1 2).crossings.card = 3 := by
  rw [crossings_torusLink_one_two]
  decide

/-- **The writhe of the trefoil grid is `-3`**, from every base column. -/
theorem writhe_gaussCode_torusLink_one_two (c₀ : Fin (1 + 1 + (2 + 1))) :
    (isKnot_torusLink_one_two.gaussCode c₀).writhe = -3 := by
  rw [writhe_gaussCode_torusLink, card_crossings_torusLink_one_two]
  norm_num

end GridDiagram

end TauCeti
