/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Basic
import TauCeti.Logic.Relation

/-!
# The circles of two smoothings differing at one crossing

An edge of the cube of resolutions of a PD-code joins two states `s` and `t` that agree at every
crossing except one crossing `c`. This file compares the circles of the two smoothed diagrams.

Smoothing only reconnects the four half-edges `D.crossing c k` at the crossing `c`, so a circle
avoiding these four half-edges is a circle of both smoothings: it consists of the same half-edges
in both (`TauCeti.PDCode.eqvGen_circleStep_iff_of_notMem_circlesAt`). This gives the bijection
`TauCeti.PDCode.unchangedCircleEquiv` between the circles of `s` and of `t` that do not pass
through `c`. The circles passing through `c`, `TauCeti.PDCode.circlesAt D s c`, are the circles of
the two half-edges in the opposite slots `0` and `2`, since each local smoothing joins every slot to
one of its two neighbours. So one or two circles of each smoothing pass through `c`.

They are never two for both smoothings when `s c ≠ t c`
(`TauCeti.PDCode.card_circlesAt_add_card_circlesAt_le_three`). Delete the smoothing arcs at `c`
from either smoothed diagram: the half-edge `x = D.crossing c 0` lies on a component of what
remains, the same for `s` and for `t`. If two circles of each smoothing passed through `c`, that
component would meet the four half-edges at `c` in `x` alone. It is closed under the arc matching,
so it has an even number of half-edges, and away from `c` it is closed under the remaining
smoothing arcs, so it has an even number of half-edges other than `x`; this is impossible.

So the circles passing through `c` change in one of three ways: two circles of `s` merge into one
circle of `t`, one circle of `s` splits into two circles of `t`, or one circle is replaced by one
circle. Nothing here uses planarity. For planar codes the last case does not occur, but it does
for the nonplanar code of two circles meeting in a single crossing. Whenever only one circle of `t`
passes through `c`, sending the circle of a half-edge to its circle in `t` is a well-defined map
`TauCeti.PDCode.saddleCircleMap`: it is the unchanged-circle bijection away from `c` and collapses
the circles of `s` through `c` onto the circle of `t` through `c`. It is the correspondence of
circles along which the saddle cobordism of a merge acts, and in reverse that of a split.

## Main definitions

* `TauCeti.PDCode.circlesAt`: the circles of a smoothed diagram passing through a crossing.
* `TauCeti.PDCode.unchangedCircleEquiv`: the circles avoiding the crossing `c` are the same for two
  states agreeing away from `c`.
* `TauCeti.PDCode.saddleCircleMap`: the correspondence of circles when one circle of the target
  passes through `c`.

## Main results

* `TauCeti.PDCode.circlesAt_eq_pair`: the circles through `c` are those of the half-edges in slots
  `0` and `2`; in particular there are one or two of them (`TauCeti.PDCode.card_circlesAt_le_two`).
* `TauCeti.PDCode.card_circlesAt_add_card_circlesAt_le_three`: two states differing exactly at `c`
  do not both have two circles through `c`; if one has two, the other has one
  (`TauCeti.PDCode.card_circlesAt_eq_one_of_card_circlesAt_eq_two`).
* `TauCeti.PDCode.stateLoopCount_add_card_circlesAt`: the change in the number of circles is the
  change in the number of circles through `c`; in particular it is at most one
  (`TauCeti.PDCode.stateLoopCount_le_stateLoopCount_add_one`).

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), 359-426,
  §2 and §4.2 (the circles of neighbouring resolutions and the merge and split maps).
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), 337-370, §2.
-/

public section

namespace TauCeti

open Finset Relation

namespace PDCode

variable {n : ℕ}

/-! ### The circles through a crossing -/

section CirclesAt

variable (D : PDCode n) (s : Fin n → Bool) (c : Fin n)

/-- The circles of the diagram smoothed according to the state `s` that pass through the
crossing `c`: the circles of the four half-edges at `c`. -/
def circlesAt : Finset (D.CrossingCircle s) :=
  univ.image fun k ↦ ⟦D.crossing c k⟧

variable {D s c} in
/-- A circle passes through the crossing `c` when it is the circle of a half-edge at `c`. -/
theorem mem_circlesAt {C : D.CrossingCircle s} :
    C ∈ D.circlesAt s c ↔ ∃ k, ⟦D.crossing c k⟧ = C := by
  simp [circlesAt]

-- Not `@[simp]`: `TauCeti.PDCode.crossing_apply` rewrites the left-hand side.
/-- The circle of a half-edge at the crossing `c` passes through `c`. -/
theorem mk_crossing_mem_circlesAt (k : Fin 4) :
    (⟦D.crossing c k⟧ : D.CrossingCircle s) ∈ D.circlesAt s c :=
  mem_circlesAt.2 ⟨k, rfl⟩

/-- The circles through the crossing `c` are the circles of the half-edges in the opposite
slots `0` and `2`: each local smoothing joins the other two slots to one of these. -/
theorem circlesAt_eq_pair :
    D.circlesAt s c = {⟦D.crossing c 0⟧, ⟦D.crossing c 2⟧} := by
  have key : ∀ (b : Bool) (k : Fin 4),
      k = 0 ∨ k = 2 ∨ slotSmoothing b k = 0 ∨ slotSmoothing b k = 2 := by
    intro b
    cases b <;> simp only [slotSmoothing_true, slotSmoothing_false] <;> decide
  ext C
  rw [mem_circlesAt, mem_insert, mem_singleton]
  constructor
  · rintro ⟨k, rfl⟩
    rcases key (D.smoothingChoice s c) k with h | h | h | h
    · exact .inl (by rw [h])
    · exact .inr (by rw [h])
    · exact .inl (by rw [← CrossingCircle.mk_crossing_slotSmoothing, h])
    · exact .inr (by rw [← CrossingCircle.mk_crossing_slotSmoothing, h])
  · rintro (rfl | rfl) <;> exact ⟨_, rfl⟩

/-- Some circle passes through the crossing `c`. -/
theorem circlesAt_nonempty : (D.circlesAt s c).Nonempty :=
  ⟨_, D.mk_crossing_mem_circlesAt s c 0⟩

/-- At most two circles pass through a crossing. -/
theorem card_circlesAt_le_two : #(D.circlesAt s c) ≤ 2 := by
  rw [circlesAt_eq_pair]
  exact card_le_two

/-- Two circles pass through the crossing `c` exactly when the half-edges in the opposite slots
`0` and `2` lie on different circles. -/
theorem card_circlesAt_eq_two_iff :
    #(D.circlesAt s c) = 2 ↔
      (⟦D.crossing c 0⟧ : D.CrossingCircle s) ≠ ⟦D.crossing c 2⟧ := by
  rw [circlesAt_eq_pair, card_pair_eq_two_iff]

end CirclesAt

/-! ### The circles avoiding the crossing -/

section Unchanged

variable (D : PDCode n) {s t : Fin n → Bool} {c : Fin n} (hst : ∀ j, j ≠ c → s j = t j)
include hst

/-- **A circle avoiding the crossing `c` is a circle of every state agreeing away from `c`.** If
the circle of `x` in the smoothing `s` does not pass through `c`, then the half-edges on the circle
of `x` are the same for the smoothings `s` and `t`. -/
theorem eqvGen_circleStep_iff_of_notMem_circlesAt {x : Fin (4 * n)}
    (hx : (⟦x⟧ : D.CrossingCircle s) ∉ D.circlesAt s c) {y : Fin (4 * n)} :
    EqvGen (D.CircleStep s) x y ↔ EqvGen (D.CircleStep t) x y := by
  refine eqvGen_iff_of_forall_symmGen_iff fun y hy z ↦ ?_
  have hy' : ∀ k, D.crossing c k ≠ y := by
    rintro k rfl
    exact hx (mem_circlesAt.2 ⟨k, Quotient.sound (EqvGen.symm _ _ hy)⟩)
  simp only [SymmGen, circleStep_comm D _ (x := z), or_self, circleStep_iff,
    D.smoothingTurn_apply_eq_smoothingTurn_apply
      (fun j hj ↦ D.smoothingChoice_eq_smoothingChoice (hst j hj)) hy']

/-- A circle of `s` avoiding the crossing `c` is a circle of `t` avoiding `c`. -/
theorem mk_notMem_circlesAt_of_notMem {x : Fin (4 * n)}
    (hx : (⟦x⟧ : D.CrossingCircle s) ∉ D.circlesAt s c) :
    (⟦x⟧ : D.CrossingCircle t) ∉ D.circlesAt t c := by
  rintro hmem
  obtain ⟨k, hk⟩ := mem_circlesAt.1 hmem
  refine hx (mem_circlesAt.2 ⟨k, (Quotient.sound ?_).symm⟩)
  exact (D.eqvGen_circleStep_iff_of_notMem_circlesAt hst hx).2 (Quotient.exact hk.symm)

/-- The circle of `t` with the same half-edges as a circle of `s` avoiding the crossing `c`. -/
private noncomputable def unchangedCircleMap
    (C : {C : D.CrossingCircle s // C ∉ D.circlesAt s c}) :
    {C : D.CrossingCircle t // C ∉ D.circlesAt t c} :=
  ⟨⟦C.1.out⟧, D.mk_notMem_circlesAt_of_notMem hst (by rw [Quotient.out_eq]; exact C.2)⟩

private theorem unchangedCircleMap_mk {x : Fin (4 * n)}
    (hx : (⟦x⟧ : D.CrossingCircle s) ∉ D.circlesAt s c) :
    D.unchangedCircleMap hst ⟨⟦x⟧, hx⟩ = ⟨⟦x⟧, D.mk_notMem_circlesAt_of_notMem hst hx⟩ := by
  refine Subtype.ext (Quotient.sound ?_)
  have hout : (⟦(⟦x⟧ : D.CrossingCircle s).out⟧ : D.CrossingCircle s) ∉ D.circlesAt s c := by
    rwa [Quotient.out_eq]
  exact (D.eqvGen_circleStep_iff_of_notMem_circlesAt hst hout).1
    (Quotient.exact (Quotient.out_eq (⟦x⟧ : D.CrossingCircle s)))

/-- **The unchanged circles.** For two states agreeing away from the crossing `c`, the circles
avoiding `c` are the same: the circle of a half-edge in one smoothing corresponds to its circle in
the other (`TauCeti.PDCode.coe_unchangedCircleEquiv_mk`). -/
noncomputable def unchangedCircleEquiv :
    {C : D.CrossingCircle s // C ∉ D.circlesAt s c} ≃
      {C : D.CrossingCircle t // C ∉ D.circlesAt t c} where
  toFun := D.unchangedCircleMap hst
  invFun := D.unchangedCircleMap fun j hj ↦ (hst j hj).symm
  left_inv := by
    rintro ⟨C, hC⟩
    obtain ⟨x, rfl⟩ := Quotient.exists_rep C
    rw [unchangedCircleMap_mk, unchangedCircleMap_mk]
  right_inv := by
    rintro ⟨C, hC⟩
    obtain ⟨x, rfl⟩ := Quotient.exists_rep C
    rw [unchangedCircleMap_mk, unchangedCircleMap_mk]

/-- The unchanged-circle bijection sends the circle of a half-edge to its circle in the other
smoothing. -/
@[simp]
theorem coe_unchangedCircleEquiv_mk {x : Fin (4 * n)}
    (hx : (⟦x⟧ : D.CrossingCircle s) ∉ D.circlesAt s c) :
    (D.unchangedCircleEquiv hst ⟨⟦x⟧, hx⟩ : D.CrossingCircle t) = ⟦x⟧ :=
  congrArg Subtype.val (D.unchangedCircleMap_mk hst hx)

/-- The inverse of the unchanged-circle bijection sends the circle of a half-edge to its circle in
the first smoothing. -/
@[simp]
theorem coe_unchangedCircleEquiv_symm_mk {x : Fin (4 * n)}
    (hx : (⟦x⟧ : D.CrossingCircle t) ∉ D.circlesAt t c) :
    ((D.unchangedCircleEquiv hst).symm ⟨⟦x⟧, hx⟩ : D.CrossingCircle s) = ⟦x⟧ :=
  congrArg Subtype.val (D.unchangedCircleMap_mk (fun j hj ↦ (hst j hj).symm) hx)

/-- The inverse of the unchanged-circle bijection is the unchanged-circle bijection in the other
direction. -/
theorem unchangedCircleEquiv_symm :
    (D.unchangedCircleEquiv hst).symm = D.unchangedCircleEquiv fun j hj ↦ (hst j hj).symm := by
  ext ⟨C, hC⟩
  obtain ⟨x, rfl⟩ := Quotient.exists_rep C
  simp

/-- **The number of circles changes as the number of circles through the crossing does.** -/
theorem stateLoopCount_add_card_circlesAt :
    D.stateLoopCount s + #(D.circlesAt t c) = D.stateLoopCount t + #(D.circlesAt s c) := by
  have hcard (u : Fin n → Bool) : Fintype.card (D.CrossingCircle u) =
      Fintype.card {C : D.CrossingCircle u // C ∉ D.circlesAt u c} + #(D.circlesAt u c) := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
    have := card_le_univ (D.circlesAt u c)
    omega
  rw [← card_resolvedCircle, ← card_resolvedCircle, Fintype.card_sum, Fintype.card_sum,
    hcard s, hcard t, Fintype.card_congr (D.unchangedCircleEquiv hst)]
  omega

/-- **The number of circles changes by at most one** along an edge of the cube of resolutions. -/
theorem stateLoopCount_le_stateLoopCount_add_one :
    D.stateLoopCount t ≤ D.stateLoopCount s + 1 := by
  have h := D.stateLoopCount_add_card_circlesAt hst
  have hs := (D.circlesAt_nonempty s c).card_pos
  have ht := D.card_circlesAt_le_two t c
  omega

end Unchanged

/-! ### The circles through the crossing -/

section Changed

variable (D : PDCode n) {s t : Fin n → Bool} {c : Fin n}

/-- If two circles of `s` and two circles of `t` pass through the crossing `c`, where `s` and `t`
select different smoothings at `c`, then the only half-edge at `c` on the circles of
`D.crossing c 0` in both smoothings is `D.crossing c 0` itself. -/
private theorem eq_zero_of_mk_crossing_eq_mk_crossing
    (hs : (⟦D.crossing c 0⟧ : D.CrossingCircle s) ≠ ⟦D.crossing c 2⟧)
    (ht : (⟦D.crossing c 0⟧ : D.CrossingCircle t) ≠ ⟦D.crossing c 2⟧)
    (hb : D.smoothingChoice t c = !D.smoothingChoice s c) {k : Fin 4}
    (hks : (⟦D.crossing c k⟧ : D.CrossingCircle s) = ⟦D.crossing c 0⟧)
    (hkt : (⟦D.crossing c k⟧ : D.CrossingCircle t) = ⟦D.crossing c 0⟧) : k = 0 := by
  -- Slot `2` lies on the other circle, and the two smoothings join slots `1` and `3` to slot `2`
  -- between them.
  have key : ∀ (b : Bool) (k : Fin 4),
      k = 0 ∨ k = 2 ∨ slotSmoothing b k = 2 ∨ slotSmoothing (!b) k = 2 := by
    intro b
    cases b <;> simp only [Bool.not_true, Bool.not_false, slotSmoothing_true,
      slotSmoothing_false] <;> decide
  have es := CrossingCircle.mk_crossing_slotSmoothing (D := D) (s := s) c k
  have et := CrossingCircle.mk_crossing_slotSmoothing (D := D) (s := t) c k
  rw [hb] at et
  rcases key (D.smoothingChoice s c) k with h | h | h | h
  · exact h
  · exact absurd (h ▸ hks).symm hs
  · rw [h] at es
    exact absurd (es.trans hks).symm hs
  · rw [h] at et
    exact absurd (et.trans hkt).symm ht

/-- **Two states differing exactly at a crossing do not both have two circles through it.** So
along an edge of the cube of resolutions two circles merge into one, one circle splits into two,
or one circle through the crossing is replaced by one circle. -/
theorem card_circlesAt_add_card_circlesAt_le_three (hst : ∀ j, j ≠ c → s j = t j)
    (hc : s c ≠ t c) : #(D.circlesAt s c) + #(D.circlesAt t c) ≤ 3 := by
  classical
  by_contra hlt
  have hs := (D.card_circlesAt_eq_two_iff s c).1
    (by have := D.card_circlesAt_le_two s c; have := D.card_circlesAt_le_two t c; omega)
  have ht := (D.card_circlesAt_eq_two_iff t c).1
    (by have := D.card_circlesAt_le_two s c; have := D.card_circlesAt_le_two t c; omega)
  -- The half-edges joined to `x` by arcs and by smoothing arcs away from `c`, which lie on the
  -- circle of `x` in both smoothings.
  set x := D.crossing c 0
  set σ := D.smoothingTurn (D.smoothingChoice s)
  let r : Fin (4 * n) → Fin (4 * n) → Prop := fun y z ↦
    z = D.edgePair.val y ∨ ((∀ k, D.crossing c k ≠ y) ∧ z = σ y)
  have hrs : EqvGen r ≤ EqvGen (D.CircleStep s) :=
    EqvGen.mono fun y z h ↦ h.imp_right And.right
  have hrt : EqvGen r ≤ EqvGen (D.CircleStep t) := EqvGen.mono fun y z h ↦ h.imp_right
    fun h ↦ h.2.trans (D.smoothingTurn_apply_eq_smoothingTurn_apply
      (fun j hj ↦ D.smoothingChoice_eq_smoothingChoice (hst j hj)) h.1)
  let E := univ.filter (EqvGen r x)
  have hxE : x ∈ E := mem_filter.2 ⟨mem_univ _, .refl _⟩
  -- The only half-edge at `c` in `E` is `x`.
  have hEc : E.filter (fun y ↦ ¬∀ k, D.crossing c k ≠ y) = {x} := by
    refine eq_singleton_iff_unique_mem.2 ⟨mem_filter.2 ⟨hxE, fun h ↦ h 0 rfl⟩, ?_⟩
    simp only [mem_filter, not_forall, not_not]
    rintro y ⟨hy, k, rfl⟩
    have hy := (mem_filter.1 hy).2
    rw [D.eq_zero_of_mk_crossing_eq_mk_crossing hs ht (D.smoothingChoice_eq_not_smoothingChoice hc)
      (Quotient.sound (hrs _ _ hy)).symm (Quotient.sound (hrt _ _ hy)).symm]
  -- `E` is closed under the arc matching, and `E` away from `c` under the smoothing arcs.
  have hE := D.edgePair.prop.even_card_of_mapsTo (S := E) fun y hy ↦
    mem_filter.2 ⟨mem_univ _, (mem_filter.1 hy).2.trans _ _ _ (.rel _ _ (.inl rfl))⟩
  have hE' := (D.isPerfectMatching_smoothingTurn (D.smoothingChoice s)).even_card_of_mapsTo
    (S := E.filter fun y ↦ ∀ k, D.crossing c k ≠ y) fun y hy ↦ by
      obtain ⟨hyE, hyc⟩ := mem_filter.1 hy
      exact mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _,
        (mem_filter.1 hyE).2.trans _ _ _ (.rel _ _ (.inr ⟨hyc, rfl⟩))⟩,
        D.crossing_ne_smoothingTurn _ hyc⟩
  have hsum := card_filter_add_card_filter_not (s := E) (fun y ↦ ∀ k, D.crossing c k ≠ y)
  rw [hEc, card_singleton] at hsum
  rw [← hsum] at hE
  exact Nat.not_even_iff_odd.2 (hE'.add_one) hE

/-- If two circles of `s` pass through the crossing `c` at which `s` and `t` differ, then only one
circle of `t` does: the two circles of `s` merge. -/
theorem card_circlesAt_eq_one_of_card_circlesAt_eq_two (hst : ∀ j, j ≠ c → s j = t j)
    (hc : s c ≠ t c) (hs : #(D.circlesAt s c) = 2) : #(D.circlesAt t c) = 1 := by
  have h := D.card_circlesAt_add_card_circlesAt_le_three hst hc
  have ht := (D.circlesAt_nonempty t c).card_pos
  omega

end Changed

/-! ### The saddle correspondence -/

section Saddle

variable (D : PDCode n) {s t : Fin n → Bool} {c : Fin n} (hst : ∀ j, j ≠ c → s j = t j)
  (ht : #(D.circlesAt t c) = 1)
include hst ht

/-- If only one circle of `t` passes through the crossing `c`, then half-edges on one circle of
`s` lie on one circle of `t`. -/
theorem eqvGen_circleStep_of_card_circlesAt_eq_one {x y : Fin (4 * n)}
    (h : EqvGen (D.CircleStep s) x y) : EqvGen (D.CircleStep t) x y := by
  obtain ⟨C, hC⟩ := card_eq_one.1 ht
  induction h with
  | rel y z hyz =>
    rcases hyz with rfl | rfl
    · exact .rel _ _ (.inl rfl)
    by_cases hy : ∀ k, D.crossing c k ≠ y
    · exact .rel _ _ (.inr (D.smoothingTurn_apply_eq_smoothingTurn_apply
        (fun j hj ↦ D.smoothingChoice_eq_smoothingChoice (hst j hj)) hy))
    -- The two ends of a smoothing arc at `c` lie on the only circle of `t` through `c`.
    obtain ⟨k, rfl⟩ := not_forall_not.1 hy
    have h₁ := D.mk_crossing_mem_circlesAt t c k
    have h₂ := D.mk_crossing_mem_circlesAt t c (slotSmoothing (D.smoothingChoice s c) k)
    rw [hC, mem_singleton] at h₁ h₂
    have hσ : D.smoothingTurn (D.smoothingChoice s) (D.crossing c k) =
        D.crossing c (slotSmoothing (D.smoothingChoice s c) k) := by
      simp
    rw [hσ]
    exact Quotient.exact (h₁.trans h₂.symm)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

/-- **The saddle correspondence of circles.** When only one circle of `t` passes through the
crossing `c`, the circle of a half-edge in the smoothing `s` determines its circle in the
smoothing `t` (`TauCeti.PDCode.saddleCircleMap_mk`). This map is the unchanged-circle bijection
away from `c` (`TauCeti.PDCode.saddleCircleMap_of_notMem`) and sends the circles of `s` through `c`
onto the circle of `t` through `c` (`TauCeti.PDCode.image_saddleCircleMap_circlesAt`). -/
def saddleCircleMap : D.CrossingCircle s → D.CrossingCircle t :=
  Quotient.map' id fun _ _ ↦ D.eqvGen_circleStep_of_card_circlesAt_eq_one hst ht

/-- The saddle correspondence sends the circle of a half-edge to its circle in the target. -/
@[simp]
theorem saddleCircleMap_mk (x : Fin (4 * n)) : D.saddleCircleMap hst ht ⟦x⟧ = ⟦x⟧ :=
  (rfl)

/-- Every circle of the target comes from a circle of the source. -/
theorem saddleCircleMap_surjective : Function.Surjective (D.saddleCircleMap hst ht) :=
  Quotient.ind fun x ↦ ⟨⟦x⟧, D.saddleCircleMap_mk hst ht x⟩

/-- Away from the crossing, the saddle correspondence is the unchanged-circle bijection. -/
theorem saddleCircleMap_of_notMem {C : D.CrossingCircle s} (hC : C ∉ D.circlesAt s c) :
    D.saddleCircleMap hst ht C = D.unchangedCircleEquiv hst ⟨C, hC⟩ := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep C
  simp

/-- The saddle correspondence sends the circles of the source through the crossing onto the
circle of the target through the crossing. -/
theorem image_saddleCircleMap_circlesAt :
    (D.circlesAt s c).image (D.saddleCircleMap hst ht) = D.circlesAt t c := by
  simp only [circlesAt, image_image, Function.comp_def, saddleCircleMap_mk]

/-- When only one circle of each state passes through the crossing, the saddle correspondences in
the two directions are mutually inverse. -/
theorem saddleCircleMap_saddleCircleMap (hs : #(D.circlesAt s c) = 1) (C : D.CrossingCircle s) :
    D.saddleCircleMap (fun j hj ↦ (hst j hj).symm) hs (D.saddleCircleMap hst ht C) = C := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep C
  simp

end Saddle

end PDCode

end TauCeti
