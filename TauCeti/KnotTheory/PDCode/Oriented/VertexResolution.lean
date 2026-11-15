/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Oriented.Component
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Seifert
public import TauCeti.KnotTheory.PDCode.VertexResolution

/-!
# Orienting PD-codes and resolving crossings of oriented PD-codes

Every unoriented `TauCeti.PDCode` admits an orientation: its directed component traversal
`TauCeti.PDCode.componentPerm` is a product of two perfect matchings (`crossingTurn` and
`edgePair`), so arc pairing induces a fixed-point-free involution
`TauCeti.PDCode.componentCycleReversal` on the directed traversal orbits. Choosing one orbit from
each reversal pair (`TauCeti.PDCode.orient`) orients all crossing-bearing components, and supplying
a `Multiset Bool` of length `crossinglessComponentCount` orients the crossing-free circles
(`TauCeti.PDCode.exists_orientedPDCode_of_card_eq`, `TauCeti.PDCode.exists_orientedPDCode`). In
particular, both smoothings of a crossing of an oriented diagram can always be endowed with
orientations, as assumed by the normalized Khovanov skein sequence.

At a crossing `c` of an oriented code `D`, the Seifert smoothing `D.seifertState c` joins incoming
half-edges to outgoing ones, so the resolution `D.toPDCode.resolveCrossing c (D.seifertState c)`
inherits the half-edge orientations of `D` (`TauCeti.OrientedPDCode.coherentResolveCrossing`) once
the newly detached crossing-free circles are oriented. Every remaining crossing `i` keeps the sign
of `c.succAbove i`.

Comparing `TauCeti.OrientedPDCode.crossingComponentOfHalfEdge` with `componentPerm` orbits yields
the oriented component-count dichotomy at `c`:

* if the two local strands at `c` belong to distinct link components, both the `A`- and
  `B`-smoothings merge those two components into one (`c - 1` components each);
* if `c` is a self-crossing of one link component, the Seifert smoothing splits that component
  (`c + 1` components) and the opposite smoothing leaves `c` components.

## Main definitions

* `TauCeti.PDCode.componentCycleReversal`: reversal of directed `componentPerm` orbits.
* `TauCeti.PDCode.orient`: build an `OrientedPDCode` from a reversal-antisymmetric choice on
  `componentPerm` orbits and a `Multiset Bool` of crossing-free circle orientations.
* `TauCeti.OrientedPDCode.coherentResolveCrossing`: the Seifert resolution at `c`, inheriting the
  orientation of `D` on all remaining half-edges.

## Main results

* `TauCeti.PDCode.exists_orientedPDCode_of_card_eq` and `TauCeti.PDCode.exists_orientedPDCode`:
  every `PDCode` admits an orientation.
* `TauCeti.OrientedPDCode.crossingSign_coherentResolveCrossing` and
  `TauCeti.OrientedPDCode.writhe_coherentResolveCrossing`: crossing signs and writhe of the
  oriented smoothing.
* `TauCeti.OrientedPDCode.crossingComponentOfHalfEdge_eq_iff`: two half-edges lie on the same
  crossing-bearing component iff `componentPerm` connects one to the other or to its opposite slot.
* `TauCeti.OrientedPDCode.componentCount_resolveCrossing_add_one_of_crossingComponentOfHalfEdge_ne`,
  `TauCeti.OrientedPDCode.componentCount_resolveCrossing_seifertState`, and
  `TauCeti.OrientedPDCode.componentCount_resolveCrossing_not_seifertState`: component counts of
  smoothings of two-component crossings and self-crossings.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapters 1-3.
* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §3.4.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), §3.1.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm Finset

namespace PDCode

variable {n : ℕ}

/-! ### Orientability of arbitrary PD-codes -/

/-- Identify the `SameCycle` quotient of `D.crossingTurn * D.edgePair.val` with that of
`D.componentPerm`, whose body is not exposed across modules. -/
private def componentOrbitEquiv (D : PDCode n) :
    Quotient (SameCycle.setoid (D.crossingTurn * D.edgePair.val)) ≃
      Quotient (SameCycle.setoid D.componentPerm) :=
  Quotient.congr (Equiv.refl _) fun _ _ ↦ by rw [componentPerm_def]; rfl

private theorem componentOrbitEquiv_mk (D : PDCode n) (x : Fin (4 * n)) :
    D.componentOrbitEquiv ⟦x⟧ = ⟦x⟧ :=
  rfl

private theorem componentOrbitEquiv_symm_mk (D : PDCode n) (x : Fin (4 * n)) :
    D.componentOrbitEquiv.symm ⟦x⟧ = ⟦x⟧ :=
  (Equiv.symm_apply_eq _).mpr rfl

/-- **Reversal of directed component orbits**: following the other end of an arc carries each
directed traversal orbit of `D.componentPerm` to the opposite traversal of the same component. -/
noncomputable def componentCycleReversal (D : PDCode n) :
    Perm (Quotient (SameCycle.setoid D.componentPerm)) :=
  D.componentOrbitEquiv.permCongr
    (D.isPerfectMatching_crossingTurn.involutive.cycleReversal D.edgePair.apply_apply)

/-- Reversal sends the directed orbit of a half-edge to that of the other end of its arc. -/
@[simp] theorem componentCycleReversal_mk (D : PDCode n) (x : Fin (4 * n)) :
    D.componentCycleReversal ⟦x⟧ = ⟦D.edgePair.val x⟧ :=
  -- Term proof: `rw` rejects `D.edgePair.val` before unfolding `PerfectMatching` at implicit
  -- transparency, as in `TauCeti.PDCode.stateCycleReversal_mk`.
  (Equiv.permCongr_apply _ _ _).trans <|
    (congrArg _ ((congrArg _ (D.componentOrbitEquiv_symm_mk x)).trans
      (Function.Involutive.cycleReversal_mk _ _ x))).trans (D.componentOrbitEquiv_mk _)

/-- Reversal also sends the directed orbit of a half-edge to that of its opposite crossing slot. -/
theorem componentCycleReversal_mk_eq_crossingTurn (D : PDCode n) (x : Fin (4 * n)) :
    D.componentCycleReversal ⟦x⟧ = ⟦D.crossingTurn x⟧ := by
  rw [componentCycleReversal_mk]
  apply Quotient.sound
  have h : D.componentPerm (D.edgePair.val x) = D.crossingTurn x :=
    (D.componentPerm_apply (D.edgePair.val x)).trans
      (congrArg D.crossingTurn (D.edgePair.apply_apply x))
  exact ⟨(1 : ℕ), by rw [zpow_natCast, pow_one]; exact h⟩

/-- Reversal of directed component orbits is a fixed-point-free involution. -/
theorem isPerfectMatching_componentCycleReversal (D : PDCode n) :
    IsPerfectMatching D.componentCycleReversal :=
  PerfectMatching.isPerfectMatching_permCongr _
    (D.isPerfectMatching_crossingTurn.isPerfectMatching_cycleReversal D.edgePair.prop)

/-- Endow an unoriented `PDCode` with an orientation from a reversal-antisymmetric `Bool` choice on
its directed `componentPerm` orbits and a `Multiset Bool` of crossing-free circle orientations. -/
def orient (D : PDCode n) (o : Quotient (SameCycle.setoid D.componentPerm) → Bool)
    (ho : ∀ q, o (D.componentCycleReversal q) = !o q) (l : Multiset Bool)
    (hl : l.card = D.crossinglessComponentCount) : OrientedPDCode n where
  toPDCode := D
  orientation x := o ⟦x⟧
  orientation_edgePair x := by
    simpa only [componentCycleReversal_mk] using ho ⟦x⟧
  orientation_oppositeCrossingSlot i slot := by
    rw [← D.crossing_apply, ← D.crossingTurn_crossing, ← componentCycleReversal_mk_eq_crossingTurn]
    exact ho _
  crossinglessComponents := l
  card_crossinglessComponents := hl

/-- Forgetting the orientation constructed by `orient` recovers `D`. -/
@[simp] theorem toPDCode_orient (D : PDCode n)
    (o : Quotient (SameCycle.setoid D.componentPerm) → Bool)
    (ho : ∀ q, o (D.componentCycleReversal q) = !o q) (l : Multiset Bool)
    (hl : l.card = D.crossinglessComponentCount) :
    (D.orient o ho l hl).toPDCode = D := (rfl)

/-- The half-edge orientation of `D.orient` evaluates the chosen orbit function on `⟦x⟧`. -/
@[simp] theorem orient_orientation (D : PDCode n)
    (o : Quotient (SameCycle.setoid D.componentPerm) → Bool)
    (ho : ∀ q, o (D.componentCycleReversal q) = !o q) (l : Multiset Bool)
    (hl : l.card = D.crossinglessComponentCount) (x : Fin (4 * n)) :
    (D.orient o ho l hl).orientation x = o ⟦x⟧ := (rfl)

/-- `D.orient` records the supplied crossing-free circle orientations. -/
@[simp] theorem orient_crossinglessComponents (D : PDCode n)
    (o : Quotient (SameCycle.setoid D.componentPerm) → Bool)
    (ho : ∀ q, o (D.componentCycleReversal q) = !o q) (l : Multiset Bool)
    (hl : l.card = D.crossinglessComponentCount) :
    (D.orient o ho l hl).crossinglessComponents = l := (rfl)

/-- **Every `PDCode` admits an orientation** with any prescribed `Multiset Bool` of orientations on
its crossing-free circles. -/
theorem exists_orientedPDCode_of_card_eq (D : PDCode n) (l : Multiset Bool)
    (hl : l.card = D.crossinglessComponentCount) :
    ∃ E : OrientedPDCode n, E.toPDCode = D ∧ E.crossinglessComponents = l := by
  classical
  let e := Fintype.equivFin (Quotient (SameCycle.setoid D.componentPerm))
  obtain ⟨hinv, hne⟩ := isPerfectMatching_iff.mp D.isPerfectMatching_componentCycleReversal
  have ho : ∀ q, decide (e (D.componentCycleReversal q) <
      e (D.componentCycleReversal (D.componentCycleReversal q))) =
        !decide (e q < e (D.componentCycleReversal q)) := fun q ↦ by
    rw [hinv q]
    have hneq : (e (D.componentCycleReversal q) : ℕ) ≠ e q :=
      Fin.val_ne_of_ne (e.injective.ne (hne q))
    cases hlt : decide (e q < e (D.componentCycleReversal q)) <;>
      simp only [Fin.lt_def, decide_eq_true_iff, decide_eq_false_iff_not,
        Bool.not_false, Bool.not_true] at hlt ⊢ <;> omega
  exact ⟨D.orient (fun q ↦ decide (e q < e (D.componentCycleReversal q))) ho l hl, rfl, rfl⟩

/-- **Every `PDCode` admits an orientation.** -/
theorem exists_orientedPDCode (D : PDCode n) : ∃ E : OrientedPDCode n, E.toPDCode = D := by
  obtain ⟨E, hE, -⟩ := D.exists_orientedPDCode_of_card_eq
    (Multiset.replicate D.crossinglessComponentCount true) (Multiset.card_replicate _ _)
  exact ⟨E, hE⟩

end PDCode

namespace OrientedPDCode

/-! ### Coherent orientation of the Seifert smoothing at one crossing -/

section CoherentResolveCrossing

variable {n : ℕ} (D : OrientedPDCode (n + 1)) (c : Fin (n + 1)) (l : Multiset Bool)
  (hl : l.card = D.toPDCode.detachedCircleCount c (D.seifertState c))

/-- **The coherently oriented smoothing at a crossing `c`**: resolving `c` by `D.seifertState c`
joins incoming half-edges to outgoing ones, so every remaining half-edge keeps its orientation in
`D`, while `l` supplies orientations for any newly detached crossing-free circles. -/
def coherentResolveCrossing : OrientedPDCode n where
  toPDCode := D.toPDCode.resolveCrossing c (D.seifertState c)
  orientation y := D.orientation (D.toPDCode.resolveCrossingHalfEdge c y)
  orientation_edgePair y := by
    have hchoice : (bif D.seifertState c then D.overPair c else !D.overPair c) =
        D.smoothingChoice D.seifertState c := by
      cases hs : D.seifertState c <;> simp [hs]
    refine D.toPDCode.bool_not_resolveCrossing_edgePair_val c (D.seifertState c)
      D.orientation_edgePair (fun k ↦ ?_) y
    have h := D.orientation_smoothingTurn_seifertState (D.crossing c k)
    rwa [PDCode.crossing_apply, PDCode.smoothingTurn_crossing, ← PDCode.crossing_apply,
      ← hchoice] at h
  orientation_oppositeCrossingSlot i slot := by
    simp [PDCode.resolveCrossingHalfEdge_crossingSlotEquiv, D.orientation_oppositeCrossingSlot]
  crossinglessComponents := D.crossinglessComponents + l
  card_crossinglessComponents := by
    simp [hl]

/-- The underlying code of `coherentResolveCrossing` is the Seifert resolution at `c`. -/
@[simp] theorem toPDCode_coherentResolveCrossing :
    (D.coherentResolveCrossing c l hl).toPDCode =
      D.toPDCode.resolveCrossing c (D.seifertState c) := (rfl)

/-- Each half-edge of `coherentResolveCrossing` inherits its orientation from `D`. -/
@[simp] theorem coherentResolveCrossing_orientation (y : Fin (4 * n)) :
    (D.coherentResolveCrossing c l hl).orientation y =
      D.orientation (D.toPDCode.resolveCrossingHalfEdge c y) := (rfl)

/-- `coherentResolveCrossing` appends the detached-circle orientations `l` to those of `D`. -/
@[simp] theorem coherentResolveCrossing_crossinglessComponents :
    (D.coherentResolveCrossing c l hl).crossinglessComponents = D.crossinglessComponents + l :=
  (rfl)

/-- Every remaining crossing `i` of `coherentResolveCrossing` keeps the sign of `c.succAbove i`. -/
@[simp] theorem crossingSign_coherentResolveCrossing (i : Fin n) :
    (D.coherentResolveCrossing c l hl).crossingSign i = D.crossingSign (c.succAbove i) := by
  simp [crossingSign_def]

/-- Resolving `c` coherently removes `D.crossingSign c` from the writhe. -/
theorem writhe_coherentResolveCrossing :
    (D.coherentResolveCrossing c l hl).writhe + D.crossingSign c = D.writhe := by
  rw [writhe_def, D.writhe_def, Fin.sum_univ_succAbove _ c]
  simp [add_comm]

/-- Positive crossing count of `D` in terms of `coherentResolveCrossing` and `D.crossingSign c`. -/
theorem positiveCrossingCount_coherentResolveCrossing :
    D.positiveCrossingCount =
      (D.coherentResolveCrossing c l hl).positiveCrossingCount +
        if D.crossingSign c = 1 then 1 else 0 := by
  rw [positiveCrossingCount_def, positiveCrossingCount_def, Finset.card_filter, Finset.card_filter,
    Fin.sum_univ_succAbove _ c]
  simp_rw [crossingSign_coherentResolveCrossing]
  exact add_comm _ _

/-- Negative crossing count of `D` in terms of `coherentResolveCrossing` and `D.crossingSign c`. -/
theorem negativeCrossingCount_coherentResolveCrossing :
    D.negativeCrossingCount =
      (D.coherentResolveCrossing c l hl).negativeCrossingCount +
        if D.crossingSign c = -1 then 1 else 0 := by
  rw [negativeCrossingCount_def, negativeCrossingCount_def, Finset.card_filter, Finset.card_filter,
    Fin.sum_univ_succAbove _ c]
  simp_rw [crossingSign_coherentResolveCrossing]
  exact add_comm _ _

end CoherentResolveCrossing

/-! ### Oriented link components and component counts of smoothings -/

section ComponentCount

/-- Two half-edges in the same directed `componentPerm` orbit have the same orientation. -/
theorem orientation_eq_of_sameCycle_componentPerm {n : ℕ} (D : OrientedPDCode n)
    {x y : Fin (4 * n)} (h : D.toPDCode.componentPerm.SameCycle x y) :
    D.orientation x = D.orientation y := by
  obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Perm.mul_apply, D.orientation_componentPerm, ih]

private theorem crossingComponentOfHalfEdge_eq_iff_of_outgoing {n : ℕ} (D : OrientedPDCode n)
    {x y : Fin (4 * n)} (hx : D.orientation x = true) (hy : D.orientation y = true) :
    D.crossingComponentOfHalfEdge x = D.crossingComponentOfHalfEdge y ↔
      D.toPDCode.componentPerm.SameCycle x y ∨
        D.toPDCode.componentPerm.SameCycle x (D.crossingTurn y) := by
  have hnot : ¬ D.toPDCode.componentPerm.SameCycle x (D.crossingTurn y) := fun h ↦ by
    have ho := D.orientation_eq_of_sameCycle_componentPerm h
    simp [hx, hy] at ho
  have hsub : D.componentPermOutgoing =
      D.toPDCode.componentPerm.subtypePerm (fun h ↦ by simp only [orientation_componentPerm]) := by
    ext h
    simp
  rw [← Sum.inl_injective.eq_iff, D.inl_crossingComponentOfHalfEdge ⟨x, hx⟩,
    D.inl_crossingComponentOfHalfEdge ⟨y, hy⟩, D.componentOfOutgoing_eq_iff, hsub,
    or_iff_left hnot]
  exact sameCycle_subtypePerm

private theorem crossingComponentOfHalfEdge_eq_iff_of_left_outgoing {n : ℕ} (D : OrientedPDCode n)
    {x : Fin (4 * n)} (hx : D.orientation x = true) (y : Fin (4 * n)) :
    D.crossingComponentOfHalfEdge x = D.crossingComponentOfHalfEdge y ↔
      D.toPDCode.componentPerm.SameCycle x y ∨
        D.toPDCode.componentPerm.SameCycle x (D.crossingTurn y) := by
  cases hy : D.orientation y
  · have hy' : D.orientation (D.crossingTurn y) = true := by simp [hy]
    rw [← D.crossingComponentOfHalfEdge_crossingTurn y,
      D.crossingComponentOfHalfEdge_eq_iff_of_outgoing hx hy', D.crossingTurn_apply_apply, or_comm]
  · exact D.crossingComponentOfHalfEdge_eq_iff_of_outgoing hx hy

/-- Two half-edges belong to the same crossing-bearing component iff `componentPerm` connects `x`
either to `y` (same direction) or to `D.crossingTurn y` (opposite direction). -/
theorem crossingComponentOfHalfEdge_eq_iff {n : ℕ} (D : OrientedPDCode n) (x y : Fin (4 * n)) :
    D.crossingComponentOfHalfEdge x = D.crossingComponentOfHalfEdge y ↔
      D.toPDCode.componentPerm.SameCycle x y ∨
        D.toPDCode.componentPerm.SameCycle x (D.crossingTurn y) := by
  cases hx : D.orientation x
  · have hx' : D.orientation (D.crossingTurn x) = true := by simp [hx]
    rw [← D.crossingComponentOfHalfEdge_crossingTurn x,
      D.crossingComponentOfHalfEdge_eq_iff_of_left_outgoing hx' y,
      ← D.toPDCode.sameCycle_componentPerm_crossingTurn_iff (x := D.crossingTurn x) (y := y),
      D.crossingTurn_apply_apply, D.toPDCode.sameCycle_componentPerm_crossingTurn_iff, or_comm]
  · exact D.crossingComponentOfHalfEdge_eq_iff_of_left_outgoing hx y

variable {n : ℕ} (D : OrientedPDCode (n + 1)) (c : Fin (n + 1))

/-- **Two-component crossing.** If slots `0` and `1` of crossing `c` lie on distinct link
components, then both the `A`- and `B`-smoothings merge those two components and have
`D.componentCount - 1` components. -/
theorem componentCount_resolveCrossing_add_one_of_crossingComponentOfHalfEdge_ne
    (h : D.crossingComponentOfHalfEdge (D.crossing c 0) ≠
      D.crossingComponentOfHalfEdge (D.crossing c 1)) (t : Bool) :
    (D.toPDCode.resolveCrossing c t).componentCount + 1 = D.componentCount := by
  rw [Ne, D.crossingComponentOfHalfEdge_eq_iff, not_or] at h
  have ht₁ : D.crossingTurn (D.crossing c 1) = D.crossing c 3 := by
    rw [PDCode.crossing_apply, PDCode.crossingTurn_crossing, PDCode.oppositeCrossingSlot_apply]
    rfl
  exact D.toPDCode.componentCount_resolveCrossing_add_one_of_not_sameCycle c t h.1 (ht₁ ▸ h.2)

/-- If slots `0` and `1` of crossing `c` lie on the same link component, then the Seifert smoothing
`D.seifertState c` splits that component (`D.componentCount + 1` components) and the opposite
smoothing `!D.seifertState c` leaves `D.componentCount` components. -/
private theorem componentCount_resolveCrossing_seifertState_and_not
    (h : D.crossingComponentOfHalfEdge (D.crossing c 0) =
      D.crossingComponentOfHalfEdge (D.crossing c 1)) :
    (D.toPDCode.resolveCrossing c (D.seifertState c)).componentCount = D.componentCount + 1 ∧
      (D.toPDCode.resolveCrossing c (!D.seifertState c)).componentCount = D.componentCount := by
  have ht₁ : D.crossingTurn (D.crossing c 1) = D.crossing c 3 := by
    rw [PDCode.crossing_apply, PDCode.crossingTurn_crossing, PDCode.oppositeCrossingSlot_apply]
    rfl
  have hsc := D.smoothingChoice_seifertState c
  have hchoice : D.smoothingChoice D.seifertState c =
      (bif D.seifertState c then D.overPair c else !D.overPair c) := by
    cases hs : D.seifertState c <;> simp [hs]
  rw [D.crossingComponentOfHalfEdge_eq_iff, ht₁] at h
  rcases h with h₁ | h₃
  · have ho := D.orientation_eq_of_sameCycle_componentPerm h₁
    have hseif : D.seifertState c = !D.overPair c := by
      rw [ho, Bool.xor_self, hchoice] at hsc
      cases hs : D.seifertState c <;> cases ho' : D.overPair c <;> simp [hs, ho'] at hsc ⊢
    rw [hseif, Bool.not_not]
    exact D.toPDCode.componentCount_resolveCrossing_of_sameCycle_zero_one c h₁
  · have ho := D.orientation_eq_of_sameCycle_componentPerm h₃
    have h31 : D.orientation (D.crossing c 3) = !D.orientation (D.crossing c 1) := by
      rw [← ht₁, D.orientation_crossingTurn]
    have hseif : D.seifertState c = D.overPair c := by
      rw [ho, h31] at hsc
      have hxor : Bool.xor (!D.orientation (D.crossing c 1)) (D.orientation (D.crossing c 1)) =
          true := by
        cases D.orientation (D.crossing c 1) <;> rfl
      rw [hxor, hchoice] at hsc
      cases hs : D.seifertState c <;> cases ho' : D.overPair c <;> simp [hs, ho'] at hsc ⊢
    rw [hseif]
    exact D.toPDCode.componentCount_resolveCrossing_of_sameCycle_zero_three c h₃

/-- **Self-crossing (Seifert smoothing).** If slots `0` and `1` of crossing `c` lie on the same
link component, then the Seifert smoothing `D.seifertState c` splits that component and has
`D.componentCount + 1` components. -/
theorem componentCount_resolveCrossing_seifertState
    (h : D.crossingComponentOfHalfEdge (D.crossing c 0) =
      D.crossingComponentOfHalfEdge (D.crossing c 1)) :
    (D.toPDCode.resolveCrossing c (D.seifertState c)).componentCount = D.componentCount + 1 :=
  (D.componentCount_resolveCrossing_seifertState_and_not c h).1

/-- **Self-crossing (non-Seifert smoothing).** If slots `0` and `1` of crossing `c` lie on the same
link component, then the opposite smoothing `!D.seifertState c` has `D.componentCount`
components. -/
theorem componentCount_resolveCrossing_not_seifertState
    (h : D.crossingComponentOfHalfEdge (D.crossing c 0) =
      D.crossingComponentOfHalfEdge (D.crossing c 1)) :
    (D.toPDCode.resolveCrossing c (!D.seifertState c)).componentCount = D.componentCount :=
  (D.componentCount_resolveCrossing_seifertState_and_not c h).2

end ComponentCount

end OrientedPDCode

end TauCeti
