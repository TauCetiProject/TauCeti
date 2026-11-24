/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.ClosingArcs
import TauCeti.KnotTheory.BraidWord.DoubleCrossing.ExternalArcs
import TauCeti.KnotTheory.BraidWord.CrossinglessComponents
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Equivalence
import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Circle.Orientation

/-!
# Free cancellation as an algebraic clasp

An adjacent inverse pair prepended to a braid word cuts the two affected strands at the closure
and inserts a Reidemeister-II clasp:

* When both positions already meet crossings, this is the two-arc clasp `PDCode.insertClasp` on
  their closing arcs, up to relabeling and crossing rotation
  (`reidemeisterEquiv_closure_cons_cons_freeCancel_insertClasp`). Together with the closing-arc
  face condition from `BraidWord.ClosingArcs`, this gives a Reidemeister-II move.
* When both positions are crossing-free, it is the two-circle clasp `adjoinTwoCircleClasp`.
* When only the lower position meets crossings, it is the circle-and-arc clasp
  `insertCircleClasp`.
* When only the higher position meets crossings, the isolated circle on the lower position runs
  against the arc it is pushed across: after reversing that circle
  (`TauCeti.OrientedPDCode.reidemeisterEquiv_adjoinCircle_not`) it is again `insertCircleClasp`,
  with the second new crossing read from its opposite slot.

Combining all four cases yields unrestricted free-cancellation invariance for a prepended inverse
pair (`reidemeisterEquiv_closure_cons_cons_freeCancel`).

## Main results

* `TauCeti.BraidWord.reidemeisterEquiv_closure_cons_cons_freeCancel_insertClasp`: identify a
  prepended inverse pair with the algebraic clasp on the two existing closing arcs, using only
  relabeling and crossing rotation (no common-face or planarity hypothesis).
* `TauCeti.BraidWord.reidemeisterEquiv_closure_cons_cons_freeCancel`: prepending an inverse pair
  preserves the oriented braid closure up to Reidemeister moves, with no assumption on whether
  either affected position already meets crossings.

## References

* J. Birman, *Braids, Links, and Mapping Class Groups*, Chapter 2.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapter 1.
-/

public section

namespace TauCeti.BraidWord

open BraidGroup PDCode Equiv

variable {n : ℕ}

/-! ### Shared relabeling and diagram-comparison machinery -/

private def claspCross (N : ℕ) : Fin (N + 2) ≃ Fin (N + 2) :=
  finAddFlip.trans (finCongr (Nat.add_comm 2 N))

@[simp] private theorem claspCross_old (N : ℕ) (j : Fin N) :
    claspCross N j.castSucc.castSucc = j.succ.succ := by
  have h : j.castSucc.castSucc = Fin.castAdd 2 j := Fin.castSucc_castAdd j
  simp only [claspCross, Equiv.trans_apply, h, finAddFlip_apply_castAdd, finCongr_apply]
  apply Fin.ext
  simp only [Fin.val_natAdd, Fin.val_succ, Fin.val_cast]
  omega

@[simp] private theorem claspCross_first (N : ℕ) :
    claspCross N (Fin.last N).castSucc = 0 := by
  have h : (Fin.last N).castSucc = Fin.natAdd N (0 : Fin 2) := by
    apply Fin.ext
    simp
  simp only [claspCross, Equiv.trans_apply, h, finAddFlip_apply_natAdd, finCongr_apply]
  apply Fin.ext
  simp

@[simp] private theorem claspCross_second (N : ℕ) :
    claspCross N (Fin.last (N + 1)) = 1 := by
  have h : Fin.last (N + 1) = Fin.natAdd N (1 : Fin 2) := by
    apply Fin.ext
    simp
  simp only [claspCross, Equiv.trans_apply, h, finAddFlip_apply_natAdd, finCongr_apply]
  apply Fin.ext
  simp

@[simp] private theorem claspCross_symm_old (N : ℕ) (j : Fin N) :
    (claspCross N).symm j.succ.succ = j.castSucc.castSucc :=
  (claspCross N).symm_apply_eq.mpr (claspCross_old N j).symm

@[simp] private theorem claspCross_symm_zero (N : ℕ) :
    (claspCross N).symm 0 = (Fin.last N).castSucc :=
  (claspCross N).symm_apply_eq.mpr (claspCross_first N).symm

@[simp] private theorem claspCross_symm_one (N : ℕ) :
    (claspCross N).symm 1 = Fin.last (N + 1) :=
  (claspCross N).symm_apply_eq.mpr (claspCross_second N).symm

/-- Half-edge relabeling moving the two trailing clasp crossings to positions `0` and `1` while
applying slot permutations `f₀` and `f₁` to those two crossings and leaving old crossings fixed. -/
private def claspHalfWith (N : ℕ) (f₀ f₁ : Fin 4 ≃ Fin 4) :
    Fin (4 * (N + 2)) ≃ Fin (4 * (N + 2)) :=
  (crossingSlotEquiv (N + 2)).symm.trans
    ((Equiv.prodCongrRight fun j : Fin (N + 2) =>
      if j = (Fin.last N).castSucc then f₀
      else if j = Fin.last (N + 1) then f₁
      else Equiv.refl (Fin 4)).trans
      ((Equiv.prodCongr (claspCross N) (Equiv.refl (Fin 4))).trans
        (crossingSlotEquiv (N + 2))))

@[simp] private theorem claspHalfWith_old_crossing (N : ℕ) (f₀ f₁ : Fin 4 ≃ Fin 4)
    (j : Fin N) (s : Fin 4) :
    claspHalfWith N f₀ f₁ (halfEdgeSuccEquiv (N + 1)
      (.inl (halfEdgeSuccEquiv N (.inl (crossingSlotEquiv N (j, s)))))) =
      crossingSlotEquiv (N + 2) (j.succ.succ, s) := by
  have h0 : (j : ℕ) ≠ N := by omega
  have h1 : (j : ℕ) ≠ N + 1 := by omega
  simp [← crossingSlotEquiv_succ_castSucc, claspHalfWith, Fin.ext_iff, h0, h1]

@[simp] private theorem claspHalfWith_first (N : ℕ) (f₀ f₁ : Fin 4 ≃ Fin 4) (s : Fin 4) :
    claspHalfWith N f₀ f₁ (halfEdgeSuccEquiv (N + 1) (.inl (halfEdgeSuccEquiv N (.inr s)))) =
      crossingSlotEquiv (N + 2) (0, f₀ s) := by
  simp [← crossingSlotEquiv_succ_last, ← crossingSlotEquiv_succ_castSucc, claspHalfWith]

@[simp] private theorem claspHalfWith_second (N : ℕ) (f₀ f₁ : Fin 4 ≃ Fin 4) (s : Fin 4) :
    claspHalfWith N f₀ f₁ (halfEdgeSuccEquiv (N + 1) (.inr s)) =
      crossingSlotEquiv (N + 2) (1, f₁ s) := by
  simp [← crossingSlotEquiv_succ_last, claspHalfWith, Fin.ext_iff]

private def claspHalf (N : ℕ) : Fin (4 * (N + 2)) ≃ Fin (4 * (N + 2)) :=
  claspHalfWith N (finRotate 4).symm (finRotate 4).symm

@[simp] private theorem claspHalf_old_crossing (N : ℕ) (j : Fin N) (s : Fin 4) :
    claspHalf N (halfEdgeSuccEquiv (N + 1)
      (.inl (halfEdgeSuccEquiv N (.inl (crossingSlotEquiv N (j, s)))))) =
      crossingSlotEquiv (N + 2) (j.succ.succ, s) :=
  claspHalfWith_old_crossing N _ _ j s

@[simp] private theorem claspHalf_first (N : ℕ) (s : Fin 4) :
    claspHalf N (halfEdgeSuccEquiv (N + 1) (.inl (halfEdgeSuccEquiv N (.inr s)))) =
      crossingSlotEquiv (N + 2) (0, s - 1) := by
  simp [claspHalf]

@[simp] private theorem claspHalf_second (N : ℕ) (s : Fin 4) :
    claspHalf N (halfEdgeSuccEquiv (N + 1) (.inr s)) =
      crossingSlotEquiv (N + 2) (1, s - 1) := by
  simp [claspHalf]

/-- Half-edge relabeling for the circle-and-arc clasp with the circle on the lower position:
no slot shift at the first new crossing, and opposite-slot shift at the second. -/
private def lowerClaspHalf (N : ℕ) : Fin (4 * (N + 2)) ≃ Fin (4 * (N + 2)) :=
  claspHalfWith N (Equiv.refl (Fin 4)) (Equiv.addRight 2)

@[simp] private theorem lowerClaspHalf_old_crossing (N : ℕ) (j : Fin N) (s : Fin 4) :
    lowerClaspHalf N (halfEdgeSuccEquiv (N + 1)
      (.inl (halfEdgeSuccEquiv N (.inl (crossingSlotEquiv N (j, s)))))) =
      crossingSlotEquiv (N + 2) (j.succ.succ, s) :=
  claspHalfWith_old_crossing N _ _ j s

@[simp] private theorem lowerClaspHalf_first (N : ℕ) (s : Fin 4) :
    lowerClaspHalf N (halfEdgeSuccEquiv (N + 1) (.inl (halfEdgeSuccEquiv N (.inr s)))) =
      crossingSlotEquiv (N + 2) (0, s) :=
  claspHalfWith_first N _ _ s

@[simp] private theorem lowerClaspHalf_second (N : ℕ) (s : Fin 4) :
    lowerClaspHalf N (halfEdgeSuccEquiv (N + 1) (.inr s)) =
      crossingSlotEquiv (N + 2) (1, s + 2) :=
  claspHalfWith_second N _ _ s

private def readClaspWith {N : ℕ} (f₀ f₁ : Fin 4 ≃ Fin 4) (k₀ k₁ : ℕ)
    (D : OrientedPDCode (N + 2)) : OrientedPDCode (N + 2) :=
  (fun C => C.rotateCrossing 1)^[k₁]
    ((fun C => C.rotateCrossing 0)^[k₀] (D.relabel (claspHalfWith N f₀ f₁) (claspCross N)))

private def readClasp {N : ℕ} (D : OrientedPDCode (N + 2)) : OrientedPDCode (N + 2) :=
  readClaspWith (finRotate 4).symm (finRotate 4).symm 1 1 D

private def readLowerClasp {N : ℕ} (D : OrientedPDCode (N + 2)) : OrientedPDCode (N + 2) :=
  readClaspWith (Equiv.refl (Fin 4)) (Equiv.addRight 2) 0 2 D

private theorem reidemeisterEquiv_readClaspWith {N : ℕ} (f₀ f₁ : Fin 4 ≃ Fin 4)
    (k₀ k₁ : ℕ) (D : OrientedPDCode (N + 2)) :
    OrientedPDCode.ReidemeisterEquiv D (readClaspWith f₀ f₁ k₀ k₁ D) :=
  (OrientedPDCode.reidemeisterEquiv_relabel D (claspHalfWith N f₀ f₁) (claspCross N)).trans
    ((OrientedPDCode.reidemeisterEquiv_iterate_rotateCrossing _ 0 k₀).trans
      (OrientedPDCode.reidemeisterEquiv_iterate_rotateCrossing _ 1 k₁))

private theorem reidemeisterEquiv_readClasp {N : ℕ} (D : OrientedPDCode (N + 2)) :
    OrientedPDCode.ReidemeisterEquiv D (readClasp D) :=
  reidemeisterEquiv_readClaspWith _ _ 1 1 D

private theorem reidemeisterEquiv_readLowerClasp {N : ℕ} (D : OrientedPDCode (N + 2)) :
    OrientedPDCode.ReidemeisterEquiv D (readLowerClasp D) :=
  reidemeisterEquiv_readClaspWith _ _ 0 2 D

private theorem readClaspWith_edgePair_apply {N : ℕ} (f₀ f₁ : Fin 4 ≃ Fin 4)
    (k₀ k₁ : ℕ) (D : OrientedPDCode (N + 2)) (x : Fin (4 * (N + 2))) :
    (readClaspWith f₀ f₁ k₀ k₁ D).edgePair.val (claspHalfWith N f₀ f₁ x) =
      claspHalfWith N f₀ f₁ (D.edgePair.val x) := by
  simp [readClaspWith]

private theorem readClasp_edgePair_apply {N : ℕ} (D : OrientedPDCode (N + 2))
    (x : Fin (4 * (N + 2))) :
    (readClasp D).edgePair.val (claspHalf N x) = claspHalf N (D.edgePair.val x) :=
  readClaspWith_edgePair_apply _ _ 1 1 D x

private theorem readLowerClasp_edgePair_apply {N : ℕ} (D : OrientedPDCode (N + 2))
    (x : Fin (4 * (N + 2))) :
    (readLowerClasp D).edgePair.val (lowerClaspHalf N x) =
      lowerClaspHalf N (D.edgePair.val x) :=
  readClaspWith_edgePair_apply _ _ 0 2 D x

@[simp] private theorem readClaspWith_crossinglessComponents {N : ℕ} (f₀ f₁ : Fin 4 ≃ Fin 4)
    (k₀ k₁ : ℕ) (D : OrientedPDCode (N + 2)) :
    (readClaspWith f₀ f₁ k₀ k₁ D).crossinglessComponents = D.crossinglessComponents := by
  simp [readClaspWith]

private theorem readClaspWith_halfEdge {N : ℕ} {f₀ f₁ : Fin 4 ≃ Fin 4} {k₀ k₁ : ℕ}
    {D : OrientedPDCode (N + 2)} (h : D.halfEdge = 1)
    (hf₀ : ∀ s : Fin 4, f₀ (s + k₀ • 1) = s)
    (hf₁ : ∀ s : Fin 4, f₁ (s + k₁ • 1) = s) :
    (readClaspWith f₀ f₁ k₀ k₁ D).halfEdge = 1 := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨j, s⟩, rfl⟩ := (crossingSlotEquiv (N + 2)).surjective x
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · simp [readClaspWith, h, crossingSlotEquiv_succ_castSucc, crossingSlotEquiv_succ_last,
      zero_ne_one, hf₀]
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · simp [readClaspWith, h, crossingSlotEquiv_succ_last, Fin.succ_zero_eq_one, one_ne_zero, hf₁]
    · simp [readClaspWith, h, crossingSlotEquiv_succ_castSucc, Fin.ext_iff]

private theorem readClasp_halfEdge {N : ℕ} {D : OrientedPDCode (N + 2)} (h : D.halfEdge = 1) :
    (readClasp D).halfEdge = 1 :=
  readClaspWith_halfEdge h (fun s => by simp) (fun s => by simp)

private theorem readLowerClasp_halfEdge {N : ℕ} {D : OrientedPDCode (N + 2)}
    (h : D.halfEdge = 1) :
    (readLowerClasp D).halfEdge = 1 :=
  readClaspWith_halfEdge h (fun s => by simp) (fun s => by fin_cases s <;> decide)

private theorem halfEdge_eq_one_of_succ {N : ℕ} {D : OrientedPDCode (N + 2)}
    (hold : ∀ (j : Fin N) (s : Fin 4), D.halfEdge (halfEdgeSuccEquiv (N + 1)
      (.inl (halfEdgeSuccEquiv N (.inl (crossingSlotEquiv N (j, s)))))) =
      halfEdgeSuccEquiv (N + 1) (.inl (halfEdgeSuccEquiv N (.inl (crossingSlotEquiv N (j, s))))))
    (h0 : ∀ s : Fin 4, D.halfEdge (halfEdgeSuccEquiv (N + 1)
      (.inl (halfEdgeSuccEquiv N (.inr s)))) =
      halfEdgeSuccEquiv (N + 1) (.inl (halfEdgeSuccEquiv N (.inr s))))
    (h1 : ∀ s : Fin 4, D.halfEdge (halfEdgeSuccEquiv (N + 1) (.inr s)) =
      halfEdgeSuccEquiv (N + 1) (.inr s)) :
    D.halfEdge = 1 := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨j, s⟩, rfl⟩ := (crossingSlotEquiv (N + 2)).surjective x
  refine Fin.lastCases ?_ (fun j => Fin.lastCases ?_ (fun j => ?_) j) j
  · simpa only [← crossingSlotEquiv_succ_last, Equiv.Perm.one_apply] using h1 s
  · simpa only [← crossingSlotEquiv_succ_castSucc, ← crossingSlotEquiv_succ_last,
      Equiv.Perm.one_apply] using h0 s
  · simpa only [← crossingSlotEquiv_succ_castSucc, Equiv.Perm.one_apply] using hold j s

private theorem readClaspWith_orientation_eq_closure
    {v : BraidWord n} {i : Fin (n - 1)} {ε : ℤˣ} {f₀ f₁ : Fin 4 ≃ Fin 4} {k₀ k₁ : ℕ}
    {D : OrientedPDCode (v.length + 2)}
    (h0 : ∀ s : Fin 4, D.orientation
        (halfEdgeSuccEquiv (v.length + 1)
          (.inl (halfEdgeSuccEquiv v.length (.inr (f₀.symm s))))) =
      decide (s = 1 ∨ s = 2))
    (h1 : ∀ s : Fin 4, D.orientation
        (halfEdgeSuccEquiv (v.length + 1) (.inr (f₁.symm s))) =
      decide (s = 1 ∨ s = 2))
    (hold : ∀ (j : Fin v.length) (s : Fin 4), D.orientation
        (halfEdgeSuccEquiv (v.length + 1)
          (.inl (halfEdgeSuccEquiv v.length (.inl (crossingSlotEquiv v.length (j, s)))))) =
      v.closure.orientation (crossingSlotEquiv v.length (j, s))) :
    (readClaspWith f₀ f₁ k₀ k₁ D).orientation =
      (closure ((i, ε) :: (i, -ε) :: v)).orientation := by
  rw [readClaspWith, OrientedPDCode.iterate_rotateCrossing_orientation,
    OrientedPDCode.iterate_rotateCrossing_orientation]
  funext x
  obtain ⟨⟨j, s⟩, rfl⟩ := (crossingSlotEquiv (v.length + 2)).surjective x
  have hori : (closure ((i, ε) :: (i, -ε) :: v)).orientation
      (crossingSlotEquiv (v.length + 2) (j, s)) = decide (s = 1 ∨ s = 2) := by
    simpa only [List.length_cons] using orientation_closure ((i, ε) :: (i, -ε) :: v) j s
  rw [hori]
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · have h := claspHalfWith_first v.length f₀ f₁ (f₀.symm s)
    simp only [Equiv.apply_symm_apply] at h
    rw [← h, OrientedPDCode.relabel_orientation, Equiv.symm_apply_apply]
    exact h0 s
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · have h := claspHalfWith_second v.length f₀ f₁ (f₁.symm s)
      simp only [Equiv.apply_symm_apply] at h
      rw [Fin.succ_zero_eq_one, ← h, OrientedPDCode.relabel_orientation, Equiv.symm_apply_apply]
      exact h1 s
    · rw [← claspHalfWith_old_crossing v.length f₀ f₁, OrientedPDCode.relabel_orientation,
        Equiv.symm_apply_apply, hold, orientation_closure]

private theorem overPair_eq_closure_cons_cons {v : BraidWord n} {i : Fin (n - 1)} {ε : ℤˣ}
    {C : OrientedPDCode (v.length + 2)}
    (h0 : C.overPair 0 = decide (ε = 1))
    (h1 : C.overPair 1 = !decide (ε = 1))
    (hold : ∀ j : Fin v.length, C.overPair j.succ.succ = v.closure.overPair j) :
    C.overPair = (closure ((i, ε) :: (i, -ε) :: v)).overPair := by
  funext j
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · rcases Int.units_eq_one_or ε with rfl | rfl <;> simpa [overPair_closure] using h0
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · rcases Int.units_eq_one_or ε with rfl | rfl <;>
        simpa [overPair_closure, Fin.succ_zero_eq_one] using h1
    · simpa [overPair_closure] using hold j

private theorem eq_closure_cons_cons_of_fields {v : BraidWord n} {i : Fin (n - 1)} {ε : ℤˣ}
    {C : OrientedPDCode (v.length + 2)}
    (hhalf : C.halfEdge = 1)
    (hedge : (closure ((i, ε) :: (i, -ε) :: v)).edgePair = C.edgePair)
    (hover : C.overPair = (closure ((i, ε) :: (i, -ε) :: v)).overPair)
    (hori : C.orientation = (closure ((i, ε) :: (i, -ε) :: v)).orientation)
    (hc : C.crossinglessComponents =
      (closure ((i, ε) :: (i, -ε) :: v)).crossinglessComponents) :
    C = closure ((i, ε) :: (i, -ε) :: v) := by
  apply OrientedPDCode.ext
  · apply PDCode.ext
    · simpa only [halfEdge_closure] using hhalf
    · exact hedge.symm
    · simpa only [OrientedPDCode.card_crossinglessComponents] using congrArg Multiset.card hc
    · exact hover
  · exact hori
  · exact hc

private theorem fields_eq_of_adjoinCircle {N : ℕ} {core D : OrientedPDCode N} {o : Bool}
    (h : core.adjoinCircle o = D) :
    core.halfEdge = D.halfEdge ∧ core.edgePair = D.edgePair ∧
      core.overPair = D.overPair ∧ core.orientation = D.orientation := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using congrArg (fun C => C.halfEdge) h
  · simpa using congrArg (fun C => C.edgePair) h
  · simpa using congrArg (fun C => C.overPair) h
  · simpa using congrArg OrientedPDCode.orientation h

private theorem crossinglessComponents_eq_of_adjoinCircle {N : ℕ} {core D : OrientedPDCode N}
    {o : Bool} {m : Multiset Bool} (hcore : core.adjoinCircle o = D)
    (hm : D.crossinglessComponents = o ::ₘ m) :
    core.crossinglessComponents = m := by
  have h := congrArg OrientedPDCode.crossinglessComponents hcore
  rw [hm] at h
  simpa only [OrientedPDCode.crossinglessComponents_adjoinCircle,
    Multiset.cons_inj_right] using h

private theorem exists_adjoinCircle_core {N : ℕ} {D : OrientedPDCode N} {m : Multiset Bool}
    (hm : D.crossinglessComponents = true ::ₘ m) :
    ∃ core : OrientedPDCode N,
      core.adjoinCircle true = D ∧ core.crossinglessComponents = m := by
  obtain ⟨core, hcore⟩ :=
    OrientedPDCode.exists_eq_adjoinCircle_of_mem (o := true) (by rw [hm]; simp)
  exact ⟨core, hcore.symm, crossinglessComponents_eq_of_adjoinCircle hcore.symm hm⟩

private theorem crossinglessComponents_cons_cons_of_two_nil {v : BraidWord n} {i : Fin (n - 1)}
    {ε : ℤˣ} (hp₀ : v.crossingsAt (strand i) = []) (hq₀ : v.crossingsAt (strandSucc i) = []) :
    v.closure.crossinglessComponents =
      true ::ₘ true ::ₘ (closure ((i, ε) :: (i, -ε) :: v)).crossinglessComponents := by
  have hc := crossinglessComponents_closure_insert_pair ([] : BraidWord n) v i ε (-ε)
  simp only [List.nil_append, List.cons_append, hp₀, hq₀, ite_true, Multiset.replicate_one] at hc
  rw [Multiset.add_comm _ {true}, Multiset.singleton_add,
    Multiset.add_comm _ {true}, Multiset.singleton_add] at hc
  exact hc.symm

private theorem crossinglessComponents_cons_cons_of_one_nil {v : BraidWord n} {i : Fin (n - 1)}
    {ε : ℤˣ}
    (h : (v.crossingsAt (strand i) ≠ [] ∧ v.crossingsAt (strandSucc i) = []) ∨
      (v.crossingsAt (strand i) = [] ∧ v.crossingsAt (strandSucc i) ≠ [])) :
    v.closure.crossinglessComponents =
      true ::ₘ (closure ((i, ε) :: (i, -ε) :: v)).crossinglessComponents := by
  have hc := crossinglessComponents_closure_insert_pair ([] : BraidWord n) v i ε (-ε)
  rcases h with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;>
    simp only [List.nil_append, List.cons_append, hp, hq, ite_false, ite_true,
      Multiset.replicate_zero, Multiset.replicate_one, add_zero] at hc <;>
    rw [Multiset.add_comm _ {true}, Multiset.singleton_add] at hc <;>
    exact hc.symm

private theorem unionOld (N : ℕ) (j : Fin N) (s : Fin 4) :
    disjointUnionHalfEdgeEquiv N 2 (.inl (crossingSlotEquiv N (j, s))) =
      halfEdgeSuccEquiv (N + 1) (.inl (halfEdgeSuccEquiv N
        (.inl (crossingSlotEquiv N (j, s))))) := by
  have h : j.castSucc.castSucc = Fin.castAdd 2 j := Fin.castSucc_castAdd j
  simp only [disjointUnionHalfEdgeEquiv_inl_crossingSlot, ← crossingSlotEquiv_succ_castSucc, h]

private theorem unionFirst (N : ℕ) (s : Fin 4) :
    disjointUnionHalfEdgeEquiv N 2 (.inr (crossingSlotEquiv 2 (0, s))) =
      halfEdgeSuccEquiv (N + 1) (.inl (halfEdgeSuccEquiv N (.inr s))) := by
  have h : Fin.natAdd N (0 : Fin 2) = (Fin.last N).castSucc := by
    apply Fin.ext
    simp
  simp only [disjointUnionHalfEdgeEquiv_inr_crossingSlot, h,
    ← crossingSlotEquiv_succ_castSucc, ← crossingSlotEquiv_succ_last]

private theorem unionSecond (N : ℕ) (s : Fin 4) :
    disjointUnionHalfEdgeEquiv N 2 (.inr (crossingSlotEquiv 2 (1, s))) =
      halfEdgeSuccEquiv (N + 1) (.inr s) := by
  have h : Fin.natAdd N (1 : Fin 2) = Fin.last (N + 1) := Fin.natAdd_last
  simp only [disjointUnionHalfEdgeEquiv_inr_crossingSlot, h, ← crossingSlotEquiv_succ_last]

/-! ### Case 1: both participating positions already meet crossings -/

section TwoArcs

variable (v : BraidWord n) (i : Fin (n - 1)) (ε : ℤˣ)
  (hp : v.crossingsAt (strand i) ≠ []) (hq : v.crossingsAt (strandSucc i) ≠ [])

private def closingClasp : OrientedPDCode (v.length + 2) :=
  v.closure.insertClasp (v.closingHalfEdge (strand i) hp)
    (v.closingHalfEdge (strandSucc i) hq) (!decide (ε = 1))
    (v.closingHalfEdge_ne hq hp (strand_ne_strandSucc i).symm)
    (v.closingHalfEdge_ne_edgePair_closingHalfEdge _ _ hp hq)

private theorem readClosingClasp_edgePair_old {j : Fin v.length} {p : Fin n}
    (hjold : j ∈ v.crossingsAt p) :
    (closure ((i, ε) :: (i, -ε) :: v)).edgePair.val
        (crossingSlotEquiv (v.length + 2) (j.succ.succ, v.outgoingSlot j p)) =
      (readClasp (closingClasp v i ε hp hq)).edgePair.val
        (crossingSlotEquiv (v.length + 2) (j.succ.succ, v.outgoingSlot j p)) := by
  let x := v.closure.crossing j (v.outgoingSlot j p)
  have hmatch := readClasp_edgePair_apply (closingClasp v i ε hp hq)
    (halfEdgeSuccEquiv (v.length + 1) (.inl (halfEdgeSuccEquiv v.length (.inl x))))
  have hxembed : claspHalf v.length
      (halfEdgeSuccEquiv (v.length + 1) (.inl (halfEdgeSuccEquiv v.length (.inl x)))) =
      crossingSlotEquiv (v.length + 2) (j.succ.succ, v.outgoingSlot j p) := by
    simp only [x, crossing_closure, claspHalf_old_crossing]
  rw [hxembed] at hmatch
  by_cases hxp : x = v.closingHalfEdge (strand i) hp
  · obtain ⟨rfl, rfl⟩ := (crossing_outgoingSlot_eq_closingHalfEdge_iff v hjold hp).mp hxp
    simp only [closingClasp, OrientedPDCode.toPDCode_insertClasp, hxp,
      insertClasp_edgePair_inl_inl_self, claspHalf_first, Fin.reduceSub] at hmatch
    have h := edgePair_closure_cons_cons_of_mem v i ε (-ε) (List.getLast_mem hp)
    have hin : incomingSlot ((i, ε) :: (i, -ε) :: v) 0 (strand i) = 3 := by
      simpa using incomingSlot_strand ((i, ε) :: (i, -ε) :: v) 0
    simp only [nextCrossing_getLast_crossingsAt, true_or, true_and, ite_true,
      crossing_closure, List.length_cons, hin] at h
    exact h.trans hmatch.symm
  · by_cases hxq : x = v.closingHalfEdge (strandSucc i) hq
    · obtain ⟨rfl, rfl⟩ := (crossing_outgoingSlot_eq_closingHalfEdge_iff v hjold hq).mp hxq
      simp only [closingClasp, OrientedPDCode.toPDCode_insertClasp, hxq,
        insertClasp_edgePair_inl_inl_right, claspHalf_first, Fin.reduceSub] at hmatch
      have h := edgePair_closure_cons_cons_of_mem v i ε (-ε) (List.getLast_mem hq)
      have hin : incomingSlot ((i, ε) :: (i, -ε) :: v) 0 (strandSucc i) = 0 := by
        simpa using incomingSlot_strandSucc ((i, ε) :: (i, -ε) :: v) 0
      simp only [nextCrossing_getLast_crossingsAt, or_true, true_and, ite_true,
        crossing_closure, List.length_cons, hin] at h
      exact h.trans hmatch.symm
    · have hxe := v.crossing_outgoingSlot_ne_edgePair_closingHalfEdge (j := j) p hp
      have hxe' := v.crossing_outgoingSlot_ne_edgePair_closingHalfEdge (j := j) p hq
      simp only [closingClasp, OrientedPDCode.toPDCode_insertClasp,
        v.closure.toPDCode.insertClasp_edgePair_inl_inl_of_ne _ _ _ _ _ hxp hxe hxq hxe']
        at hmatch
      simp only [x] at hmatch
      rw [edgePair_closure_outgoingSlot v hjold, crossing_closure, claspHalf_old_crossing] at hmatch
      have hc := v.not_nextCrossing_eq_head_of_ne_closingHalfEdge i hp hq hjold hxp hxq
      have h := edgePair_closure_cons_cons_of_mem v i ε (-ε) hjold
      simp only [hc, ite_false, crossing_closure, List.length_cons] at h
      exact h.trans hmatch.symm

private theorem readClosingClasp_edgePair :
    (closure ((i, ε) :: (i, -ε) :: v)).edgePair =
      (readClasp (closingClasp v i ε hp hq)).edgePair := by
  let D := closingClasp v i ε hp hq
  have hfirst₁ := readClasp_edgePair_apply D
    (halfEdgeSuccEquiv (v.length + 1) (.inl (halfEdgeSuccEquiv v.length (.inr 2))))
  have hfirst₂ := readClasp_edgePair_apply D
    (halfEdgeSuccEquiv (v.length + 1) (.inl (halfEdgeSuccEquiv v.length (.inr 3))))
  have hsecond₁ := readClasp_edgePair_apply D (halfEdgeSuccEquiv (v.length + 1) (.inr 2))
  have hsecond₂ := readClasp_edgePair_apply D (halfEdgeSuccEquiv (v.length + 1) (.inr 3))
  simp only [D, closingClasp, OrientedPDCode.toPDCode_insertClasp,
    insertClasp_edgePair_inl_inr_two, insertClasp_edgePair_inl_inr_three,
    insertClasp_edgePair_inr_two, insertClasp_edgePair_inr_three,
    claspHalf_first, claspHalf_second, edgePair_closingHalfEdge, crossing_closure,
    claspHalf_old_crossing, Fin.reduceSub] at hfirst₁ hfirst₂ hsecond₁ hsecond₂
  refine edgePair_closure_cons_cons_eq_of_outgoingSlot v i ε (-ε) ?_ ?_ ?_ ?_
    fun hjold ↦ readClosingClasp_edgePair_old v i ε hp hq hjold
  · exact (edgePair_closure_cons_cons_one v i ε (-ε)).trans hfirst₁.symm
  · exact (edgePair_closure_cons_cons_two v i ε (-ε)).trans hfirst₂.symm
  · exact (edgePair_closure_cons_cons_one_one_of_ne_nil v i ε (-ε) hq).trans hsecond₁.symm
  · exact (edgePair_closure_cons_cons_one_two_of_ne_nil v i ε (-ε) hp).trans hsecond₂.symm

private theorem readClosingClasp_eq :
    readClasp (closingClasp v i ε hp hq) = closure ((i, ε) :: (i, -ε) :: v) := by
  refine eq_closure_cons_cons_of_fields ?_ (readClosingClasp_edgePair v i ε hp hq) ?_ ?_ ?_
  · exact readClasp_halfEdge (halfEdge_eq_one_of_succ
      (fun _ _ => by simp [closingClasp]) (fun _ => by simp [closingClasp])
      (fun _ => by simp [closingClasp]))
  · refine overPair_eq_closure_cons_cons ?_ ?_ fun j ↦ ?_
    · simp [readClasp, readClaspWith, closingClasp]
    · simp [readClasp, readClaspWith, closingClasp, one_ne_zero]
    · simp [readClasp, readClaspWith, closingClasp, Fin.ext_iff]
  · refine readClaspWith_orientation_eq_closure (fun s ↦ ?_) (fun s ↦ ?_) fun j s ↦ ?_
    · simp only [closingClasp, OrientedPDCode.orientation_insertClasp_inl_inr,
        orientation_closingHalfEdge]
      fin_cases s <;> decide
    · simp only [closingClasp, OrientedPDCode.orientation_insertClasp_inr,
        orientation_closingHalfEdge]
      fin_cases s <;> decide
    · simp only [closingClasp, OrientedPDCode.orientation_insertClasp_inl_inl]
  · have hc := crossinglessComponents_closure_insert_pair ([] : BraidWord n) v i ε (-ε)
    simp only [List.nil_append, hp, hq, ite_false, Multiset.replicate_zero, add_zero] at hc
    simpa [readClasp, closingClasp] using hc.symm

end TwoArcs

/-- When both positions meet old crossings, an inverse pair in a braid closure is the
algebraic clasp on their closing arcs, up to the diagram isomorphisms generated by relabeling
and crossing rotation. No common-face or planarity hypothesis is required for this comparison. -/
theorem reidemeisterEquiv_closure_cons_cons_freeCancel_insertClasp
    (v : BraidWord n) (i : Fin (n - 1)) (ε : ℤˣ)
    (hp : v.crossingsAt (strand i) ≠ []) (hq : v.crossingsAt (strandSucc i) ≠ []) :
    OrientedPDCode.ReidemeisterEquiv (closure ((i, ε) :: (i, -ε) :: v))
      (v.closure.insertClasp (v.closingHalfEdge (strand i) hp)
        (v.closingHalfEdge (strandSucc i) hq) (!decide (ε = 1))
        (v.closingHalfEdge_ne hq hp (strand_ne_strandSucc i).symm)
        (v.closingHalfEdge_ne_edgePair_closingHalfEdge _ _ hp hq)) := by
  rw [← readClosingClasp_eq v i ε hp hq]
  exact (reidemeisterEquiv_readClasp _).symm

/-! ### Case 2: both participating positions are crossing-free -/

section TwoCircles

private def twoCircleDiagram {N : ℕ} (ε : ℤˣ) (core : OrientedPDCode N) :
    OrientedPDCode (N + 2) :=
  core.adjoinTwoCircleClasp true true (!decide (ε = 1))

private theorem readTwoCircleDiagram_edgePair_old {v : BraidWord n} {i : Fin (n - 1)} {ε : ℤˣ}
    (hp₀ : v.crossingsAt (strand i) = []) (hq₀ : v.crossingsAt (strandSucc i) = [])
    {core : OrientedPDCode v.length} (hedge : core.edgePair = v.closure.edgePair)
    {j : Fin v.length} {p : Fin n} (hjold : j ∈ v.crossingsAt p) :
    (closure ((i, ε) :: (i, -ε) :: v)).edgePair.val
        (crossingSlotEquiv _ (j.succ.succ, v.outgoingSlot j p)) =
      (readClasp (twoCircleDiagram ε core)).edgePair.val
        (crossingSlotEquiv _ (j.succ.succ, v.outgoingSlot j p)) := by
  have hpos : p ≠ strand i ∧ p ≠ strandSucc i := by
    constructor <;> intro h <;> subst p <;> simp_all
  have h := edgePair_closure_cons_cons_of_mem v i ε (-ε) hjold
  simp only [hpos.1, hpos.2, false_or, false_and, ite_false, crossing_closure,
    List.length_cons] at h
  have hm := readClasp_edgePair_apply (twoCircleDiagram ε core)
    (disjointUnionHalfEdgeEquiv v.length 2 (.inl (v.closure.crossing j (v.outgoingSlot j p))))
  simp only [twoCircleDiagram, OrientedPDCode.adjoinTwoCircleClasp_def,
    OrientedPDCode.toPDCode_disjointUnion, disjointUnion_edgePair_val,
    Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.Perm.sumCongr_apply, Sum.map_inl,
    hedge] at hm
  rw [edgePair_closure_outgoingSlot v hjold] at hm
  simp only [crossing_closure, unionOld, claspHalf_old_crossing] at hm
  simpa only [twoCircleDiagram, OrientedPDCode.adjoinTwoCircleClasp_def, List.length_cons]
    using h.trans hm.symm

private theorem readTwoCircleDiagram_edgePair {v : BraidWord n} {i : Fin (n - 1)} {ε : ℤˣ}
    (hp₀ : v.crossingsAt (strand i) = []) (hq₀ : v.crossingsAt (strandSucc i) = [])
    {core : OrientedPDCode v.length} (hedge : core.edgePair = v.closure.edgePair) :
    (closure ((i, ε) :: (i, -ε) :: v)).edgePair =
      (readClasp (twoCircleDiagram ε core)).edgePair := by
  let C := twoCircleDiagram ε core
  have hmatch (k : Fin 2) (s : Fin 4) :
      (readClasp C).edgePair.val (claspHalf v.length
        (disjointUnionHalfEdgeEquiv v.length 2 (.inr (crossingSlotEquiv 2 (k, s))))) =
      claspHalf v.length (disjointUnionHalfEdgeEquiv v.length 2
        (.inr (crossingSlotEquiv 2 (k.rev, s.rev)))) := by
    simpa [C, twoCircleDiagram, OrientedPDCode.adjoinTwoCircleClasp_def, disjointUnion_edgePair_val]
      using readClasp_edgePair_apply C
        (disjointUnionHalfEdgeEquiv v.length 2 (.inr (crossingSlotEquiv 2 (k, s))))
  have hm₀₁ := hmatch 0 2
  have hm₀₂ := hmatch 0 3
  have hm₁₁ := hmatch 1 2
  have hm₁₂ := hmatch 1 3
  simp only [unionFirst, unionSecond, claspHalf_first, claspHalf_second, Fin.reduceRev,
    Fin.reduceSub] at hm₀₁ hm₀₂ hm₁₁ hm₁₂
  refine edgePair_closure_cons_cons_eq_of_outgoingSlot v i ε (-ε) ?_ ?_ ?_ ?_
    fun hjold ↦ readTwoCircleDiagram_edgePair_old hp₀ hq₀ hedge hjold
  · exact (edgePair_closure_cons_cons_one v i ε (-ε)).trans hm₀₁.symm
  · exact (edgePair_closure_cons_cons_two v i ε (-ε)).trans hm₀₂.symm
  · exact (edgePair_closure_cons_cons_one_one_of_nil v i ε (-ε) hq₀).trans hm₁₁.symm
  · exact (edgePair_closure_cons_cons_one_two_of_nil v i ε (-ε) hp₀).trans hm₁₂.symm

private theorem readTwoCircleDiagram_eq {v : BraidWord n} {i : Fin (n - 1)} {ε : ℤˣ}
    (hp₀ : v.crossingsAt (strand i) = []) (hq₀ : v.crossingsAt (strandSucc i) = [])
    {core : OrientedPDCode v.length}
    (hcore : (core.adjoinCircle true).adjoinCircle true = v.closure) :
    readClasp (twoCircleDiagram ε core) = closure ((i, ε) :: (i, -ε) :: v) := by
  obtain ⟨hhalf₁, hedge₁, hover₁, hori₁⟩ :=
    fields_eq_of_adjoinCircle (rfl : core.adjoinCircle true = _)
  obtain ⟨hhalf₂, hedge₂, hover₂, hori₂⟩ := fields_eq_of_adjoinCircle hcore
  have hhalf : core.halfEdge = 1 := by rw [hhalf₁, hhalf₂, halfEdge_closure]
  have hedge : core.edgePair = v.closure.edgePair := hedge₁.trans hedge₂
  have hover : core.overPair = v.closure.overPair := hover₁.trans hover₂
  have hori : core.orientation = v.closure.orientation := hori₁.trans hori₂
  have hc : core.crossinglessComponents =
      (closure ((i, ε) :: (i, -ε) :: v)).crossinglessComponents :=
    crossinglessComponents_eq_of_adjoinCircle (rfl : core.adjoinCircle true = _)
      (crossinglessComponents_eq_of_adjoinCircle hcore
        (crossinglessComponents_cons_cons_of_two_nil hp₀ hq₀))
  refine eq_closure_cons_cons_of_fields ?_ (readTwoCircleDiagram_edgePair hp₀ hq₀ hedge) ?_ ?_ ?_
  · exact readClasp_halfEdge (by
      ext x
      simp [twoCircleDiagram, OrientedPDCode.adjoinTwoCircleClasp_def, disjointUnion_halfEdge,
        hhalf])
  · have hfirst : (Fin.last v.length).castSucc = Fin.natAdd v.length (0 : Fin 2) := by
      apply Fin.ext; simp
    have hsecond : Fin.last (v.length + 1) = Fin.natAdd v.length (1 : Fin 2) := Fin.natAdd_last.symm
    refine overPair_eq_closure_cons_cons ?_ ?_ fun j ↦ ?_
    · simp [readClasp, readClaspWith, twoCircleDiagram, OrientedPDCode.adjoinTwoCircleClasp_def,
        hfirst]
    · simp [readClasp, readClaspWith, twoCircleDiagram, OrientedPDCode.adjoinTwoCircleClasp_def,
        hsecond, one_ne_zero]
    · have hj : j.castSucc.castSucc = Fin.castAdd 2 j := Fin.castSucc_castAdd j
      simp [readClasp, readClaspWith, twoCircleDiagram, OrientedPDCode.adjoinTwoCircleClasp_def,
        hover, hj, Fin.ext_iff]
  · refine readClaspWith_orientation_eq_closure (fun s ↦ ?_) (fun s ↦ ?_) fun j s ↦ ?_
    · rw [twoCircleDiagram, OrientedPDCode.adjoinTwoCircleClasp_def, ← unionFirst,
        OrientedPDCode.orientation_disjointUnion_inr, OrientedPDCode.orientation_twoCircleClasp]
      fin_cases s <;> decide
    · rw [twoCircleDiagram, OrientedPDCode.adjoinTwoCircleClasp_def, ← unionSecond,
        OrientedPDCode.orientation_disjointUnion_inr, OrientedPDCode.orientation_twoCircleClasp]
      fin_cases s <;> decide
    · rw [twoCircleDiagram, OrientedPDCode.adjoinTwoCircleClasp_def, ← unionOld,
        OrientedPDCode.orientation_disjointUnion_inl, hori]
  · simpa [readClasp, twoCircleDiagram] using hc

end TwoCircles

/-! ### Cases 3 and 4: one crossing-free position and one position meeting crossings -/

section CircleArc

/-- Shared old-crossing arc comparison for `insertCircleClasp`, covering both the higher-circle
and lower-circle readings. -/
private theorem readInsertCircleClasp_edgePair_old {v : BraidWord n} {i : Fin (n - 1)} {ε : ℤˣ}
    {pArc pCircle : Fin n} (hpArc : v.crossingsAt pArc ≠ []) (hpCircle : v.crossingsAt pCircle = [])
    (hpArc_mem : pArc = strand i ∨ pArc = strandSucc i)
    (hother : ∀ p, p = strand i ∨ p = strandSucc i → p = pArc ∨ p = pCircle)
    {core : OrientedPDCode v.length} (hedge : core.edgePair = v.closure.edgePair)
    {o b : Bool} {f₀ f₁ : Fin 4 ≃ Fin 4}
    (hf₀ : f₀ 0 = incomingSlot ((i, ε) :: (i, -ε) :: v) 0 pArc)
    {R : OrientedPDCode (v.length + 2)}
    (hR : ∀ x, R.edgePair.val (claspHalfWith v.length f₀ f₁ x) =
      claspHalfWith v.length f₀ f₁
        ((core.insertCircleClasp (v.closingHalfEdge pArc hpArc) o b).edgePair.val x))
    {j : Fin v.length} {p : Fin n} (hj : j ∈ v.crossingsAt p) :
    (closure ((i, ε) :: (i, -ε) :: v)).edgePair.val
        (crossingSlotEquiv _ (j.succ.succ, v.outgoingSlot j p)) =
      R.edgePair.val (crossingSlotEquiv _ (j.succ.succ, v.outgoingSlot j p)) := by
  let x := v.closure.crossing j (v.outgoingSlot j p)
  have hm := hR (halfEdgeSuccEquiv (v.length + 1) (.inl (halfEdgeSuccEquiv v.length (.inl x))))
  rw [show claspHalfWith v.length f₀ f₁
      (halfEdgeSuccEquiv (v.length + 1) (.inl (halfEdgeSuccEquiv v.length (.inl x)))) =
      crossingSlotEquiv (v.length + 2) (j.succ.succ, v.outgoingSlot j p) by
    simp only [x, crossing_closure, claspHalfWith_old_crossing]] at hm
  by_cases hxa : x = v.closingHalfEdge pArc hpArc
  · obtain ⟨rfl, rfl⟩ := (crossing_outgoingSlot_eq_closingHalfEdge_iff v hj hpArc).mp hxa
    simp only [OrientedPDCode.toPDCode_insertCircleClasp, hxa] at hm
    rw [core.toPDCode.insertCircleClasp_edgePair_old_self, claspHalfWith_first, hf₀] at hm
    have h := edgePair_closure_cons_cons_of_mem v i ε (-ε) (List.getLast_mem hpArc)
    simp only [nextCrossing_getLast_crossingsAt, hpArc_mem, true_and, ite_true,
      crossing_closure, List.length_cons] at h
    exact h.trans hm.symm
  · have hxe : x ≠ core.edgePair.val (v.closingHalfEdge pArc hpArc) := by
      rw [hedge]; exact v.crossing_outgoingSlot_ne_edgePair_closingHalfEdge p hpArc
    simp only [OrientedPDCode.toPDCode_insertCircleClasp] at hm
    rw [core.toPDCode.insertCircleClasp_edgePair_old _ _ hxa hxe, hedge] at hm
    simp only [x] at hm
    rw [edgePair_closure_outgoingSlot v hj, crossing_closure, claspHalfWith_old_crossing] at hm
    have hc : ¬ ((p = strand i ∨ p = strandSucc i) ∧
        v.nextCrossing p j = (v.crossingsAt p).head (List.ne_nil_of_mem hj)) := by
      rintro ⟨hpos, hn⟩
      rcases hother p hpos with rfl | rfl
      · exact hxa ((crossing_outgoingSlot_eq_closingHalfEdge_iff v hj hpArc).mpr
          ⟨rfl, (v.nextCrossing p).injective (by simpa using hn)⟩)
      · simp [hpCircle] at hj
    have h := edgePair_closure_cons_cons_of_mem v i ε (-ε) hj
    simp only [hc, ite_false, crossing_closure, List.length_cons] at h
    exact h.trans hm.symm

/-! #### Higher position crossing-free, lower position meeting crossings -/

private def circleArcDiagram (v : BraidWord n) (i : Fin (n - 1)) (ε : ℤˣ)
    (hp : v.crossingsAt (strand i) ≠ []) (core : OrientedPDCode v.length) :
    OrientedPDCode (v.length + 2) :=
  core.insertCircleClasp (v.closingHalfEdge (strand i) hp) true (!decide (ε = 1))

private theorem readCircleArcDiagram_edgePair {v : BraidWord n} {i : Fin (n - 1)} {ε : ℤˣ}
    (hp : v.crossingsAt (strand i) ≠ []) (hq : v.crossingsAt (strandSucc i) = [])
    {core : OrientedPDCode v.length} (hedge : core.edgePair = v.closure.edgePair) :
    (closure ((i, ε) :: (i, -ε) :: v)).edgePair =
      (readClasp (circleArcDiagram v i ε hp core)).edgePair := by
  let C := circleArcDiagram v i ε hp core
  have h0one := readClasp_edgePair_apply C
    (halfEdgeSuccEquiv (v.length + 1) (.inl (halfEdgeSuccEquiv v.length (.inr 2))))
  have h0two := readClasp_edgePair_apply C
    (halfEdgeSuccEquiv (v.length + 1) (.inl (halfEdgeSuccEquiv v.length (.inr 3))))
  have h1one := readClasp_edgePair_apply C (halfEdgeSuccEquiv (v.length + 1) (.inr 2))
  have h1two := readClasp_edgePair_apply C (halfEdgeSuccEquiv (v.length + 1) (.inr 3))
  simp only [C, circleArcDiagram, OrientedPDCode.toPDCode_insertCircleClasp,
    core.toPDCode.insertCircleClasp_edgePair_first, core.toPDCode.insertCircleClasp_edgePair_second,
    claspHalf_first, claspHalf_second, Fin.reduceSub, hedge, edgePair_closingHalfEdge,
    crossing_closure] at h0one h0two h1one h1two
  norm_num only [Matrix.cons_val, Fin.reduceSub] at h0one h0two h1one h1two
  simp only [claspHalf_first, claspHalf_second, claspHalf_old_crossing, Fin.reduceSub]
    at h0one h0two h1one h1two
  refine edgePair_closure_cons_cons_eq_of_outgoingSlot v i ε (-ε) ?_ ?_ ?_ ?_ fun hj ↦
    readInsertCircleClasp_edgePair_old hp hq (Or.inl rfl) (fun _ h ↦ h) hedge
      (by
        have hin : incomingSlot ((i, ε) :: (i, -ε) :: v) 0 (strand i) = 3 := by
          simpa using incomingSlot_strand ((i, ε) :: (i, -ε) :: v) 0
        rw [hin]; decide)
      (readClasp_edgePair_apply C) hj
  · exact (edgePair_closure_cons_cons_one v i ε (-ε)).trans h0one.symm
  · exact (edgePair_closure_cons_cons_two v i ε (-ε)).trans h0two.symm
  · exact (edgePair_closure_cons_cons_one_one_of_nil v i ε (-ε) hq).trans h1one.symm
  · exact (edgePair_closure_cons_cons_one_two_of_ne_nil v i ε (-ε) hp).trans h1two.symm

private theorem readCircleArcDiagram_eq {v : BraidWord n} {i : Fin (n - 1)} {ε : ℤˣ}
    (hp : v.crossingsAt (strand i) ≠ []) (hq : v.crossingsAt (strandSucc i) = [])
    {core : OrientedPDCode v.length} (hcore : core.adjoinCircle true = v.closure) :
    readClasp (circleArcDiagram v i ε hp core) = closure ((i, ε) :: (i, -ε) :: v) := by
  obtain ⟨hhalf, hedge, hover, hori⟩ := fields_eq_of_adjoinCircle hcore
  rw [halfEdge_closure] at hhalf
  have hc : core.crossinglessComponents =
      (closure ((i, ε) :: (i, -ε) :: v)).crossinglessComponents :=
    crossinglessComponents_eq_of_adjoinCircle hcore
      (crossinglessComponents_cons_cons_of_one_nil (Or.inl ⟨hp, hq⟩))
  refine eq_closure_cons_cons_of_fields ?_ (readCircleArcDiagram_edgePair hp hq hedge) ?_ ?_ ?_
  · exact readClasp_halfEdge (halfEdge_eq_one_of_succ
      (fun _ _ => by simp [circleArcDiagram, hhalf]) (fun _ => by simp [circleArcDiagram])
      (fun _ => by simp [circleArcDiagram]))
  · refine overPair_eq_closure_cons_cons ?_ ?_ fun j ↦ ?_
    · simp [readClasp, readClaspWith, circleArcDiagram]
    · simp [readClasp, readClaspWith, circleArcDiagram, one_ne_zero]
    · simp [readClasp, readClaspWith, circleArcDiagram, hover, Fin.ext_iff]
  · refine readClaspWith_orientation_eq_closure (fun s ↦ ?_) (fun s ↦ ?_) fun j s ↦ ?_
    · simp only [circleArcDiagram, OrientedPDCode.orientation_insertCircleClasp_first,
        hori, orientation_closingHalfEdge]
      fin_cases s <;> decide
    · simp only [circleArcDiagram, OrientedPDCode.orientation_insertCircleClasp_second,
        hori, orientation_closingHalfEdge]
      fin_cases s <;> decide
    · simp only [circleArcDiagram, OrientedPDCode.orientation_insertCircleClasp_old, hori]
  · simpa [readClasp, circleArcDiagram] using hc

/-! #### Lower position crossing-free, higher position meeting crossings -/

/-- The lower circle runs against the arc it is pushed across, so it is inserted with the
opposite direction to the one it has in the closure. -/
private def lowerCircleDiagram (v : BraidWord n) (i : Fin (n - 1)) (ε : ℤˣ)
    (hq : v.crossingsAt (strandSucc i) ≠ []) (core : OrientedPDCode v.length) :
    OrientedPDCode (v.length + 2) :=
  core.insertCircleClasp (v.closingHalfEdge (strandSucc i) hq) false (decide (ε = 1))

private theorem readLowerCircleDiagram_edgePair {v : BraidWord n} {i : Fin (n - 1)} {ε : ℤˣ}
    (hp : v.crossingsAt (strand i) = []) (hq : v.crossingsAt (strandSucc i) ≠ [])
    {core : OrientedPDCode v.length} (hedge : core.edgePair = v.closure.edgePair) :
    (closure ((i, ε) :: (i, -ε) :: v)).edgePair =
      (readLowerClasp (lowerCircleDiagram v i ε hq core)).edgePair := by
  let C := lowerCircleDiagram v i ε hq core
  have h0one := readLowerClasp_edgePair_apply C
    (halfEdgeSuccEquiv (v.length + 1) (.inl (halfEdgeSuccEquiv v.length (.inr 1))))
  have h0two := readLowerClasp_edgePair_apply C
    (halfEdgeSuccEquiv (v.length + 1) (.inl (halfEdgeSuccEquiv v.length (.inr 2))))
  have h1one := readLowerClasp_edgePair_apply C (halfEdgeSuccEquiv (v.length + 1) (.inr 3))
  have h1two := readLowerClasp_edgePair_apply C (halfEdgeSuccEquiv (v.length + 1) (.inr 0))
  simp only [C, lowerCircleDiagram, OrientedPDCode.toPDCode_insertCircleClasp,
    core.toPDCode.insertCircleClasp_edgePair_first, core.toPDCode.insertCircleClasp_edgePair_second,
    lowerClaspHalf_first, lowerClaspHalf_second, hedge, edgePair_closingHalfEdge,
    crossing_closure] at h0one h0two h1one h1two
  norm_num only [Matrix.cons_val, Fin.reduceAdd] at h0one h0two h1one h1two
  simp only [lowerClaspHalf_first, lowerClaspHalf_second, lowerClaspHalf_old_crossing,
    Fin.reduceAdd] at h0one h0two h1one h1two
  refine edgePair_closure_cons_cons_eq_of_outgoingSlot v i ε (-ε) ?_ ?_ ?_ ?_ fun hj ↦
    readInsertCircleClasp_edgePair_old hq hp (Or.inr rfl) (fun _ h ↦ h.symm) hedge
      (by simpa using (incomingSlot_strandSucc ((i, ε) :: (i, -ε) :: v) 0).symm)
      (readLowerClasp_edgePair_apply C) hj
  · exact (edgePair_closure_cons_cons_one v i ε (-ε)).trans h0one.symm
  · exact (edgePair_closure_cons_cons_two v i ε (-ε)).trans h0two.symm
  · exact (edgePair_closure_cons_cons_one_one_of_ne_nil v i ε (-ε) hq).trans h1one.symm
  · exact (edgePair_closure_cons_cons_one_two_of_nil v i ε (-ε) hp).trans h1two.symm

private theorem readLowerCircleDiagram_eq {v : BraidWord n} {i : Fin (n - 1)} {ε : ℤˣ}
    (hp : v.crossingsAt (strand i) = []) (hq : v.crossingsAt (strandSucc i) ≠ [])
    {core : OrientedPDCode v.length} (hcore : core.adjoinCircle true = v.closure) :
    readLowerClasp (lowerCircleDiagram v i ε hq core) = closure ((i, ε) :: (i, -ε) :: v) := by
  obtain ⟨hhalf, hedge, hover, hori⟩ := fields_eq_of_adjoinCircle hcore
  rw [halfEdge_closure] at hhalf
  have hc : core.crossinglessComponents =
      (closure ((i, ε) :: (i, -ε) :: v)).crossinglessComponents :=
    crossinglessComponents_eq_of_adjoinCircle hcore
      (crossinglessComponents_cons_cons_of_one_nil (Or.inr ⟨hp, hq⟩))
  refine eq_closure_cons_cons_of_fields ?_ (readLowerCircleDiagram_edgePair hp hq hedge) ?_ ?_ ?_
  · exact readLowerClasp_halfEdge (halfEdge_eq_one_of_succ
      (fun _ _ => by simp [lowerCircleDiagram, hhalf]) (fun _ => by simp [lowerCircleDiagram])
      (fun _ => by simp [lowerCircleDiagram]))
  · refine overPair_eq_closure_cons_cons ?_ ?_ fun j ↦ ?_
    · simp [readLowerClasp, readClaspWith, lowerCircleDiagram]
    · simp [readLowerClasp, readClaspWith, lowerCircleDiagram]
    · simp [readLowerClasp, readClaspWith, lowerCircleDiagram, hover, Fin.ext_iff]
  · refine readClaspWith_orientation_eq_closure (fun s ↦ ?_) (fun s ↦ ?_) fun j s ↦ ?_
    · simp only [lowerCircleDiagram, OrientedPDCode.orientation_insertCircleClasp_first,
        hori, orientation_closingHalfEdge]
      fin_cases s <;> decide
    · simp only [lowerCircleDiagram, OrientedPDCode.orientation_insertCircleClasp_second,
        hori, orientation_closingHalfEdge]
      fin_cases s <;> decide
    · simp only [lowerCircleDiagram, OrientedPDCode.orientation_insertCircleClasp_old, hori]
  · simpa [readLowerClasp, lowerCircleDiagram] using hc

end CircleArc

/-! ### Unrestricted free cancellation at the top of a braid word -/

/-- Prepending an inverse pair to a braid word preserves its oriented closure up to Reidemeister
moves, whether the two affected positions already meet crossings or are crossing-free. -/
theorem reidemeisterEquiv_closure_cons_cons_freeCancel
    (v : BraidWord n) (i : Fin (n - 1)) (ε : ℤˣ) :
    OrientedPDCode.ReidemeisterEquiv v.closure (closure ((i, ε) :: (i, -ε) :: v)) := by
  by_cases hp : v.crossingsAt (strand i) = []
  · by_cases hq : v.crossingsAt (strandSucc i) = []
    · obtain ⟨D₁, hD₁, hm₁⟩ :=
        exists_adjoinCircle_core (crossinglessComponents_cons_cons_of_two_nil (ε := ε) hp hq)
      obtain ⟨core, hcore, _⟩ := exists_adjoinCircle_core hm₁
      have htwo : (core.adjoinCircle true).adjoinCircle true = v.closure := by rw [hcore, hD₁]
      rw [← readTwoCircleDiagram_eq hp hq htwo, ← htwo]
      exact (OrientedPDCode.reidemeisterEquiv_adjoinTwoCircleClasp core true true _).trans
        (reidemeisterEquiv_readClasp _)
    · obtain ⟨core, hcore, _⟩ := exists_adjoinCircle_core
        (crossinglessComponents_cons_cons_of_one_nil (ε := ε) (Or.inr ⟨hp, hq⟩))
      rw [← readLowerCircleDiagram_eq hp hq hcore, ← hcore]
      exact (OrientedPDCode.reidemeisterEquiv_adjoinCircle_not core true).trans
        ((OrientedPDCode.reidemeisterEquiv_insertCircleClasp core
          (v.closingHalfEdge (strandSucc i) hq) false (decide (ε = 1))).trans
          (reidemeisterEquiv_readLowerClasp _))
  · by_cases hq : v.crossingsAt (strandSucc i) = []
    · obtain ⟨core, hcore, _⟩ := exists_adjoinCircle_core
        (crossinglessComponents_cons_cons_of_one_nil (ε := ε) (Or.inl ⟨hp, hq⟩))
      rw [← readCircleArcDiagram_eq hp hq hcore, ← hcore]
      exact (OrientedPDCode.reidemeisterEquiv_insertCircleClasp core
        (v.closingHalfEdge (strand i) hp) true (!decide (ε = 1))).trans
        (reidemeisterEquiv_readClasp _)
    · exact (OrientedPDCode.reidemeisterEquiv_insertClasp v.closure
        (v.closingHalfEdge (strand i) hp) (v.closingHalfEdge (strandSucc i) hq)
        (!decide (ε = 1)) (v.closingHalfEdge_ne hq hp (strand_ne_strandSucc i).symm)
        (v.closingHalfEdge_ne_edgePair_closingHalfEdge _ _ hp hq)
        (v.closingHalfEdge_clasp_face_condition i hp hq)).trans
        (reidemeisterEquiv_closure_cons_cons_freeCancel_insertClasp v i ε hp hq).symm

end TauCeti.BraidWord
