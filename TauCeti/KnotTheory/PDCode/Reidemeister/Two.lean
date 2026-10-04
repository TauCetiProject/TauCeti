/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Circle
public import TauCeti.KnotTheory.PDCode.Planar
import TauCeti.GroupTheory.Perm.SumCongr
import TauCeti.GroupTheory.Perm.OrbitCount.FinRotate
import TauCeti.Data.Fin.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The second Reidemeister move between a circle and an arc

`PDCode.insertCircleClasp D p b` pushes a new crossing-free circle across the arc ending
at `p`, creating a cancelling pair of crossings. It is compared with `D.adjoinCircle`:
the circle becomes a crossing-bearing component, and the other components retain their
strands. Unlike clasp insertion between two existing arcs, there is no common-face
hypothesis: the new circle can be placed beside the chosen arc.

The new crossings have opposite over-pair indicators, so the same physical strand is
over at both crossings. The two internal clasp arcs join slots `2` to `1` and `3` to `0`;
the outside arc of the circle joins slot `1` of the first crossing to slot `2` of the
second. The remaining ports attach to the cut arc. This is the circle-and-arc case;
clasp insertion between two crossing-free circles is a separate case.

The clasp has the same component count and Kauffman bracket as `D.adjoinCircle`, and
is planar exactly when `D` is planar. These results allow this local second Reidemeister
move within planar PD codes while preserving component count and the bracket; together
with the oriented move's writhe preservation, they give Jones polynomial invariance
for the circle-and-arc case.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, GTM 175 (1997), Chapter 1 and
  Chapter 3, Lemma 3.3 (the second Reidemeister move).
* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395–407.
-/

public section

namespace TauCeti.PDCode

open Equiv Equiv.Perm TemperleyLieb

variable {n : ℕ}

private abbrev Slots := Fin 4 ⊕ Fin 4

/-- The four arcs of the closed local clasp before its first port is cut open. -/
private def circleArcs : PerfectMatching Slots :=
  PerfectMatching.mk
    ((Equiv.sumCongr Fin.revPerm Fin.revPerm).trans (Equiv.sumComm _ _))
    (by decide) (by decide)

private def circleHalfEdges (n : ℕ) : Fin (4 * n) ⊕ Slots ≃ Fin (4 * (n + 2)) :=
  (Equiv.sumAssoc _ _ _).symm.trans
    ((Equiv.sumCongr (halfEdgeSuccEquiv n) (Equiv.refl _)).trans
      (halfEdgeSuccEquiv (n + 1)))

private def circleMatching (D : PDCode n) (p : Fin (4 * n)) :
    PerfectMatching (Fin (4 * n) ⊕ Slots) :=
  PerfectMatching.congr (swap (.inl (D.edgePair.val p)) (.inr (.inl 0)))
    (PerfectMatching.mk (Perm.sumCongr D.edgePair.val circleArcs.val)
      (by rintro (x | x) <;> simp [D.edgePair.apply_apply, circleArcs.apply_apply])
      (by rintro (x | x) <;> simp [D.edgePair.apply_ne, circleArcs.apply_ne]))

/-- Push a new circle across an existing arc, creating a two-crossing Reidemeister clasp.
The circle is additional to the components of `D`; the result is compared to `D.adjoinCircle`.
The bit `b` selects the over-strand at the first new crossing. -/
def insertCircleClasp (D : PDCode n) (p : Fin (4 * n)) (b : Bool) : PDCode (n + 2) where
  halfEdge := (circleHalfEdges n).permCongr (Perm.sumCongr D.halfEdge 1)
  edgePair := PerfectMatching.congr (circleHalfEdges n) (circleMatching D p)
  crossinglessComponentCount := D.crossinglessComponentCount
  overPair := Fin.snoc (Fin.snoc D.overPair b) (!b)

variable (D : PDCode n) (p : Fin (4 * n)) (b : Bool)

/-- The old crossing slots retain their half-edges. -/
@[simp] theorem insertCircleClasp_crossing_castSucc_castSucc (i : Fin n) (s : Fin 4) :
    (D.insertCircleClasp p b).halfEdge
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n
          (.inl (crossingSlotEquiv n (i, s)))))) =
      halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl (D.crossing i s)))) := by
  simp [insertCircleClasp, circleHalfEdges, Equiv.permCongr_apply]

/-- The first new crossing uses the first four new half-edges. -/
@[simp] theorem insertCircleClasp_crossing_castSucc_last (s : Fin 4) :
    (D.insertCircleClasp p b).halfEdge
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr s)))) =
      halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr s))) := by
  simp [insertCircleClasp, circleHalfEdges, Equiv.permCongr_apply]

/-- The second new crossing uses the last four half-edges. -/
@[simp] theorem insertCircleClasp_crossing_last (s : Fin 4) :
    (D.insertCircleClasp p b).halfEdge (halfEdgeSuccEquiv (n + 1) (.inr s)) =
      halfEdgeSuccEquiv (n + 1) (.inr s) := by
  simp [insertCircleClasp, circleHalfEdges, Equiv.permCongr_apply]

@[simp] theorem insertCircleClasp_overPair_castSucc_castSucc (i : Fin n) :
    (D.insertCircleClasp p b).overPair i.castSucc.castSucc = D.overPair i := by
  simp [insertCircleClasp]

@[simp] theorem insertCircleClasp_overPair_castSucc_last :
    (D.insertCircleClasp p b).overPair (Fin.last n).castSucc = b := by
  simp [insertCircleClasp]

@[simp] theorem insertCircleClasp_overPair_last :
    (D.insertCircleClasp p b).overPair (Fin.last (n + 1)) = !b := by
  simp [insertCircleClasp]

@[simp] theorem insertCircleClasp_crossinglessComponentCount :
    (D.insertCircleClasp p b).crossinglessComponentCount = D.crossinglessComponentCount := (rfl)

private theorem edgePair_circleHalfEdges (x : Fin (4 * n) ⊕ Slots) :
    (D.insertCircleClasp p b).edgePair.val (circleHalfEdges n x) =
      circleHalfEdges n ((circleMatching D p).val x) := by
  simp [insertCircleClasp, PerfectMatching.congr_val]

private theorem edgePair_circleClasp : (D.insertCircleClasp p b).edgePair.val =
    (circleHalfEdges n).permCongr (circleMatching D p).val := by
  simp [insertCircleClasp, PerfectMatching.congr_val]

private theorem circleMatching_old_self : (circleMatching D p).val (.inl p) = .inr (.inl 0) := by
  simp [circleMatching, PerfectMatching.congr_val, swap_apply_def, (D.edgePair.apply_ne p).symm]

private theorem circleMatching_old_partner :
    (circleMatching D p).val (.inl (D.edgePair.val p)) = .inr (.inr 3) := by
  simp [circleMatching, PerfectMatching.congr_val, swap_apply_def, circleArcs]

private theorem circleMatching_old {x : Fin (4 * n)} (hx : x ≠ p)
    (hx' : x ≠ D.edgePair.val p) :
    (circleMatching D p).val (.inl x) = .inl (D.edgePair.val x) := by
  have hxe : D.edgePair.val x ≠ D.edgePair.val p := D.edgePair.val.injective.ne hx
  simp [circleMatching, PerfectMatching.congr_val, swap_apply_def, hx', hxe]

private theorem circleMatching_first (s : Fin 4) :
    (circleMatching D p).val (.inr (.inl s)) =
      ![.inl p, .inr (.inr 2), .inr (.inr 1), .inr (.inr 0)] s := by
  fin_cases s <;> simp [circleMatching, PerfectMatching.congr_val, circleArcs,
    swap_apply_def, D.edgePair.apply_apply p, (D.edgePair.apply_ne p).symm]

private theorem circleMatching_second (s : Fin 4) :
    (circleMatching D p).val (.inr (.inr s)) =
      ![.inr (.inl 3), .inr (.inl 2), .inr (.inl 1), .inl (D.edgePair.val p)] s := by
  fin_cases s <;> simp [circleMatching, PerfectMatching.congr_val, circleArcs, swap_apply_def]

/-- The arc ending at `p` enters the first crossing at slot `0`. -/
@[simp] theorem insertCircleClasp_edgePair_old_self :
    (D.insertCircleClasp p b).edgePair.val
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl p)))) =
      halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 0))) := by
  simpa [circleHalfEdges] using edgePair_circleHalfEdges D p b (.inl p) |>.trans
    (congrArg (circleHalfEdges n) (circleMatching_old_self D p))

/-- The other end of the cut arc attaches to slot `3` of the second crossing. -/
@[simp] theorem insertCircleClasp_edgePair_old_partner :
    (D.insertCircleClasp p b).edgePair.val
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl (D.edgePair.val p))))) =
      halfEdgeSuccEquiv (n + 1) (.inr 3) := by
  simpa [circleHalfEdges] using edgePair_circleHalfEdges D p b (.inl (D.edgePair.val p)) |>.trans
    (congrArg (circleHalfEdges n) (circleMatching_old_partner D p))

/-- Every half-edge off the cut arc keeps its old partner. -/
@[simp] theorem insertCircleClasp_edgePair_old {x : Fin (4 * n)} (hx : x ≠ p)
    (hx' : x ≠ D.edgePair.val p) :
    (D.insertCircleClasp p b).edgePair.val
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x)))) =
      halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl (D.edgePair.val x)))) := by
  simpa [circleHalfEdges] using edgePair_circleHalfEdges D p b (.inl x) |>.trans
    (congrArg (circleHalfEdges n) (circleMatching_old D p hx hx'))

/-- Partners of the first crossing's slots: the chosen arc, the outside circle arc, and the
 two internal clasp arcs. -/
@[simp] theorem insertCircleClasp_edgePair_first (s : Fin 4) :
    (D.insertCircleClasp p b).edgePair.val
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr s)))) =
      ![halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl p))),
        halfEdgeSuccEquiv (n + 1) (.inr 2),
        halfEdgeSuccEquiv (n + 1) (.inr 1),
        halfEdgeSuccEquiv (n + 1) (.inr 0)] s := by
  have h := edgePair_circleHalfEdges D p b (.inr (.inl s))
  rw [circleMatching_first] at h
  fin_cases s <;> simpa [circleHalfEdges] using h

/-- Partners of the second crossing's slots. -/
@[simp] theorem insertCircleClasp_edgePair_second (s : Fin 4) :
    (D.insertCircleClasp p b).edgePair.val
        (halfEdgeSuccEquiv (n + 1) (.inr s)) =
      ![halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 3))),
        halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 2))),
        halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 1))),
        halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl (D.edgePair.val p))))] s := by
  have h := edgePair_circleHalfEdges D p b (.inr (.inr s))
  rw [circleMatching_second] at h
  fin_cases s <;> simpa [circleHalfEdges] using h

/-- Mirroring the circle clasp reverses the over-strand at both new crossings. -/
@[simp] theorem mirror_insertCircleClasp :
    (D.insertCircleClasp p b).mirror = D.mirror.insertCircleClasp p (!b) := by
  apply PDCode.ext
  · simp [insertCircleClasp]
  · simp [insertCircleClasp, circleMatching]
  · simp
  · funext i
    induction i using Fin.lastCases with
    | last => simp
    | cast i => induction i using Fin.lastCases <;> simp

/-! ### Traversals and the four smoothings -/

-- Following `PDCode.insertClasp`, attach local traversal cycles to the original arc
-- by two transpositions.
private theorem circleTraversal (T : Perm (Fin (4 * n))) (r : Perm Slots) :
    Perm.sumCongr T r * (circleMatching D p).val =
      Perm.sumCongr (T * D.edgePair.val) (r * circleArcs.val) *
        swap (.inl p) (.inr (.inr 3)) * swap (.inl (D.edgePair.val p)) (.inr (.inl 0)) := by
  ext x
  rcases x with x | (s | s)
  · by_cases hx : x = p
    · subst x
      simp [circleMatching_old_self, swap_apply_def, circleArcs, (D.edgePair.apply_ne p).symm]
    by_cases hx' : x = D.edgePair.val p
    · subst x
      simp [circleMatching_old_partner, swap_apply_def, circleArcs]
    simp [circleMatching_old D p hx hx', swap_apply_def, hx, hx']
  · rw [Perm.mul_apply, circleMatching_first]
    fin_cases s <;> simp [circleArcs, swap_apply_def, D.edgePair.apply_apply p]
  · rw [Perm.mul_apply, circleMatching_second]
    fin_cases s <;> simp [circleArcs, swap_apply_def]

private theorem orbitCount_circleTraversal (T : Perm (Fin (4 * n))) (r : Perm Slots)
    (hr : ¬ (r * circleArcs.val).SameCycle (.inr 3) (.inl 0)) :
    orbitCount (Perm.sumCongr T r * (circleMatching D p).val) + 2 =
      orbitCount (T * D.edgePair.val) + orbitCount (r * circleArcs.val) := by
  rw [circleTraversal]
  exact orbitCount_sumCongr_mul_swap_mul_swap_add_two _ _ _ _ hr

private theorem crossingwise_circleClasp (old : Perm (Fin (4 * n)))
    (new : Perm (Fin (4 * (n + 2)))) (slots : Fin (n + 2) → Perm (Fin 4))
    (hold : ∀ i s, old (D.crossing i s) = D.crossing i (slots i.castSucc.castSucc s))
    (hnew : ∀ i s, new ((D.insertCircleClasp p b).crossing i s) =
      (D.insertCircleClasp p b).crossing i (slots i s)) :
    new = (circleHalfEdges n).permCongr
      (Perm.sumCongr old (Perm.sumCongr (slots (Fin.last n).castSucc)
        (slots (Fin.last (n + 1))))) := by
  apply Equiv.ext
  intro x
  obtain ⟨x, rfl⟩ := (circleHalfEdges n).surjective x
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rcases x with x | (s | s)
  · obtain ⟨x, rfl⟩ := D.halfEdge.surjective x
    obtain ⟨⟨i, s⟩, rfl⟩ := (crossingSlotEquiv n).surjective x
    simp only [Perm.sumCongr_apply, Sum.map_inl, ← crossing_apply, hold]
    simpa only [crossing_apply, crossingSlotEquiv_succ_castSucc,
      insertCircleClasp_crossing_castSucc_castSucc, circleHalfEdges,
      Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.sumAssoc_symm_apply_inl,
      Sum.map_inl] using hnew i.castSucc.castSucc s
  · simpa only [crossing_apply, crossingSlotEquiv_succ_castSucc, crossingSlotEquiv_succ_last,
      insertCircleClasp_crossing_castSucc_last, circleHalfEdges,
      Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.sumAssoc_symm_apply_inr_inl,
      Sum.map_inl, Sum.map_inr, Equiv.refl_apply, Perm.sumCongr_apply] using
        hnew (Fin.last n).castSucc s
  · simpa only [crossing_apply, crossingSlotEquiv_succ_last,
      insertCircleClasp_crossing_last, circleHalfEdges,
      Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.sumAssoc_symm_apply_inr_inr,
      Sum.map_inl, Sum.map_inr, Equiv.refl_apply, Perm.sumCongr_apply] using
        hnew (Fin.last (n + 1)) s

private theorem smoothingTurn_circleClasp (s : Fin (n + 2) → Bool) :
    (D.insertCircleClasp p b).smoothingTurn ((D.insertCircleClasp p b).smoothingChoice s) =
      (circleHalfEdges n).permCongr (Perm.sumCongr
        (D.smoothingTurn (D.smoothingChoice (Fin.init (Fin.init s))))
        (Perm.sumCongr (slotSmoothing (s (Fin.last n).castSucc == b))
          (slotSmoothing (s (Fin.last (n + 1)) == !b)))) := by
  have h := crossingwise_circleClasp D p b
    (D.smoothingTurn (D.smoothingChoice (Fin.init (Fin.init s))))
    ((D.insertCircleClasp p b).smoothingTurn ((D.insertCircleClasp p b).smoothingChoice s))
    (fun i => slotSmoothing ((D.insertCircleClasp p b).smoothingChoice s i))
    (fun i t => by
      cases hs : s i.castSucc.castSucc <;> simp [smoothingTurn_crossing, Fin.init, hs])
    (fun i t => by simpa only [crossing_apply] using
      (D.insertCircleClasp p b).smoothingTurn_crossing _ i t)
  have h₁ : (D.insertCircleClasp p b).smoothingChoice s (Fin.last n).castSucc =
      (s (Fin.last n).castSucc == b) := by
    cases hs : s (Fin.last n).castSucc <;> cases b <;> simp [hs]
  have h₂ : (D.insertCircleClasp p b).smoothingChoice s (Fin.last (n + 1)) =
      (s (Fin.last (n + 1)) == !b) := by
    cases hs : s (Fin.last (n + 1)) <;> cases b <;> simp [hs]
  rwa [h₁, h₂] at h

private def mixedSmoothingRelabel : Perm Slots where
  toFun := Sum.elim
    (fun i => ![.inl 0, .inr 2, .inl 2, .inr 0] i)
    (fun i => ![.inl 1, .inr 3, .inl 3, .inr 1] i)
  invFun := Sum.elim
    (fun i => ![.inl 0, .inr 0, .inl 2, .inr 2] i)
    (fun i => ![.inl 3, .inr 3, .inl 1, .inr 1] i)
  left_inv := by decide
  right_inv := by decide

private theorem localSmoothingOrbitCount (u v : Bool) : orbitCount
    (Perm.sumCongr (slotSmoothing u) (slotSmoothing v) * circleArcs.val) =
      if u = v then 4 else 2 := by
  have hsame (u : Bool) : IsPerfectMatching
      (Perm.sumCongr (slotSmoothing u) (slotSmoothing u) * circleArcs.val) := by
    cases u <;> simp only [circleArcs, PerfectMatching.val_mk,
      slotSmoothing_true, slotSmoothing_false, isPerfectMatching_iff] <;> decide
  have hft : Perm.sumCongr (slotSmoothing false) (slotSmoothing true) * circleArcs.val =
      mixedSmoothingRelabel.permCongr (Perm.sumCongr (finRotate 4) (finRotate 4)) := by
    simp only [circleArcs, PerfectMatching.val_mk, slotSmoothing_false, slotSmoothing_true,
      mixedSmoothingRelabel]
    decide
  have htf : Perm.sumCongr (slotSmoothing true) (slotSmoothing false) * circleArcs.val =
      (Perm.sumCongr (slotSmoothing false) (slotSmoothing true) * circleArcs.val)⁻¹ := by
    simp only [circleArcs, PerfectMatching.val_mk, slotSmoothing_false, slotSmoothing_true]
    decide
  cases u <;> cases v
  · have h := (hsame false).two_mul_orbitCount
    simp only [Nat.card_sum, Nat.card_fin] at h
    simp only [↓reduceIte]; omega
  · rw [hft, orbitCount_permCongr, Perm.orbitCount_sumCongr]
    simp [orbitCount_finRotate]
  · rw [htf, orbitCount_inv, hft, orbitCount_permCongr, Perm.orbitCount_sumCongr]
    simp [orbitCount_finRotate]
  · have h := (hsame true).two_mul_orbitCount
    simp only [Nat.card_sum, Nat.card_fin] at h
    simp only [↓reduceIte]; omega

/-- The four smoothings leave the original state circles, plus one circle exactly when
both local slot smoothings agree. The statement uses the actual `A`/`B` state choices. -/
@[simp] theorem stateLoopCount_insertCircleClasp (s : Fin (n + 2) → Bool) :
    (D.insertCircleClasp p b).stateLoopCount s =
      D.stateLoopCount (Fin.init (Fin.init s)) +
        if s (Fin.last n).castSucc ≠ s (Fin.last (n + 1)) then 1 else 0 := by
  rw [stateLoopCount_def, statePerm_def, smoothingTurn_circleClasp]
  rw [edgePair_circleClasp, ← Equiv.permCongr_mul, Equiv.orbitCount_permCongr,
    insertCircleClasp_crossinglessComponentCount]
  have hr (u v : Bool) : ¬ (Perm.sumCongr (slotSmoothing u) (slotSmoothing v) *
      circleArcs.val).SameCycle (.inr 3) (.inl 0) := by
    cases u <;> cases v <;>
      simp only [circleArcs, PerfectMatching.val_mk, slotSmoothing_true, slotSmoothing_false] <;>
      decide
  have h := orbitCount_circleTraversal D p
    (D.smoothingTurn (D.smoothingChoice (Fin.init (Fin.init s))))
    (Perm.sumCongr (slotSmoothing (s (Fin.last n).castSucc == b))
      (slotSmoothing (s (Fin.last (n + 1)) == !b))) (hr _ _)
  rw [localSmoothingOrbitCount] at h
  rw [stateLoopCount_def, statePerm_def]
  cases b <;> cases h₁ : s (Fin.last n).castSucc <;>
    cases h₂ : s (Fin.last (n + 1)) <;> simp_all only [Bool.not_true, Bool.not_false,
      Bool.true_beq, Bool.false_beq, Bool.not_true, Bool.not_false, ↓reduceIte,
      ne_eq, Bool.true_eq_false, Bool.false_eq_true, not_false_eq_true, not_true_eq_false] <;> omega

/-- The circle-and-arc second Reidemeister move preserves the Kauffman bracket. -/
@[simp] theorem kauffmanBracket_insertCircleClasp {R : Type*} [CommRing R] (a : Rˣ) :
    (D.insertCircleClasp p b).kauffmanBracket a = D.adjoinCircle.kauffmanBracket a := by
  -- Sum the four local smoothings and apply the Kauffman bracket's loop relation.
  have hn : n ≠ 0 := by rintro rfl; exact p.elim0
  rw [kauffmanBracket_def, kauffmanBracket_def,
    ← ((Equiv.prodCongr (Equiv.refl Bool) (Fin.snocEquiv fun _ => Bool)).trans
      (Fin.snocEquiv fun _ => Bool)).sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  obtain ⟨k, hk⟩ : ∃ k, D.stateLoopCount s = k + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (D.one_le_stateLoopCount hn s)).symm⟩
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.refl_apply, Prod.map_apply,
    Fin.snocEquiv, Equiv.coe_fn_mk, stateLoopCount_insertCircleClasp, Fin.init_snoc,
    Fin.snoc_castSucc, Fin.snoc_last, stateWeight_snoc, stateLoopCount_adjoinCircle, hk]
  simp only [Bool.true_eq_false, Bool.false_eq_true, ne_eq, not_false_eq_true,
    not_true_eq_false, ↓reduceIte, add_zero, Nat.add_sub_cancel, Units.val_mul,
    Bool.cond_true, Bool.cond_false, pow_succ, jonesDelta_def]
  linear_combination (2 * (stateWeight s a : R) *
    (-((a : R) ^ 2 + ((a⁻¹ : Rˣ) : R) ^ 2)) ^ (k + 1)) * a.mul_inv

/-! ### Components and planarity -/

private theorem crossingTurn_circleClasp : (D.insertCircleClasp p b).crossingTurn =
    (circleHalfEdges n).permCongr (Perm.sumCongr D.crossingTurn
      (Perm.sumCongr oppositeCrossingSlot oppositeCrossingSlot)) := by
  apply crossingwise_circleClasp D p b _ _ (fun _ => oppositeCrossingSlot)
  · intro i t; simpa only [crossing_apply] using D.crossingTurn_crossing i t
  · intro i t
    simpa only [crossing_apply] using (D.insertCircleClasp p b).crossingTurn_crossing i t

private theorem crossingRotation_circleClasp : (D.insertCircleClasp p b).crossingRotation =
    (circleHalfEdges n).permCongr (Perm.sumCongr D.crossingRotation
      (Perm.sumCongr (finRotate 4) (finRotate 4))) := by
  apply crossingwise_circleClasp D p b _ _ (fun _ => finRotate 4)
  · intro i t; simpa only [crossing_apply, finRotate_apply] using D.crossingRotation_crossing i t
  · intro i t
    simpa only [crossing_apply, finRotate_apply] using
      (D.insertCircleClasp p b).crossingRotation_crossing i t

private theorem orbitCount_circleTraversal_opposite :
    orbitCount (Perm.sumCongr D.crossingTurn
      (Perm.sumCongr oppositeCrossingSlot oppositeCrossingSlot) * (circleMatching D p).val) =
        orbitCount D.componentPerm + 2 := by
  have hm : IsPerfectMatching
      (Perm.sumCongr oppositeCrossingSlot oppositeCrossingSlot * circleArcs.val) := by
    simp only [isPerfectMatching_iff, circleArcs, PerfectMatching.val_mk,
      oppositeCrossingSlot_eq_swap_mul_swap]
    decide
  have hc := hm.two_mul_orbitCount
  simp only [Nat.card_sum, Nat.card_fin] at hc
  have h := orbitCount_circleTraversal D p D.crossingTurn
    (Perm.sumCongr oppositeCrossingSlot oppositeCrossingSlot) (by
      simp only [circleArcs, PerfectMatching.val_mk, oppositeCrossingSlot_eq_swap_mul_swap]
      decide)
  rw [← componentPerm_def] at h
  omega

/-- The newly inserted circle is a crossing-bearing component. -/
@[simp] theorem crossingComponentCount_insertCircleClasp :
    (D.insertCircleClasp p b).crossingComponentCount = D.crossingComponentCount + 1 := by
  rw [crossingComponentCount_def, componentPerm_def, crossingTurn_circleClasp]
  rw [edgePair_circleClasp, ← Equiv.permCongr_mul, orbitCount_permCongr,
    orbitCount_circleTraversal_opposite,
    crossingComponentCount_def]
  omega

/-- The circle-and-arc move preserves the component count of `D.adjoinCircle`. -/
@[simp] theorem componentCount_insertCircleClasp :
    (D.insertCircleClasp p b).componentCount = D.adjoinCircle.componentCount := by
  simp [componentCount_eq, Nat.add_right_comm, Nat.add_assoc]

/-- The two new crossings add two graph faces. -/
@[simp] theorem faceCount_insertCircleClasp :
    (D.insertCircleClasp p b).faceCount = D.faceCount + 2 := by
  rw [faceCount_eq_orbitCount_crossingRotation_mul_edgePair, crossingRotation_circleClasp]
  rw [edgePair_circleClasp, ← Equiv.permCongr_mul, orbitCount_permCongr]
  have hm : IsPerfectMatching
      (Perm.sumCongr (finRotate 4) (finRotate 4) * circleArcs.val) := by
    simp only [isPerfectMatching_iff, circleArcs, PerfectMatching.val_mk]
    decide
  have hc := hm.two_mul_orbitCount
  simp only [Nat.card_sum, Nat.card_fin] at hc
  have h := orbitCount_circleTraversal D p D.crossingRotation
    (Perm.sumCongr (finRotate 4) (finRotate 4)) (by
      simp only [circleArcs, PerfectMatching.val_mk]; decide)
  rw [← faceCount_eq_orbitCount_crossingRotation_mul_edgePair] at h
  omega

private def newGraphOrbit (x : Fin (4 * n) ⊕ Slots) :
    (D.insertCircleClasp p b).toPermutationTriple.MonodromyOrbit :=
  Quotient.mk _ (circleHalfEdges n x)

private theorem newGraphOrbit_rotation (x : Fin (4 * n) ⊕ Slots) :
    newGraphOrbit D p b (Perm.sumCongr D.crossingRotation
      (Perm.sumCongr (finRotate 4) (finRotate 4)) x) = newGraphOrbit D p b x := by
  unfold newGraphOrbit
  have hr := (D.insertCircleClasp p b).toPermutationTriple.mk_σ0_apply (circleHalfEdges n x)
  simpa only [toPermutationTriple_σ0, crossingRotation_circleClasp, Equiv.permCongr_apply,
    Equiv.symm_apply_apply] using hr

private theorem newGraphOrbit_matching (x : Fin (4 * n) ⊕ Slots) :
    newGraphOrbit D p b ((circleMatching D p).val x) = newGraphOrbit D p b x := by
  unfold newGraphOrbit
  rw [← edgePair_circleHalfEdges, ← toPermutationTriple_σ1]
  exact (D.insertCircleClasp p b).toPermutationTriple.mk_σ1_apply _

private theorem newGraphOrbit_slots (t : Slots) :
    newGraphOrbit D p b (.inr t) = newGraphOrbit D p b (.inl p) := by
  have hu : ∀ s, newGraphOrbit D p b (.inr (.inl s)) = newGraphOrbit D p b (.inr (.inl 0)) := by
    apply apply_eq_apply_zero_of_add_one
    intro i
    simpa only [Perm.sumCongr_apply, Sum.map_inr, Sum.map_inl, finRotate_apply] using
      newGraphOrbit_rotation D p b (.inr (.inl i))
  have hv : ∀ s, newGraphOrbit D p b (.inr (.inr s)) = newGraphOrbit D p b (.inr (.inr 0)) := by
    apply apply_eq_apply_zero_of_add_one
    intro i
    simpa only [Perm.sumCongr_apply, Sum.map_inr, finRotate_apply] using
      newGraphOrbit_rotation D p b (.inr (.inr i))
  have hp := newGraphOrbit_matching D p b (.inl p)
  rw [circleMatching_old_self] at hp
  have hbridge := newGraphOrbit_matching D p b (.inr (.inl 3))
  rw [circleMatching_first] at hbridge
  rcases t with s | s
  · exact (hu s).trans hp
  · exact (hv s).trans (hbridge.trans ((hu 3).trans hp))

private theorem newGraphOrbit_old_edge (x : Fin (4 * n)) :
    newGraphOrbit D p b (.inl (D.edgePair.val x)) = newGraphOrbit D p b (.inl x) := by
  have he := newGraphOrbit_matching D p b (.inl (D.edgePair.val p))
  rw [circleMatching_old_partner, newGraphOrbit_slots] at he
  by_cases hx : x = p
  · subst x; exact he.symm
  by_cases hx' : x = D.edgePair.val p
  · subst x; simpa only [D.edgePair.apply_apply] using he
  simpa only [circleMatching_old D p hx hx'] using newGraphOrbit_matching D p b (.inl x)

private def oldGraphOrbit : Fin (4 * n) ⊕ Slots → D.toPermutationTriple.MonodromyOrbit :=
  Sum.elim (Quotient.mk _) (fun _ => Quotient.mk _ p)

/-- Graph components correspond by retaining every old half-edge; both new crossings
belong to the component containing the chosen arc. -/
def insertCircleClaspMonodromyOrbitEquiv : D.toPermutationTriple.MonodromyOrbit ≃
    (D.insertCircleClasp p b).toPermutationTriple.MonodromyOrbit where
  -- The old rotation and edge pairing both preserve the new graph orbit.
  toFun := Quotient.lift (fun x => newGraphOrbit D p b (.inl x)) (by
    rintro _ x ⟨⟨σ, hσ⟩, rfl⟩
    apply D.toPermutationTriple.apply_eq_of_mem_monodromyGroup
      (f := fun x => newGraphOrbit D p b (.inl x))
      (fun y => ?_) (fun y => ?_) hσ x
    · simpa only [toPermutationTriple_σ0, Perm.sumCongr_apply, Sum.map_inl] using
        newGraphOrbit_rotation D p b (.inl y)
    · simpa only [toPermutationTriple_σ1] using newGraphOrbit_old_edge D p b y)
  -- Collapse the new crossings to the chosen arc, respecting both graph generators.
  invFun := Quotient.lift (fun x => oldGraphOrbit D p ((circleHalfEdges n).symm x)) (by
    rintro _ x ⟨⟨σ, hσ⟩, rfl⟩
    apply (D.insertCircleClasp p b).toPermutationTriple.apply_eq_of_mem_monodromyGroup
      (f := fun x => oldGraphOrbit D p ((circleHalfEdges n).symm x))
      (fun y => ?_) (fun y => ?_) hσ x
    · obtain ⟨y, rfl⟩ := (circleHalfEdges n).surjective y
      rw [toPermutationTriple_σ0, crossingRotation_circleClasp, Equiv.permCongr_apply,
        Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      rcases y with y | (s | s)
      · simpa only [oldGraphOrbit, Perm.sumCongr_apply, Sum.map_inl, Sum.elim_inl,
          toPermutationTriple_σ0] using D.toPermutationTriple.mk_σ0_apply y
      · rfl
      · rfl
    · obtain ⟨y, rfl⟩ := (circleHalfEdges n).surjective y
      rw [toPermutationTriple_σ1, edgePair_circleHalfEdges,
        Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      have hep : (Quotient.mk _ (D.edgePair.val p) : D.toPermutationTriple.MonodromyOrbit) =
          Quotient.mk _ p := by
        simpa only [toPermutationTriple_σ1] using D.toPermutationTriple.mk_σ1_apply p
      rcases y with y | (s | s)
      · by_cases hy : y = p
        · subst y; rw [circleMatching_old_self]; rfl
        by_cases hy' : y = D.edgePair.val p
        · subst y; rw [circleMatching_old_partner]; exact hep.symm
        rw [circleMatching_old D p hy hy']
        simpa only [oldGraphOrbit, Sum.elim_inl, toPermutationTriple_σ1] using
          D.toPermutationTriple.mk_σ1_apply y
      · rw [circleMatching_first]; fin_cases s <;> rfl
      · rw [circleMatching_second]; fin_cases s <;> first | rfl | exact hep)
  left_inv := Quotient.ind (fun x => by simp [newGraphOrbit, oldGraphOrbit])
  right_inv := Quotient.ind (fun x => by
    obtain ⟨y, rfl⟩ := (circleHalfEdges n).surjective x
    simp only [Quotient.lift_mk, Equiv.symm_apply_apply]
    rcases y with y | s
    · rfl
    · exact (newGraphOrbit_slots D p b s).symm)

/-- The graph-component correspondence retains old representatives. -/
@[simp] theorem insertCircleClaspMonodromyOrbitEquiv_apply (x : Fin (4 * n)) :
    insertCircleClaspMonodromyOrbitEquiv D p b (Quotient.mk _ x) =
      Quotient.mk _ (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x)))) := (rfl)

/-- The inverse graph-component correspondence retains old representatives. -/
@[simp] theorem insertCircleClaspMonodromyOrbitEquiv_symm_apply (x : Fin (4 * n)) :
    (insertCircleClaspMonodromyOrbitEquiv D p b).symm
        (Quotient.mk _ (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x))))) =
      Quotient.mk _ x := by
  simp [insertCircleClaspMonodromyOrbitEquiv, oldGraphOrbit, circleHalfEdges]

/-- Every slot of the first new crossing maps back to the chosen arc's graph component. -/
@[simp] theorem insertCircleClaspMonodromyOrbitEquiv_symm_first (s : Fin 4) :
    (insertCircleClaspMonodromyOrbitEquiv D p b).symm
        (Quotient.mk _ (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr s))))) =
      Quotient.mk _ p := by
  simp [insertCircleClaspMonodromyOrbitEquiv, oldGraphOrbit, circleHalfEdges]

/-- Every slot of the second new crossing maps back to the chosen arc's graph component. -/
@[simp] theorem insertCircleClaspMonodromyOrbitEquiv_symm_second (s : Fin 4) :
    (insertCircleClaspMonodromyOrbitEquiv D p b).symm
        (Quotient.mk _ (halfEdgeSuccEquiv (n + 1) (.inr s))) =
      Quotient.mk _ p := by
  simp [insertCircleClaspMonodromyOrbitEquiv, oldGraphOrbit, circleHalfEdges]

/-- The circle-and-arc clasp preserves planarity. -/
@[simp] theorem isPlanar_insertCircleClasp_iff :
    (D.insertCircleClasp p b).IsPlanar ↔ D.IsPlanar := by
  have hc := Nat.card_congr (insertCircleClaspMonodromyOrbitEquiv D p b)
  rw [isPlanar_iff_faceCount_eq, isPlanar_iff_faceCount_eq, faceCount_insertCircleClasp, ← hc]
  omega

end TauCeti.PDCode
