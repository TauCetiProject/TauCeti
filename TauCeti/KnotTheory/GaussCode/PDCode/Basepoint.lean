/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.GaussCode.PDCode.Basic
public import TauCeti.KnotTheory.GaussCode.Unbased
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Equivalence

/-!
# The PD-code of a Gauss code does not depend on the base point

The oriented PD-code `TauCeti.BasedOrientedGaussCode.toOrientedPDCode D` of a based oriented Gauss
code `D` names the incoming and outgoing ends of the `i`-th visit of the traversal by the half-edges
`2 * i` and `2 * i + 1` (`TauCeti.visitHalfEdgeEquiv`). The base point enters only through this
numbering. Moving it forward by one visit (`TauCeti.BasedOrientedGaussCode.rotateBasepoint`) turns
visit `i + 1` into visit `i`, so the PD-code of the rotated code is the PD-code of `D` with its
half-edges renumbered by `TauCeti.visitHalfEdgeRotate n`, which sends each end of visit `i` to the
same end of visit `i - 1`, cyclically. The crossings keep their labels
(`TauCeti.BasedOrientedGaussCode.toOrientedPDCode_rotateBasepoint`).

So two based codes representing the same unbased oriented Gauss code
(`TauCeti.OrientedGaussCode`) have PD-codes that differ only by a relabelling of half-edges
(`TauCeti.BasedOrientedGaussCode.exists_toOrientedPDCode_eq_relabel_of_forgetBasepoint_eq`), and
relabelling the crossings as well, codes that agree up to relabelling as unbased codes have
Reidemeister equivalent PD-codes
(`TauCeti.BasedOrientedGaussCode.reidemeisterEquiv_toOrientedPDCode_of_forgetBasepoint_eq_relabel`).
This is the form in which a diagram read off by traversing a knot from some point, such as the
diagram of a regular projection of a polygonal knot, defines a PD-code up to Reidemeister
equivalence independently of where the traversal starts.

## Main definitions

* `TauCeti.visitHalfEdgeRotate n`: the renumbering of the half-edges of `2 * n` visits that moves
  each visit back by one.

## Main results

* `TauCeti.BasedOrientedGaussCode.toOrientedPDCode_rotateBasepoint`: moving the base point
  relabels the half-edges of the PD-code by `TauCeti.visitHalfEdgeRotate n`.
* `TauCeti.BasedOrientedGaussCode.exists_toOrientedPDCode_eq_relabel_of_forgetBasepoint_eq`: based
  codes with the same unbased code have PD-codes differing by a relabelling of half-edges.
* `TauCeti.BasedOrientedGaussCode.reidemeisterEquiv_toOrientedPDCode_of_forgetBasepoint_eq_relabel`:
  based codes whose unbased codes agree up to relabelling crossings have Reidemeister equivalent
  PD-codes.

## References

* M. Mastin, *Links and Planar Diagram Codes*, Definitions 2–3, for PD-codes and their
  relabellings.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1, for
  Gauss codes of knot diagrams.
-/

public section

namespace TauCeti

/-- The renumbering of the half-edges of `2 * n` visits that moves every visit back by one,
cyclically: the incoming or outgoing end of visit `i` becomes the same end of visit `i - 1`. This
is how the half-edge labels of `TauCeti.BasedOrientedGaussCode.toOrientedPDCode` change when the
base point moves forward by one visit. -/
def visitHalfEdgeRotate (n : ℕ) : Equiv.Perm (Fin (4 * n)) :=
  (visitHalfEdgeEquiv n).permCongr (Equiv.prodCongr (finRotate (2 * n)).symm (Equiv.refl Bool))

/-- `TauCeti.visitHalfEdgeRotate n` moves each end of visit `i` to the same end of the previous
visit. -/
@[simp]
theorem visitHalfEdgeRotate_visitHalfEdgeEquiv (n : ℕ) (i : Fin (2 * n)) (outgoing : Bool) :
    visitHalfEdgeRotate n (visitHalfEdgeEquiv n (i, outgoing)) =
      visitHalfEdgeEquiv n ((finRotate (2 * n)).symm i, outgoing) := by
  simp [visitHalfEdgeRotate, Equiv.permCongr_apply]

/-- The inverse of `TauCeti.visitHalfEdgeRotate n` moves each end of visit `i` to the same end of
the next visit. -/
@[simp]
theorem visitHalfEdgeRotate_symm_visitHalfEdgeEquiv (n : ℕ) (i : Fin (2 * n)) (outgoing : Bool) :
    (visitHalfEdgeRotate n).symm (visitHalfEdgeEquiv n (i, outgoing)) =
      visitHalfEdgeEquiv n (finRotate (2 * n) i, outgoing) := by
  rw [Equiv.symm_apply_eq, visitHalfEdgeRotate_visitHalfEdgeEquiv, Equiv.symm_apply_apply]

namespace BasedOrientedGaussCode

variable {n m : ℕ}

/-- After moving the base point forward, the visit in a crossing slot is the previous visit of the
original traversal. -/
@[simp]
theorem crossingVisit_rotateBasepoint (D : BasedOrientedGaussCode n) (c : Fin n) (slot : Fin 4) :
    (rotateBasepoint n D).crossingVisit c slot =
      (finRotate (2 * n)).symm (D.crossingVisit c slot) := by
  apply (rotateBasepoint n D).visitDataEquiv.injective
  -- First evaluate the left side, before `visit_rotateBasepoint` can unfold the rotated code there.
  simp only [visitDataEquiv_apply, visit_crossingVisit, over_crossingVisit]
  simp only [visit_rotateBasepoint, over_rotateBasepoint, Equiv.apply_symm_apply,
    visit_crossingVisit, over_crossingVisit]

/-- Moving the base point does not change the incoming/outgoing direction of a crossing slot. -/
@[simp]
theorem crossingOutgoing_rotateBasepoint (D : BasedOrientedGaussCode n) (c : Fin n)
    (slot : Fin 4) :
    (rotateBasepoint n D).crossingOutgoing c slot = D.crossingOutgoing c slot := by
  simp [crossingOutgoing_def]

/-- **Moving the base point relabels the half-edges.** The PD-code of a Gauss code with its base
point moved forward by one visit is the PD-code of the original code with every half-edge moved
back by one visit (`TauCeti.visitHalfEdgeRotate`), and the same crossing labels. -/
@[simp]
theorem toOrientedPDCode_rotateBasepoint (D : BasedOrientedGaussCode n) :
    (rotateBasepoint n D).toOrientedPDCode =
      D.toOrientedPDCode.relabel (visitHalfEdgeRotate n) (Equiv.refl (Fin n)) := by
  apply OrientedPDCode.ext
  · apply PDCode.ext
    · refine Equiv.ext fun h => ?_
      rw [← (PDCode.crossingSlotEquiv n).apply_symm_apply h]
      rcases (PDCode.crossingSlotEquiv n).symm h with ⟨c, slot⟩
      rw [toOrientedPDCode_crossing, OrientedPDCode.relabel_toPDCode, PDCode.relabel_halfEdge]
      simp only [Equiv.equivCongr_apply_apply, PDCode.crossingBlockEquiv_symm,
        PDCode.crossingBlockEquiv_apply_crossingSlotEquiv, Equiv.refl_symm, Equiv.refl_apply,
        toOrientedPDCode_crossing, crossingVisit_rotateBasepoint,
        crossingOutgoing_rotateBasepoint, visitHalfEdgeRotate_visitHalfEdgeEquiv]
    · refine Subtype.ext <| Equiv.ext fun h => ?_
      rw [← (visitHalfEdgeEquiv n).apply_symm_apply h]
      rcases (visitHalfEdgeEquiv n).symm h with ⟨i, outgoing⟩
      rw [OrientedPDCode.relabel_toPDCode, PDCode.relabel_edgePair,
        PerfectMatching.congr_val_apply, visitHalfEdgeRotate_symm_visitHalfEdgeEquiv]
      cases outgoing <;>
        simp only [toOrientedPDCode_edgePair_visitHalfEdge, Bool.false_eq_true, ↓reduceIte,
          visitHalfEdgeRotate_visitHalfEdgeEquiv, Equiv.symm_apply_apply]
    · simp
    · funext c
      simp
  · funext h
    rw [← (visitHalfEdgeEquiv n).apply_symm_apply h]
    rcases (visitHalfEdgeEquiv n).symm h with ⟨i, outgoing⟩
    simp
  · simp

/-- Moving the base point backward by one visit relabels the half-edges of the PD-code by the
inverse of `TauCeti.visitHalfEdgeRotate n`, keeping the crossing labels. -/
@[simp]
theorem toOrientedPDCode_rotateBasepoint_symm (D : BasedOrientedGaussCode n) :
    ((rotateBasepoint n).symm D).toOrientedPDCode =
      D.toOrientedPDCode.relabel (visitHalfEdgeRotate n).symm (Equiv.refl (Fin n)) := by
  conv_rhs => rw [← (rotateBasepoint n).apply_symm_apply D, toOrientedPDCode_rotateBasepoint]
  simp

/-- Moving the base point forward or backward any number of times relabels the half-edges of the
PD-code, keeping the crossing labels. -/
theorem exists_toOrientedPDCode_rotateBasepoint_zpow_eq_relabel (D : BasedOrientedGaussCode n)
    (k : ℤ) : ∃ half : Equiv.Perm (Fin (4 * n)),
      ((rotateBasepoint n ^ k) D).toOrientedPDCode =
        D.toOrientedPDCode.relabel half (Equiv.refl (Fin n)) := by
  induction k using Int.induction_on with
  | zero => exact ⟨Equiv.refl _, by simp⟩
  | succ k ih =>
    obtain ⟨half, h⟩ := ih
    refine ⟨half.trans (visitHalfEdgeRotate n), ?_⟩
    rw [add_comm, zpow_one_add, Equiv.Perm.mul_apply, toOrientedPDCode_rotateBasepoint, h,
      OrientedPDCode.relabel_relabel, Equiv.refl_trans]
  | pred k ih =>
    obtain ⟨half, h⟩ := ih
    refine ⟨half.trans (visitHalfEdgeRotate n).symm, ?_⟩
    rw [sub_eq_neg_add, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply, Equiv.Perm.inv_def,
      toOrientedPDCode_rotateBasepoint_symm, h, OrientedPDCode.relabel_relabel, Equiv.refl_trans]

/-- **The PD-code of an unbased Gauss code is defined up to relabelling half-edges.** Based codes
representing the same unbased oriented Gauss code have PD-codes that differ by a relabelling of
their half-edges, with the same crossing labels. -/
theorem exists_toOrientedPDCode_eq_relabel_of_forgetBasepoint_eq {D E : BasedOrientedGaussCode n}
    (h : D.forgetBasepoint = E.forgetBasepoint) : ∃ half : Equiv.Perm (Fin (4 * n)),
      E.toOrientedPDCode = D.toOrientedPDCode.relabel half (Equiv.refl (Fin n)) := by
  obtain ⟨k, rfl⟩ := forgetBasepoint_eq_iff.1 h
  exact exists_toOrientedPDCode_rotateBasepoint_zpow_eq_relabel D k

/-- Equal Gauss codes, paired with their numbers of crossings, have Reidemeister equivalent
PD-codes. This compares codes whose numbers of crossings are equal but computed differently, as for
the Gauss codes of a polygonal knot before and after an elementary move. -/
theorem reidemeisterEquiv_toOrientedPDCode_of_sigma_eq {D : BasedOrientedGaussCode n}
    {E : BasedOrientedGaussCode m} (h : (⟨n, D⟩ : Σ k, BasedOrientedGaussCode k) = ⟨m, E⟩) :
    OrientedPDCode.ReidemeisterEquiv D.toOrientedPDCode E.toOrientedPDCode := by
  cases h
  rfl

/-- Relabelling the crossings of a Gauss code gives a Reidemeister equivalent PD-code. -/
theorem reidemeisterEquiv_toOrientedPDCode_relabel (D : BasedOrientedGaussCode n)
    (e : Equiv.Perm (Fin n)) :
    OrientedPDCode.ReidemeisterEquiv (D.relabel e).toOrientedPDCode D.toOrientedPDCode := by
  rw [toOrientedPDCode_relabel]
  exact (OrientedPDCode.reidemeisterEquiv_relabel _ _ _).symm

/-- Based codes representing the same unbased oriented Gauss code have Reidemeister equivalent
PD-codes. -/
theorem reidemeisterEquiv_toOrientedPDCode_of_forgetBasepoint_eq {D E : BasedOrientedGaussCode n}
    (h : D.forgetBasepoint = E.forgetBasepoint) :
    OrientedPDCode.ReidemeisterEquiv D.toOrientedPDCode E.toOrientedPDCode := by
  obtain ⟨half, hE⟩ := exists_toOrientedPDCode_eq_relabel_of_forgetBasepoint_eq h
  rw [hE]
  exact OrientedPDCode.reidemeisterEquiv_relabel _ _ _

/-- **The PD-code of an unbased Gauss code is defined up to Reidemeister equivalence.** If the
unbased code of `D` is that of `E` with its crossings relabelled, then `D` and `E` have
Reidemeister equivalent PD-codes. -/
theorem reidemeisterEquiv_toOrientedPDCode_of_forgetBasepoint_eq_relabel
    {D E : BasedOrientedGaussCode n} {e : Equiv.Perm (Fin n)}
    (h : D.forgetBasepoint = E.forgetBasepoint.relabel e) :
    OrientedPDCode.ReidemeisterEquiv D.toOrientedPDCode E.toOrientedPDCode := by
  rw [OrientedGaussCode.relabel_forgetBasepoint] at h
  exact (reidemeisterEquiv_toOrientedPDCode_of_forgetBasepoint_eq h).trans
    (reidemeisterEquiv_toOrientedPDCode_relabel E e)

end BasedOrientedGaussCode

end TauCeti
