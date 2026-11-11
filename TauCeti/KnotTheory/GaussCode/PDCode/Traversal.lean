/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.GaussCode.PDCode.Components
public import TauCeti.KnotTheory.PDCode.Planar
public import TauCeti.KnotTheory.PDCode.Visit
import TauCeti.GroupTheory.Perm.OrbitCount.FinRotate
import Mathlib.Logic.Equiv.Bool

/-!
# Reading Gauss codes from oriented PD-codes

An outgoing half-edge of an oriented PD-code identifies a visit to a crossing. At each
crossing there are exactly two such visits, one over and one under. Ordering those visits
by component traversal reads the Gauss word of a diagram with one crossing-bearing component.
Crossing labels and signs are retained, rather than renumbered by first occurrence.

The construction separates the local crossing data from the cyclic order: an arbitrary
numbering of outgoing half-edges gives crossing data, and the traversal equation certifies
that the numbering follows the diagram. Converting the result back preserves arcs and the
counterclockwise order at crossings under an explicit half-edge identification, and therefore
preserves planarity. Reading the PD-code of a Gauss code in its original order recovers that
Gauss code exactly.

The component permutation is `OrientedPDCode.componentPermOutgoing`; the forward conversion
is `BasedOrientedGaussCode.toOrientedPDCode`. Explicit crossing-free circles are ignored:
a single Gauss word describes the component that meets the crossings.

## References

* M. Mastin, *Links and Planar Diagram Codes*, Definitions 2–3.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapter 1.
-/

public noncomputable section

namespace TauCeti.OrientedPDCode

variable {n : ℕ}

/-- Read the visits of a PD-code in a specified order. For a diagram traversal, the numbering
must carry cyclic rotation to `componentPermOutgoing`; see `exists_gaussTraversal`.
This construction reads all crossing-bearing components and ignores explicit crossing-free
circles. -/
def gaussCodeOfEquiv (D : OrientedPDCode n)
    (e : Fin (2 * n) ≃ {h : Fin (4 * n) // D.orientation h = true}) :
    BasedOrientedGaussCode n := by
  let v := e.trans D.outgoingHalfEdgeDataEquiv
  let p : PerfectMatching (Fin n × Bool) := PerfectMatching.mk
    (Equiv.prodCongr (Equiv.refl _) Equiv.boolNot) (by simp) (by
      rintro ⟨c, b⟩ h
      exact Bool.not_ne_self b (congrArg Prod.snd h))
  exact {
    visit := fun i => (v i).1
    over := fun i => (v i).2
    sign := fun c => if D.crossingSign c = 1 then 1 else -1
    partner := PerfectMatching.congr v.symm p
    visit_eq_iff := by
      intro i j
      rw [PerfectMatching.congr_val_apply]
      constructor
      · intro h
        by_cases ho : (v j).2 = (v i).2
        · exact .inl (v.injective (Prod.ext h.symm ho))
        · refine .inr (v.injective ?_)
          simp only [Equiv.symm_symm, Equiv.apply_symm_apply]
          apply Prod.ext
          · simpa [p] using h.symm
          · simpa [p] using Bool.eq_not_iff.mpr ho
      · rintro (rfl | rfl) <;> simp [p]
    over_partner := by simp [p] }

/-- The crossing met at a numbered visit is the crossing of its outgoing half-edge. -/
@[simp]
theorem gaussCodeOfEquiv_visit (D : OrientedPDCode n)
    (e : Fin (2 * n) ≃ {h : Fin (4 * n) // D.orientation h = true}) (i : Fin (2 * n)) :
    (D.gaussCodeOfEquiv e).visit i = (D.outgoingHalfEdgeDataEquiv (e i)).1 := (rfl)

/-- Over/under data is read at the outgoing half-edge of the visit. -/
@[simp]
theorem gaussCodeOfEquiv_over (D : OrientedPDCode n)
    (e : Fin (2 * n) ≃ {h : Fin (4 * n) // D.orientation h = true}) (i : Fin (2 * n)) :
    (D.gaussCodeOfEquiv e).over i = (D.outgoingHalfEdgeDataEquiv (e i)).2 := (rfl)

/-- Crossing signs are preserved by reading a PD-code. -/
@[simp]
theorem gaussCodeOfEquiv_sign (D : OrientedPDCode n)
    (e : Fin (2 * n) ≃ {h : Fin (4 * n) // D.orientation h = true}) (c : Fin n) :
    ((D.gaussCodeOfEquiv e).sign c : ℤ) = D.crossingSign c := by
  simp only [gaussCodeOfEquiv]
  rcases D.crossingSign_eq_one_or_neg_one c with h | h <;> simp [h]

/-- Reading a PD-code preserves its writhe. -/
@[simp]
theorem gaussCodeOfEquiv_writhe (D : OrientedPDCode n)
    (e : Fin (2 * n) ≃ {h : Fin (4 * n) // D.orientation h = true}) :
    (D.gaussCodeOfEquiv e).writhe = D.writhe := by
  simp [BasedOrientedGaussCode.writhe_def, writhe_def]

/-- A PD-code with one crossing-bearing component admits a cyclic numbering of its outgoing
visits. This is the order used to read its Gauss word. -/
theorem exists_gaussTraversal (D : OrientedPDCode n)
    (hD : D.toPDCode.crossingComponentCount = 1) :
    ∃ e : Fin (2 * n) ≃ {h : Fin (4 * n) // D.orientation h = true},
      ∀ i, e (finRotate _ i) = D.componentPermOutgoing (e i) := by
  obtain ⟨f, hf⟩ := exists_equiv_permCongr_eq_finRotate
    (D.orbitCount_componentPermOutgoing.trans hD)
  let e := (f.trans (finCongr D.card_outgoingHalfEdges)).symm
  refine ⟨e, ?_⟩
  intro i
  have hcast : ∀ {a b : ℕ} (hab : a = b) (j : Fin a),
      finCongr hab (finRotate a j) = finRotate b (finCongr hab j) := by
    intro a b hab j
    subst hab
    rfl
  have hstep (a) : f (D.componentPermOutgoing a) = finRotate _ (f a) := by
    simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using
      congrArg (fun σ => σ (f a)) hf
  apply (f.trans (finCongr D.card_outgoingHalfEdges)).injective
  rw [Equiv.apply_symm_apply]
  simp only [Equiv.trans_apply, hstep, hcast]
  have hi := (f.trans (finCongr D.card_outgoingHalfEdges)).apply_symm_apply i
  exact congrArg (finRotate _) hi.symm

/-- Extend a numbering of outgoing visits to all half-edges, matching the incoming end
with the opposite slot at the same crossing. The source labels are those of the Gauss-to-PD
conversion. -/
def gaussHalfEdgeEquiv (D : OrientedPDCode n)
    (e : Fin (2 * n) ≃ {h : Fin (4 * n) // D.orientation h = true}) :
    Fin (4 * n) ≃ Fin (4 * n) :=
  ((visitHalfEdgeEquiv n).symm.trans
    (Equiv.prodCongr (e.trans D.outgoingHalfEdgeDataEquiv) (Equiv.refl Bool))).trans
      ((Equiv.prodAssoc (Fin n) Bool Bool).trans D.halfEdgeDataEquiv.symm)

/-- The extended numbering retains the crossing, over/under and direction of each visit. -/
@[simp]
theorem halfEdgeDataEquiv_gaussHalfEdgeEquiv (D : OrientedPDCode n)
    (e : Fin (2 * n) ≃ {h : Fin (4 * n) // D.orientation h = true})
    (i : Fin (2 * n)) (b : Bool) :
    D.halfEdgeDataEquiv (D.gaussHalfEdgeEquiv e (visitHalfEdgeEquiv n (i, b))) =
      ((D.gaussCodeOfEquiv e).visit i, (D.gaussCodeOfEquiv e).over i, b) := by
  simp [gaussHalfEdgeEquiv]

/-- The outgoing endpoint of a visit is the prescribed outgoing half-edge. -/
@[simp]
theorem gaussHalfEdgeEquiv_outgoing (D : OrientedPDCode n)
    (e : Fin (2 * n) ≃ {h : Fin (4 * n) // D.orientation h = true}) (i : Fin (2 * n)) :
    D.gaussHalfEdgeEquiv e (visitHalfEdgeEquiv n (i, true)) = e i := by
  apply D.halfEdgeDataEquiv.injective
  rw [halfEdgeDataEquiv_gaussHalfEdgeEquiv]
  simp only [gaussCodeOfEquiv_visit, gaussCodeOfEquiv_over, outgoingHalfEdgeDataEquiv_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rfl
  · rfl
  · simpa using (e i).property

/-- The incoming endpoint is opposite the numbered outgoing endpoint at its crossing. -/
@[simp]
theorem gaussHalfEdgeEquiv_incoming (D : OrientedPDCode n)
    (e : Fin (2 * n) ≃ {h : Fin (4 * n) // D.orientation h = true}) (i : Fin (2 * n)) :
    D.gaussHalfEdgeEquiv e (visitHalfEdgeEquiv n (i, false)) = D.crossingTurn (e i) := by
  apply D.halfEdgeDataEquiv.injective
  rw [halfEdgeDataEquiv_gaussHalfEdgeEquiv, halfEdgeDataEquiv_crossingTurn]
  simp only [gaussCodeOfEquiv_visit, gaussCodeOfEquiv_over, outgoingHalfEdgeDataEquiv_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rfl
  · rfl
  · simpa using (e i).property

private theorem exists_gaussSlotOffset (D : OrientedPDCode n) (c : Fin n) :
    ∃ k : Fin 4, ∀ s : Fin 4,
      (D.isOver c (s + k), D.orientation (D.crossing c (s + k))) =
        (decide (s = 0 ∨ s = 2),
          if D.crossingSign c = 1 then decide (s = 2 ∨ s = 3)
            else decide (s = 1 ∨ s = 2)) := by
  refine ⟨if D.overPair c then
    (if D.orientation (D.crossing c 1) then 3 else 1)
    else (if D.orientation (D.crossing c 0) then 2 else 0), ?_⟩
  intro s
  have hdir := D.orientation_crossing_eq c
  cases h0 : D.orientation (D.crossing c 0) <;>
    cases h1 : D.orientation (D.crossing c 1) <;> cases hp : D.overPair c <;>
    simp only [h0, h1] at hdir <;> fin_cases s <;>
    simp [h0, h1, hp, hdir, PDCode.isOver_def, crossingSign_def, -PDCode.crossing_apply]

/-- At each crossing, converting the read Gauss code back to a PD-code changes only the
starting slot of the counterclockwise reading. -/
theorem exists_gaussHalfEdgeEquiv_crossing (D : OrientedPDCode n)
    (e : Fin (2 * n) ≃ {h : Fin (4 * n) // D.orientation h = true}) :
    ∃ k : Fin n → Fin 4, ∀ c s,
      D.gaussHalfEdgeEquiv e ((D.gaussCodeOfEquiv e).toOrientedPDCode.crossing c s) =
        D.crossing c (s + k c) := by
  choose k hk using D.exists_gaussSlotOffset
  refine ⟨k, fun c s => ?_⟩
  apply D.halfEdgeDataEquiv.injective
  simp only [PDCode.crossing_apply]
  rw [BasedOrientedGaussCode.toOrientedPDCode_crossing,
    halfEdgeDataEquiv_gaussHalfEdgeEquiv, halfEdgeDataEquiv_crossing]
  simp only [BasedOrientedGaussCode.visit_crossingVisit,
    BasedOrientedGaussCode.over_crossingVisit, BasedOrientedGaussCode.crossingOutgoing_def]
  have hs : (D.gaussCodeOfEquiv e).sign c = 1 ↔ D.crossingSign c = 1 := by
    rw [← D.gaussCodeOfEquiv_sign e c]
    exact Units.val_inj.symm
  simpa only [hs, PDCode.crossing_apply] using congrArg (Prod.mk c) (hk c s).symm

/-- For a cyclic traversal, the half-edge identification respects every arc of the diagram. -/
theorem gaussHalfEdgeEquiv_edgePair (D : OrientedPDCode n)
    (e : Fin (2 * n) ≃ {h : Fin (4 * n) // D.orientation h = true})
    (he : ∀ i, e (finRotate _ i) = D.componentPermOutgoing (e i)) (h : Fin (4 * n)) :
    D.gaussHalfEdgeEquiv e ((D.gaussCodeOfEquiv e).toOrientedPDCode.edgePair.val h) =
      D.edgePair.val (D.gaussHalfEdgeEquiv e h) := by
  obtain ⟨⟨i, b⟩, rfl⟩ := (visitHalfEdgeEquiv n).surjective h
  rw [BasedOrientedGaussCode.toOrientedPDCode_edgePair_visitHalfEdge]
  cases b
  · have ht := congrArg Subtype.val (he ((finRotate _).symm i))
    simp only [Equiv.apply_symm_apply, componentPermOutgoing_apply,
      PDCode.componentPerm_apply] at ht
    simp only [Bool.false_eq_true, ↓reduceIte, gaussHalfEdgeEquiv_outgoing,
      gaussHalfEdgeEquiv_incoming]
    rw [ht]
    simp
  · simp only [↓reduceIte, gaussHalfEdgeEquiv_incoming, gaussHalfEdgeEquiv_outgoing]
    rw [he]
    simp

/-- The half-edge identification preserves the counterclockwise rotation at crossings. -/
theorem gaussHalfEdgeEquiv_crossingRotation (D : OrientedPDCode n)
    (e : Fin (2 * n) ≃ {h : Fin (4 * n) // D.orientation h = true}) (h : Fin (4 * n)) :
    D.gaussHalfEdgeEquiv e ((D.gaussCodeOfEquiv e).toOrientedPDCode.crossingRotation h) =
      D.crossingRotation (D.gaussHalfEdgeEquiv e h) := by
  obtain ⟨k, hk⟩ := D.exists_gaussHalfEdgeEquiv_crossing e
  have hk' (c : Fin n) (s : Fin 4) :
      D.gaussHalfEdgeEquiv e ((D.gaussCodeOfEquiv e).toOrientedPDCode.halfEdge
        (PDCode.crossingSlotEquiv n (c, s))) =
          D.halfEdge (PDCode.crossingSlotEquiv n (c, s + k c)) := by
    simpa only [PDCode.crossing_apply] using hk c s
  obtain ⟨⟨c, s⟩, rfl⟩ := ((PDCode.crossingSlotEquiv n).trans
    (D.gaussCodeOfEquiv e).toOrientedPDCode.halfEdge).surjective h
  simp only [Equiv.trans_apply, PDCode.crossingRotation_crossing, PDCode.crossing_apply, hk']
  congr 2
  exact congrArg (Prod.mk c) (add_right_comm s 1 (k c))

/-- Reading along a component traversal preserves the embedded graph, including its cyclic
order at each vertex. -/
theorem gaussCodeOfEquiv_toPermutationTriple (D : OrientedPDCode n)
    (e : Fin (2 * n) ≃ {h : Fin (4 * n) // D.orientation h = true})
    (he : ∀ i, e (finRotate _ i) = D.componentPermOutgoing (e i)) :
    D.gaussHalfEdgeEquiv e • (D.gaussCodeOfEquiv e).toOrientedPDCode.toPermutationTriple =
      D.toPermutationTriple := by
  apply PermutationTriple.ext_of_two
  · simp only [PermutationTriple.smul_σ0, PDCode.toPermutationTriple_σ0]
    apply Equiv.ext
    intro h
    obtain ⟨h, rfl⟩ := (D.gaussHalfEdgeEquiv e).surjective h
    simpa only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply] using
      D.gaussHalfEdgeEquiv_crossingRotation e h
  · simp only [PermutationTriple.smul_σ1, PDCode.toPermutationTriple_σ1]
    apply Equiv.ext
    intro h
    obtain ⟨h, rfl⟩ := (D.gaussHalfEdgeEquiv e).surjective h
    simpa only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply] using
      D.gaussHalfEdgeEquiv_edgePair e he h

/-- The Gauss word read by a cyclic traversal is planar exactly when the original PD-code is
planar. Thus the reverse conversion retains planar realizability, rather than merely the
abstract pairing of visits. -/
theorem gaussCodeOfEquiv_isPlanar_iff (D : OrientedPDCode n)
    (e : Fin (2 * n) ≃ {h : Fin (4 * n) // D.orientation h = true})
    (he : ∀ i, e (finRotate _ i) = D.componentPermOutgoing (e i)) :
    (D.gaussCodeOfEquiv e).toOrientedPDCode.toPDCode.IsPlanar ↔ D.toPDCode.IsPlanar := by
  rw [PDCode.isPlanar_def, PDCode.isPlanar_def,
    ← D.gaussCodeOfEquiv_toPermutationTriple e he]
  simp

end TauCeti.OrientedPDCode

namespace TauCeti.BasedOrientedGaussCode

variable {n : ℕ}

/-- Half-edge data of a converted Gauss code recovers the visit label, over/under status
and direction that labelled the endpoint. -/
@[simp]
theorem halfEdgeDataEquiv_toOrientedPDCode (G : BasedOrientedGaussCode n)
    (i : Fin (2 * n)) (b : Bool) :
    G.toOrientedPDCode.halfEdgeDataEquiv (visitHalfEdgeEquiv n (i, b)) =
      (G.visit i, G.over i, b) := by
  obtain ⟨⟨c, s⟩, hh⟩ := ((PDCode.crossingSlotEquiv n).trans
    G.toOrientedPDCode.halfEdge).surjective (visitHalfEdgeEquiv n (i, b))
  have hcross : G.toOrientedPDCode.crossing c s = visitHalfEdgeEquiv n (i, b) := by
    simpa only [PDCode.crossing_apply, Equiv.trans_apply] using hh
  have hdata := (visitHalfEdgeEquiv n).injective
    ((G.toOrientedPDCode_crossing c s).symm.trans (by
      simpa only [PDCode.crossing_apply] using hcross))
  have hi : G.crossingVisit c s = i := congrArg Prod.fst hdata
  have hb : G.crossingOutgoing c s = b := congrArg Prod.snd hdata
  rw [← hcross, PDCode.crossing_apply, OrientedPDCode.halfEdgeDataEquiv_crossing]
  simp only [toOrientedPDCode_isOver_crossing, toOrientedPDCode_crossing,
    toOrientedPDCode_orientation_halfEdge, hb, ← hi, visit_crossingVisit, over_crossingVisit]

/-- Reading the PD-code of a Gauss code along its original visits recovers that code exactly. -/
@[simp]
theorem gaussCodeOfEquiv_toOrientedPDCode (G : BasedOrientedGaussCode n) :
    G.toOrientedPDCode.gaussCodeOfEquiv G.outgoingHalfEdgeEquiv = G := by
  apply BasedOrientedGaussCode.ext
  · funext i
    simp
  · funext i
    simp
  · funext c
    apply Units.ext
    simp only [OrientedPDCode.gaussCodeOfEquiv_sign, toOrientedPDCode_crossingSign]

end TauCeti.BasedOrientedGaussCode
