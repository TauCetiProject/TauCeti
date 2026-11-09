/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Oriented.Component
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Circle.Basic

/-!
# Component transport for an isolated first Reidemeister move

`OrientedPDCode.adjoinKinkComponentEquiv` identifies the labelled components of
`D.adjoinCircle o` with those of `D.adjoinKink o b`. It sends the last crossing-free label
to the component of the new crossing, preserves the old crossing-free labels, and carries
each old outgoing half-edge to its inclusion. This remains valid for the empty surrounding
diagram and for either orientation and either crossing sign.

The label convention matters: the added circle has label `Fin.last`, even if other circles
have the same orientation. The transport is a bijection of actual traversal classes, not
merely an equality of component counts. Its inverse collapses the new crossing-bearing
component back to that particular label. These bijections allow a marked component to be
retained across a first Reidemeister move on a crossing-free circle.

The native isolated-kink construction follows W. B. R. Lickorish, *An Introduction to Knot
Theory*, Chapter 1.
-/

public section

noncomputable section

namespace TauCeti.OrientedPDCode

open PDCode Equiv Equiv.Perm

variable {n : ℕ} (D : OrientedPDCode n) (o b : Bool)

private def collapseKinkRepresentative :
    (x : Fin (4 * n) ⊕ Fin 4) →
      (D.adjoinKink o b).orientation (halfEdgeSuccEquiv n x) = true →
        (D.adjoinCircle o).Component
  | .inl x, hx => (D.adjoinCircle o).componentOfOutgoing ⟨x, by simpa using hx⟩
  | .inr _, _ => .inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount))

private def collapseKinkOutgoing
    (x : {x // (D.adjoinKink o b).orientation x = true}) :
    (D.adjoinCircle o).Component :=
  collapseKinkRepresentative D o b ((halfEdgeSuccEquiv n).symm x.val)
    (by simpa using x.property)

private theorem collapseKinkOutgoing_inl
    (x : {x // D.orientation x = true}) :
    collapseKinkOutgoing D o b
        ⟨halfEdgeSuccEquiv n (.inl x.val), by simp [x.property]⟩ =
      (D.adjoinCircle o).componentOfOutgoing ⟨x.val, by simpa using x.property⟩ := by
  unfold collapseKinkOutgoing
  -- Abstract the dependent orientation proof so the inverse-equivalence law can rewrite its index.
  generalize_proofs hp
  revert hp
  simp only [Equiv.symm_apply_apply]
  intros
  rfl

private theorem collapseKinkOutgoing_inr (s : Fin 4)
    (hs : (D.adjoinKink o b).orientation (halfEdgeSuccEquiv n (.inr s)) = true) :
    collapseKinkOutgoing D o b ⟨halfEdgeSuccEquiv n (.inr s), hs⟩ =
      Sum.inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount)) := by
  unfold collapseKinkOutgoing
  -- As above, rewriting the index requires abstracting its dependent orientation proof.
  generalize_proofs hp
  revert hp
  simp only [Equiv.symm_apply_apply]
  intros
  rfl

private theorem collapseKinkOutgoing_traversal
    (x : {x // (D.adjoinKink o b).orientation x = true}) :
    collapseKinkOutgoing D o b ((D.adjoinKink o b).componentPermOutgoing x) =
      collapseKinkOutgoing D o b x := by
  obtain ⟨y, hy⟩ := (halfEdgeSuccEquiv n).surjective x.val
  rcases y with y | s
  · have ho : D.orientation y = true := by simpa [← hy] using x.property
    have hx : x = ⟨halfEdgeSuccEquiv n (.inl y), by simp [ho]⟩ := Subtype.ext hy.symm
    subst x
    have ht : (D.adjoinKink o b).componentPermOutgoing
        ⟨halfEdgeSuccEquiv n (.inl y), by simp [ho]⟩ =
        ⟨halfEdgeSuccEquiv n (.inl (D.toPDCode.componentPerm y)),
          by simp [ho]⟩ := by
      apply Subtype.ext
      simp [componentPerm_adjoinKink, Equiv.permCongr_apply]
    rw [ht]
    rw [collapseKinkOutgoing_inl D o b ⟨D.toPDCode.componentPerm y, by simp [ho]⟩,
      collapseKinkOutgoing_inl D o b ⟨y, ho⟩]
    have hval : (⟨D.toPDCode.componentPerm y, by simp [ho]⟩ :
        {h // (D.adjoinCircle o).orientation h = true}) =
        (D.adjoinCircle o).componentPermOutgoing ⟨y, by simpa using ho⟩ := by
      apply Subtype.ext
      simp
    rw [hval]
    exact (D.adjoinCircle o).componentOfOutgoing_componentPermOutgoing _
  · have hs : (D.adjoinKink o b).orientation (halfEdgeSuccEquiv n (.inr s)) = true :=
      hy ▸ x.property
    have hx : x = ⟨halfEdgeSuccEquiv n (.inr s), hs⟩ := Subtype.ext hy.symm
    subst x
    have ht : (D.adjoinKink o b).componentPermOutgoing
        ⟨halfEdgeSuccEquiv n (.inr s), hs⟩ =
        ⟨halfEdgeSuccEquiv n (.inr ((oppositeCrossingSlot * slotSmoothing true) s)),
          by simpa [componentPerm_adjoinKink, Equiv.permCongr_apply] using
            ((D.adjoinKink o b).orientation_componentPerm
              (halfEdgeSuccEquiv n (.inr s))).trans hs⟩ := by
      apply Subtype.ext
      simp [componentPerm_adjoinKink, Equiv.permCongr_apply]
    rw [ht, collapseKinkOutgoing_inr, collapseKinkOutgoing_inr]

private def collapseKinkComponent : (D.adjoinKink o b).Component →
    (D.adjoinCircle o).Component :=
  Sum.elim (Quotient.lift (collapseKinkOutgoing D o b)
    (fun _ _ h => h.apply_eq_of_apply_eq (collapseKinkOutgoing_traversal D o b)))
    (fun i => .inr (Fin.cast (by simp) i.castSucc))

private theorem collapseKinkComponent_old
    (x : {x // D.orientation x = true}) :
    collapseKinkComponent D o b
        ((D.adjoinKink o b).componentOfOutgoing
          ⟨halfEdgeSuccEquiv n (.inl x.val), by simp [x.property]⟩) =
      (D.adjoinCircle o).componentOfOutgoing ⟨x.val, by simpa using x.property⟩ := by
  rw [componentOfOutgoing_def]
  exact collapseKinkOutgoing_inl D o b x

private theorem collapseKinkComponent_new (s : Fin 4)
    (hs : (D.adjoinKink o b).orientation (halfEdgeSuccEquiv n (.inr s)) = true) :
    collapseKinkComponent D o b
        ((D.adjoinKink o b).componentOfOutgoing
          ⟨halfEdgeSuccEquiv n (.inr s), hs⟩) =
      Sum.inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount)) := by
  rw [componentOfOutgoing_def]
  exact collapseKinkOutgoing_inr D o b s hs

private theorem collapseKinkComponent_surjective :
    Function.Surjective (collapseKinkComponent D o b) := by
  intro c
  rcases (D.adjoinCircle o).component_cases c with ⟨x, rfl⟩ | ⟨i, rfl⟩
  · exact ⟨_, collapseKinkComponent_old D o b ⟨x.val, by simpa using x.property⟩⟩
  · obtain ⟨i, rfl⟩ := (finCongr (by simp :
        D.crossinglessComponentCount + 1 =
          (D.adjoinCircle o).crossinglessComponentCount)).surjective i
    induction i using Fin.lastCases with
    | last =>
      have hs : (D.adjoinKink o b).orientation
          (halfEdgeSuccEquiv n (.inr (if o then 1 else 0))) = true := by
        cases o <;> simp
      exact ⟨_, collapseKinkComponent_new D o b _ hs⟩
    | cast i => exact ⟨Sum.inr (Fin.cast (by simp) i), by
        simp only [collapseKinkComponent, Sum.elim_inr, Sum.inr.injEq]
        apply Fin.ext
        rfl⟩

/-- Transport labelled components across the isolated first Reidemeister move. The circle
with the last crossing-free label becomes the component passing through the new crossing;
all old components retain their representatives or labels. -/
def adjoinKinkComponentEquiv :
    (D.adjoinCircle o).Component ≃ (D.adjoinKink o b).Component :=
  (Equiv.ofBijective (collapseKinkComponent D o b)
    ((Nat.bijective_iff_surjective_and_card _).mpr
      ⟨collapseKinkComponent_surjective D o b, by
        simp only [card_component, toPDCode_adjoinKink, toPDCode_adjoinCircle,
          componentCount_adjoinKink]⟩)).symm

/-- Old outgoing representatives are carried by the native half-edge inclusion. -/
@[simp] theorem adjoinKinkComponentEquiv_componentOfOutgoing
    (x : {x // D.orientation x = true}) :
    D.adjoinKinkComponentEquiv o b
        ((D.adjoinCircle o).componentOfOutgoing ⟨x.val, by simpa using x.property⟩) =
      (D.adjoinKink o b).componentOfOutgoing
        ⟨halfEdgeSuccEquiv n (.inl x.val), by simp [x.property]⟩ := by
  apply (D.adjoinKinkComponentEquiv o b).symm.injective
  exact (Equiv.symm_apply_apply _ _).trans (collapseKinkComponent_old D o b x).symm

/-- The added-circle label goes to the new crossing's component, represented by slot `1`
when `o = true` and slot `0` otherwise. These slots are always outgoing. -/
@[simp] theorem adjoinKinkComponentEquiv_last :
    D.adjoinKinkComponentEquiv o b
        (Sum.inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount))) =
      (D.adjoinKink o b).componentOfOutgoing
        ⟨halfEdgeSuccEquiv n (.inr (if o then 1 else 0)), by cases o <;> simp⟩ := by
  apply (D.adjoinKinkComponentEquiv o b).symm.injective
  exact (Equiv.symm_apply_apply _ _).trans (collapseKinkComponent_new D o b _ _).symm

/-- All old crossing-free labels are preserved, even when their orientations repeat. -/
@[simp] theorem adjoinKinkComponentEquiv_inr_castSucc (i : Fin D.crossinglessComponentCount) :
    D.adjoinKinkComponentEquiv o b (Sum.inr (Fin.cast (by simp) i.castSucc)) =
      Sum.inr (Fin.cast (by simp) i) := by
  apply (D.adjoinKinkComponentEquiv o b).symm.injective
  exact Equiv.symm_apply_apply _ _

/-- Removing the isolated kink sends every old outgoing representative back to itself. -/
@[simp] theorem adjoinKinkComponentEquiv_symm_componentOfOutgoing
    (x : {x // D.orientation x = true}) :
    (D.adjoinKinkComponentEquiv o b).symm
        ((D.adjoinKink o b).componentOfOutgoing
          ⟨halfEdgeSuccEquiv n (.inl x.val), by simp [x.property]⟩) =
      (D.adjoinCircle o).componentOfOutgoing ⟨x.val, by simpa using x.property⟩ :=
  collapseKinkComponent_old D o b x

/-- Removing the isolated kink restores the particular crossing-free label that was consumed. -/
@[simp] theorem adjoinKinkComponentEquiv_symm_new (s : Fin 4)
    (hs : (D.adjoinKink o b).orientation (halfEdgeSuccEquiv n (.inr s)) = true) :
    (D.adjoinKinkComponentEquiv o b).symm
        ((D.adjoinKink o b).componentOfOutgoing ⟨halfEdgeSuccEquiv n (.inr s), hs⟩) =
      Sum.inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount)) :=
  collapseKinkComponent_new D o b s hs

/-- Removing the isolated kink preserves every other crossing-free circle. -/
@[simp] theorem adjoinKinkComponentEquiv_symm_inr (i : Fin D.crossinglessComponentCount) :
    (D.adjoinKinkComponentEquiv o b).symm (Sum.inr (Fin.cast (by simp) i)) =
      Sum.inr (Fin.cast (by simp) i.castSucc) := by
  simp only [adjoinKinkComponentEquiv, Equiv.symm_symm, Equiv.ofBijective_apply,
    collapseKinkComponent, Sum.elim_inr, Sum.inr.injEq]
  apply Fin.ext
  rfl

end TauCeti.OrientedPDCode
