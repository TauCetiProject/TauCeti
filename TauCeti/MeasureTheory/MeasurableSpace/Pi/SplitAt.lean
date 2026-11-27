/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Splitting a measurable product at a coordinate

The measurable equivalence `MeasurableEquiv.piSplitAt` separates one coordinate of a
dependent product from its remaining coordinates.
-/

public section

noncomputable section

namespace MeasurableEquiv

/-- Separate a coordinate of a dependent product from the remaining coordinates, as a
measurable equivalence. -/
def piSplitAt {ι : Type*} [DecidableEq ι] (i : ι) (α : ι → Type*)
    [∀ j, MeasurableSpace (α j)] : (∀ j, α j) ≃ᵐ α i × (∀ j : {j // j ≠ i}, α j) :=
  letI : Unique {j : ι // j = i} := ⟨⟨⟨i, rfl⟩⟩, fun j ↦ Subtype.ext j.property⟩
  (piEquivPiSubtypeProd α (· = i)).trans
    ((piUnique fun j : {j : ι // j = i} ↦ α j).prodCongr (.refl _))

/-- Splitting a dependent product reads off the chosen coordinate and restricts the others. -/
@[simp] theorem piSplitAt_apply {ι : Type*} [DecidableEq ι]
    {α : ι → Type*} [∀ j, MeasurableSpace (α j)] (i : ι) (x : ∀ j, α j) :
    MeasurableEquiv.piSplitAt i α x = (x i, fun j : {j // j ≠ i} ↦ x j) := (rfl)

/-- The underlying equivalence of the measurable coordinate split is `Equiv.piSplitAt`. -/
@[simp] theorem piSplitAt_toEquiv {ι : Type*} [DecidableEq ι] (i : ι) (α : ι → Type*)
    [∀ j, MeasurableSpace (α j)] : (piSplitAt i α).toEquiv = Equiv.piSplitAt i α := by
  apply Equiv.ext
  intro x
  rw [coe_toEquiv, piSplitAt_apply, Equiv.piSplitAt_apply]

/-- Reconstructing an assignment from its split recovers the chosen coordinate. -/
@[simp] theorem piSplitAt_symm_apply_self {ι : Type*} [DecidableEq ι]
    {α : ι → Type*} [∀ j, MeasurableSpace (α j)] (i : ι)
    (p : α i × (∀ j : {j // j ≠ i}, α j)) :
    (MeasurableEquiv.piSplitAt i α).symm p i = p.1 := by
  simpa only [piSplitAt_apply] using congrArg Prod.fst ((piSplitAt i α).apply_symm_apply p)

/-- Reconstructing an assignment from its split recovers each remaining coordinate. -/
@[simp] theorem piSplitAt_symm_apply_ne {ι : Type*} [DecidableEq ι]
    {α : ι → Type*} [∀ j, MeasurableSpace (α j)] (i : ι)
    (p : α i × (∀ j : {j // j ≠ i}, α j)) (j : ι) (hj : j ≠ i) :
    (MeasurableEquiv.piSplitAt i α).symm p j = p.2 ⟨j, hj⟩ := by
  simpa only [piSplitAt_apply] using
    congrFun (congrArg Prod.snd ((piSplitAt i α).apply_symm_apply p)) ⟨j, hj⟩

end MeasurableEquiv
