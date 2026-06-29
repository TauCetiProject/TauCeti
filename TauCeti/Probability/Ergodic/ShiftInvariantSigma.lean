module

public import TauCeti.Probability.Exchangeability.PathSpace.Shift
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants

/-!
# Shift-invariant σ-algebra on one-sided path space

This file records the Layer 2 Exchangeability roadmap API for the σ-algebra of measurable
events on path space that are invariant under the one-sided shift.  The construction is the
shift-specialized form of Mathlib's `MeasurableSpace.invariants`; the lemmas here are only
adapters for Tau Ceti's path-space shift notation.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {α β : Type*} [MeasurableSpace α]

/-- A path-space event is shift-invariant if its preimage under the one-sided shift is itself. -/
def IsShiftInvariant (s : Set (ℕ → α)) : Prop :=
  shift α ⁻¹' s = s

/-- The σ-algebra of measurable shift-invariant events on one-sided path space. -/
@[expose, implicit_reducible]
def shiftInvariantSigma (α : Type*) [MeasurableSpace α] : MeasurableSpace (ℕ → α) :=
  MeasurableSpace.invariants (shift α)

/-- A set is measurable for `shiftInvariantSigma` iff it is ambient-measurable and invariant
under the one-sided shift. -/
theorem measurableSet_shiftInvariantSigma_iff {s : Set (ℕ → α)} :
    MeasurableSet[shiftInvariantSigma α] s ↔ MeasurableSet s ∧ IsShiftInvariant s :=
  MeasurableSpace.measurableSet_invariants

/-- The shift-invariant σ-algebra is a sub-σ-algebra of the ambient path-space σ-algebra. -/
theorem shiftInvariantSigma_le :
    shiftInvariantSigma α ≤ (inferInstance : MeasurableSpace (ℕ → α)) :=
  MeasurableSpace.invariants_le (shift α)

/-- A `shiftInvariantSigma`-measurable set is ambient-measurable. -/
theorem MeasurableSet.ambient_of_shiftInvariantSigma {s : Set (ℕ → α)}
    (hs : MeasurableSet[shiftInvariantSigma α] s) : MeasurableSet s :=
  shiftInvariantSigma_le s hs

/-- A `shiftInvariantSigma`-measurable set is invariant under the one-sided shift. -/
theorem MeasurableSet.isShiftInvariant_of_shiftInvariantSigma {s : Set (ℕ → α)}
    (hs : MeasurableSet[shiftInvariantSigma α] s) : IsShiftInvariant s :=
  (measurableSet_shiftInvariantSigma_iff.mp hs).2

/-- An ambient-measurable shift-invariant set is measurable for `shiftInvariantSigma`. -/
theorem IsShiftInvariant.measurableSet_shiftInvariantSigma {s : Set (ℕ → α)}
    (hs : IsShiftInvariant s) (hsm : MeasurableSet s) :
    MeasurableSet[shiftInvariantSigma α] s :=
  measurableSet_shiftInvariantSigma_iff.mpr ⟨hsm, hs⟩

omit [MeasurableSpace α] in
/-- A shift-invariant set is invariant under every iterate of the one-sided shift. -/
theorem IsShiftInvariant.iterate {s : Set (ℕ → α)} (hs : IsShiftInvariant s) (n : ℕ) :
    (shift α)^[n] ⁻¹' s = s := by
  induction n with
  | zero =>
      simp
  | succ n ihn =>
      calc
        (shift α)^[n + 1] ⁻¹' s = (shift α) ⁻¹' ((shift α)^[n] ⁻¹' s) := by
          ext x
          simp
        _ = (shift α) ⁻¹' s := by rw [ihn]
        _ = s := hs

/-- Sets in the shift-invariant σ-algebra are fixed by every shift iterate. -/
theorem MeasurableSet.shift_iterate_preimage_eq {s : Set (ℕ → α)}
    (hs : MeasurableSet[shiftInvariantSigma α] s) (n : ℕ) :
    (shift α)^[n] ⁻¹' s = s :=
  (MeasurableSet.isShiftInvariant_of_shiftInvariantSigma hs).iterate n

/-- The one-sided shift is measurable as a map on the shift-invariant σ-algebra. -/
theorem measurable_shift_shiftInvariantSigma :
    @Measurable (ℕ → α) (ℕ → α) (shiftInvariantSigma α) (shiftInvariantSigma α) (shift α) := by
  intro s hs
  rw [MeasurableSet.isShiftInvariant_of_shiftInvariantSigma hs]
  exact hs

/-- Every iterate of the one-sided shift is measurable as a map on the shift-invariant
σ-algebra. -/
theorem measurable_shift_iterate_shiftInvariantSigma (n : ℕ) :
    @Measurable (ℕ → α) (ℕ → α) (shiftInvariantSigma α) (shiftInvariantSigma α)
      ((shift α)^[n]) := by
  intro s hs
  rw [MeasurableSet.shift_iterate_preimage_eq hs n]
  exact hs

/-- A function measurable with respect to the shift-invariant σ-algebra is fixed by the
one-sided shift. -/
theorem comp_shift_eq_of_measurable_shiftInvariantSigma [MeasurableSpace β]
    [MeasurableSingletonClass β] {g : (ℕ → α) → β}
    (hg : @Measurable (ℕ → α) β (shiftInvariantSigma α) inferInstance g) :
    g ∘ shift α = g :=
  MeasurableSpace.comp_eq_of_measurable_invariants hg

end Probability

end TauCeti
