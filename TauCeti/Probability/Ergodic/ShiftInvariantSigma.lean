module

public import TauCeti.Probability.Exchangeability.Basic
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

variable {α β : Type*}

/-- A path-space event is shift-invariant if its preimage under the one-sided shift is itself. -/
def isShiftInvariant (s : Set (ℕ → α)) : Prop :=
  shift α ⁻¹' s = s

/-- The defining characterization of shift-invariant path-space events. -/
@[simp]
theorem isShiftInvariant_iff {s : Set (ℕ → α)} :
    isShiftInvariant s ↔ shift α ⁻¹' s = s :=
  Iff.rfl

variable [MeasurableSpace (ℕ → α)]

/-- The σ-algebra of measurable shift-invariant events on one-sided path space. -/
@[implicit_reducible]
def shiftInvariantSigma (α : Type*) [MeasurableSpace (ℕ → α)] : MeasurableSpace (ℕ → α) :=
  MeasurableSpace.invariants (shift α)

/-- A set is measurable for `shiftInvariantSigma` iff it is ambient-measurable and invariant
under the one-sided shift. -/
@[simp]
theorem mem_shiftInvariantSigma_iff {s : Set (ℕ → α)} :
    MeasurableSet[shiftInvariantSigma α] s ↔ MeasurableSet s ∧ isShiftInvariant s :=
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
    (hs : MeasurableSet[shiftInvariantSigma α] s) : isShiftInvariant s :=
  (mem_shiftInvariantSigma_iff.mp hs).2

/-- An ambient-measurable shift-invariant set is measurable for `shiftInvariantSigma`. -/
theorem isShiftInvariant.measurableSet_shiftInvariantSigma {s : Set (ℕ → α)}
    (hs : isShiftInvariant s) (hsm : MeasurableSet s) :
    MeasurableSet[shiftInvariantSigma α] s :=
  mem_shiftInvariantSigma_iff.mpr ⟨hsm, hs⟩

omit [MeasurableSpace (ℕ → α)] in
/-- A shift-invariant path-space event is fixed by every iterate of the one-sided shift. -/
@[simp]
theorem isShiftInvariant.preimage_shift_iterate_eq {s : Set (ℕ → α)}
    (hs : isShiftInvariant s) (n : ℕ) : ((shift α)^[n]) ⁻¹' s = s :=
  Function.IsFixedPt.preimage_iterate hs n

/-- A `shiftInvariantSigma`-measurable set is fixed by every iterate of the one-sided shift. -/
@[simp]
theorem MeasurableSet.preimage_shift_iterate_eq_of_shiftInvariantSigma {s : Set (ℕ → α)}
    (hs : MeasurableSet[shiftInvariantSigma α] s) (n : ℕ) : ((shift α)^[n]) ⁻¹' s = s :=
  (MeasurableSet.isShiftInvariant_of_shiftInvariantSigma hs).preimage_shift_iterate_eq n

/-- Every iterate of the one-sided shift is measurable as a map on the shift-invariant
σ-algebra. -/
theorem measurable_shift_iterate_shiftInvariantSigma (n : ℕ) :
    @Measurable (ℕ → α) (ℕ → α) (shiftInvariantSigma α) (shiftInvariantSigma α)
      ((shift α)^[n]) := by
  intro s hs
  have hs_iter : MeasurableSet[MeasurableSpace.invariants ((shift α)^[n])] s :=
    (MeasurableSpace.le_invariants_iterate (shift α) n) s hs
  rw [(MeasurableSpace.measurableSet_invariants.mp hs_iter).2]
  exact hs

/-- The one-sided shift is measurable as a map on the shift-invariant σ-algebra. -/
theorem measurable_shift_shiftInvariantSigma :
    @Measurable (ℕ → α) (ℕ → α) (shiftInvariantSigma α) (shiftInvariantSigma α) (shift α) := by
  simpa using measurable_shift_iterate_shiftInvariantSigma (α := α) 1

/-- An ambient-measurable observable fixed by the one-sided shift is measurable with respect to
the shift-invariant σ-algebra. -/
theorem measurable_shiftInvariantSigma_of_comp_shift_eq [MeasurableSpace β]
    {g : (ℕ → α) → β} (hg : Measurable g) (hg_shift : g ∘ shift α = g) :
    @Measurable (ℕ → α) β (shiftInvariantSigma α) inferInstance g :=
  MeasurableSpace.measurable_invariants_dom.mpr ⟨hg, fun _ _ => by rw [hg_shift]⟩

/-- A function measurable with respect to the shift-invariant σ-algebra is fixed by the
one-sided shift. -/
theorem comp_shift_eq_of_measurable_shiftInvariantSigma [MeasurableSpace β]
    [MeasurableSingletonClass β] {g : (ℕ → α) → β}
    (hg : @Measurable (ℕ → α) β (shiftInvariantSigma α) inferInstance g) :
    g ∘ shift α = g :=
  MeasurableSpace.comp_eq_of_measurable_invariants hg

end Probability

end TauCeti
