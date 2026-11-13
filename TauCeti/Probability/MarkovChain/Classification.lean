/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Invariant
public import TauCeti.Probability.MarkovChain.ClosedClass

/-!
# Null recurrence and finite communicating classes

A null recurrent state returns almost surely but has infinite extended mean positive
return time. Together with positive recurrence and transience, this gives the three
mutually exclusive state classifications. Null recurrence is constant on communicating
classes and is preserved by restriction to a closed set.

Every finite closed communicating class is positive recurrent, even when the ambient
state space is infinite. On a countable state space, a null recurrent state has an
infinite communicating class. Recurrence and positive recurrence coincide on finite spaces.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §§1.5–1.7.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S] {κ : Kernel S S} [IsMarkovKernel κ] {x y : S}

/-- A state is null recurrent if it returns almost surely but its extended mean
positive return time is infinite. -/
def IsNullRecurrent (κ : Kernel S S) [IsMarkovKernel κ] (x : S) : Prop :=
  κ.IsRecurrent x ∧ κ.meanReturnTime x = ∞

/-- The defining characterization of null recurrence. -/
theorem isNullRecurrent_iff :
    κ.IsNullRecurrent x ↔ κ.IsRecurrent x ∧ κ.meanReturnTime x = ∞ := Iff.rfl

/-- Null recurrence is recurrence without positive recurrence. The recurrence condition
cannot be omitted: transient states also have infinite mean return time. -/
theorem isNullRecurrent_iff_isRecurrent_and_not_isPositiveRecurrent :
    κ.IsNullRecurrent x ↔ κ.IsRecurrent x ∧ ¬ κ.IsPositiveRecurrent x := by
  simp [isNullRecurrent_iff, isPositiveRecurrent_iff, lt_top_iff_ne_top]

/-- Every null recurrent state is recurrent. -/
theorem IsNullRecurrent.isRecurrent (hx : κ.IsNullRecurrent x) : κ.IsRecurrent x :=
  hx.1

/-- A null recurrent state has infinite extended mean positive return time. -/
theorem IsNullRecurrent.meanReturnTime_eq_top (hx : κ.IsNullRecurrent x) :
    κ.meanReturnTime x = ∞ := hx.2

/-- A null recurrent state is not positive recurrent. -/
theorem IsNullRecurrent.not_isPositiveRecurrent (hx : κ.IsNullRecurrent x) :
    ¬ κ.IsPositiveRecurrent x :=
  (isNullRecurrent_iff_isRecurrent_and_not_isPositiveRecurrent.mp hx).2

/-- Recurrence splits into the mutually exclusive positive and null cases. -/
theorem isRecurrent_iff_isPositiveRecurrent_or_isNullRecurrent :
    κ.IsRecurrent x ↔ κ.IsPositiveRecurrent x ∨ κ.IsNullRecurrent x := by
  rw [isNullRecurrent_iff_isRecurrent_and_not_isPositiveRecurrent]
  constructor
  · intro hx
    by_cases hpos : κ.IsPositiveRecurrent x
    · exact Or.inl hpos
    · exact Or.inr ⟨hx, hpos⟩
  · rintro (hx | hx)
    · exact hx.isRecurrent
    · exact hx.1

section MeasurableSingleton

variable [MeasurableSingletonClass S]

/-- Communicating states are null recurrent together. -/
theorem Communicates.isNullRecurrent_iff (hxy : κ.Communicates x y) :
    κ.IsNullRecurrent x ↔ κ.IsNullRecurrent y := by
  simp only [isNullRecurrent_iff_isRecurrent_and_not_isPositiveRecurrent,
    hxy.isRecurrent_iff, hxy.isPositiveRecurrent_iff]

/-- Every state reachable from a null recurrent state is null recurrent. Recurrence
forces the reverse reachability, so the states lie in the same communicating class. -/
theorem IsNullRecurrent.of_reaches (hx : κ.IsNullRecurrent x) (hxy : κ.Reaches x y) :
    κ.IsNullRecurrent y :=
  (Communicates.isNullRecurrent_iff
    ((communicates_def x y).mpr ⟨hxy, hx.isRecurrent.reaches_of_reaches hxy⟩)).mp hx

/-- Restriction to a closed set preserves and reflects positive recurrence. -/
@[simp]
theorem isPositiveRecurrent_subtype_iff {s : Set S} (hs : MeasurableSet s)
    [IsMarkovKernel (κ.subtype hs)] (x : s) :
    (κ.subtype hs).IsPositiveRecurrent x ↔ κ.IsPositiveRecurrent x.val := by
  simp only [isPositiveRecurrent_iff, meanReturnTime_subtype]

/-- Restriction to a closed set preserves and reflects null recurrence. -/
@[simp]
theorem isNullRecurrent_subtype_iff {s : Set S} (hs : MeasurableSet s)
    [IsMarkovKernel (κ.subtype hs)] (x : s) :
    (κ.subtype hs).IsNullRecurrent x ↔ κ.IsNullRecurrent x.val := by
  simp only [isNullRecurrent_iff, isRecurrent_subtype_iff, meanReturnTime_subtype]

/-- Every state in a finite closed communicating class is positive recurrent.
Only the class, not the ambient state space, must be finite. -/
theorem isPositiveRecurrent_of_finite_communicatingClass
    (hfinite : (κ.communicatingClass x).Finite)
    (hclosed : κ.IsClosedSet (κ.communicatingClass x)) : κ.IsPositiveRecurrent x := by
  have := hfinite.to_subtype
  have hmeas : MeasurableSet (κ.communicatingClass x) := hfinite.measurableSet
  let : IsMarkovKernel (κ.subtype hmeas) :=
    (isMarkovKernel_subtype_iff_isClosedSet hmeas).mpr hclosed
  let : IsIrreducible Measure.count (κ.subtype hmeas) :=
    (isIrreducible_subtype_iff hmeas hclosed).mpr fun a ha b hb =>
      (((mem_communicatingClass_iff x a).mp ha).symm.trans
        ((mem_communicatingClass_iff x b).mp hb))
  exact (isPositiveRecurrent_subtype_iff hmeas
    ⟨x, by simp⟩).mp ((κ.subtype hmeas).isPositiveRecurrent_of_finite ⟨x, by simp⟩)

/-- A recurrent state with a finite communicating class is positive recurrent.
Closedness is automatic from recurrence. -/
theorem IsRecurrent.isPositiveRecurrent_of_finite_communicatingClass [Countable S]
    (hx : κ.IsRecurrent x) (hfinite : (κ.communicatingClass x).Finite) :
    κ.IsPositiveRecurrent x :=
  Kernel.isPositiveRecurrent_of_finite_communicatingClass hfinite hx.isClosedSet_communicatingClass

/-- A null recurrent state necessarily has an infinite communicating class. -/
theorem IsNullRecurrent.infinite_communicatingClass [Countable S] (hx : κ.IsNullRecurrent x) :
    (κ.communicatingClass x).Infinite := by
  intro hfinite
  exact hx.not_isPositiveRecurrent
    (hx.isRecurrent.isPositiveRecurrent_of_finite_communicatingClass hfinite)

/-- On a finite state space, a state is recurrent exactly when it is positive recurrent;
no irreducibility assumption is needed. -/
theorem isRecurrent_iff_isPositiveRecurrent_of_finite [Finite S] :
    κ.IsRecurrent x ↔ κ.IsPositiveRecurrent x :=
  ⟨fun hx => hx.isPositiveRecurrent_of_finite_communicatingClass (Set.toFinite _),
    IsPositiveRecurrent.isRecurrent⟩

end MeasurableSingleton

end ProbabilityTheory.Kernel
