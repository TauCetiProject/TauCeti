/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import TauCeti.Topology.Algebra.IsOpenUnits

/-!
# Borel measurability of `Ring.inverse` for monoids with open units

In a topological monoid `M` with open units (`IsOpenUnits M`), `{x : M | IsUnit x}` is open and
therefore Borel measurable (`measurableSet_isUnit`). In a topological monoid with zero satisfying
`IsOpenUnits R` (in particular, in any complete normed ring or endomorphism algebra `E →L[𝕜] E`
of a Banach space via `NormedRing.instIsOpenUnits`), `Ring.inverse : R → R` is continuous at every
unit (`IsOpenUnits.continuousAt_ringInverse`) and vanishes outside `{x : R | IsUnit x}`, so it is
Borel measurable (`measurable_ringInverse`).

## Main results

* `measurableSet_isUnit`: `{x : M | IsUnit x}` is Borel measurable when `IsOpenUnits M`.
* `measurable_ringInverse`, `Measurable.ringInverse`, `AEMeasurable.ringInverse`: Borel
  measurability of `Ring.inverse` under `IsOpenUnits R`.
-/

public section

open MeasureTheory Set Topology

/-- In a topological monoid with open units, the set of units `{x : M | IsUnit x}` is Borel
measurable. -/
theorem measurableSet_isUnit {M : Type*} [Monoid M] [TopologicalSpace M] [IsOpenUnits M]
    [MeasurableSpace M] [OpensMeasurableSpace M] :
    MeasurableSet {x : M | IsUnit x} := by
  have heq : {x : M | IsUnit x} = range (Units.val : Mˣ → M) := by
    ext x
    exact Iff.rfl
  rw [heq]
  exact IsOpenUnits.isOpenEmbedding_unitsVal.isOpen_range.measurableSet

section MonoidWithZero

variable {R : Type*} [MonoidWithZero R] [TopologicalSpace R] [IsOpenUnits R]
  [MeasurableSpace R] [BorelSpace R]

/-- Ring inversion `Ring.inverse` on a monoid with zero and open units is Borel measurable: it is
continuous on the open set of units and zero on its complement. -/
@[fun_prop]
theorem measurable_ringInverse : Measurable (Ring.inverse : R → R) := by
  classical
  have hcont : ContinuousOn (Ring.inverse : R → R) {x : R | IsUnit x} := by
    intro x (hx : IsUnit x)
    obtain ⟨u, rfl⟩ := hx
    exact (IsOpenUnits.continuousAt_ringInverse u).continuousWithinAt
  have heq : (Ring.inverse : R → R) =
      {x : R | IsUnit x}.piecewise Ring.inverse (fun _ => 0) := by
    ext x
    by_cases hx : x ∈ {x : R | IsUnit x}
    · rw [Set.piecewise_eq_of_mem _ _ _ hx]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx, Ring.inverse_non_unit x hx]
  rw [heq]
  exact hcont.measurable_piecewise continuousOn_const measurableSet_isUnit

/-- Composition form of `measurable_ringInverse` for `fun_prop` and dot notation. -/
@[fun_prop]
theorem Measurable.ringInverse {α : Type*} [MeasurableSpace α] {f : α → R} (hf : Measurable f) :
    Measurable fun a => Ring.inverse (f a) :=
  measurable_ringInverse.comp hf

/-- Almost-everywhere measurable composition form of `measurable_ringInverse`. -/
@[fun_prop]
theorem AEMeasurable.ringInverse {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → R}
    (hf : AEMeasurable f μ) : AEMeasurable (fun a => Ring.inverse (f a)) μ :=
  measurable_ringInverse.comp_aemeasurable hf

end MonoidWithZero
