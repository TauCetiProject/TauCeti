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

In a topological monoid with open units (`IsOpenUnits`), `{x | IsUnit x}` is open and Borel
measurable (`measurableSet_isUnit`), and `Ring.inverse` on a `MonoidWithZero` with open units is
Borel measurable (`measurable_ringInverse`, `Measurable.ringInverse`, `AEMeasurable.ringInverse`).
-/

public section

open MeasureTheory Set Topology

/-- In a topological monoid with open units, `{x : M | IsUnit x}` is Borel measurable. -/
theorem measurableSet_isUnit {M : Type*} [Monoid M] [TopologicalSpace M] [IsOpenUnits M]
    [MeasurableSpace M] [OpensMeasurableSpace M] : MeasurableSet {x : M | IsUnit x} :=
  IsOpenUnits.isOpenEmbedding_unitsVal.isOpen_range.measurableSet

section MonoidWithZero

variable {R : Type*} [MonoidWithZero R] [TopologicalSpace R] [IsOpenUnits R]
  [MeasurableSpace R] [BorelSpace R]

/-- Ring inversion `Ring.inverse` on a monoid with zero and open units is Borel measurable. -/
@[fun_prop]
theorem measurable_ringInverse : Measurable (Ring.inverse : R → R) := by
  classical
  have hcont : ContinuousOn (Ring.inverse : R → R) {x : R | IsUnit x} := by
    rintro _ ⟨u, rfl⟩; exact (IsOpenUnits.continuousAt_ringInverse u).continuousWithinAt
  have heq : (Ring.inverse : R → R) = {x : R | IsUnit x}.piecewise Ring.inverse 0 := funext fun x =>
    if hx : x ∈ {x : R | IsUnit x} then (Set.piecewise_eq_of_mem _ _ _ hx).symm
    else (Ring.inverse_non_unit x hx).trans
      (Set.piecewise_eq_of_notMem _ Ring.inverse (0 : R → R) hx).symm
  exact heq ▸ hcont.measurable_piecewise continuousOn_const measurableSet_isUnit

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
