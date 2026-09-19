/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Action

/-!
# Invariant measures of a scalar multiplication

General facts about `SMulInvariantMeasure`, Mathlib's class of measures invariant under a scalar
multiplication, that do not concern ergodicity: the restriction of an invariant measure to an
exactly invariant measurable set is again invariant (`SMulInvariantMeasure.restrict`).
-/

public section

open Set

namespace MeasureTheory

variable {G X : Type*} [SMul G X] {m : MeasurableSpace X} {μ : Measure X}

/-- The restriction of an invariant measure to an exactly invariant measurable set is
invariant. -/
theorem SMulInvariantMeasure.restrict [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ]
    {u : Set X} (hum : MeasurableSet u) (huinv : ∀ g : G, (g • ·) ⁻¹' u = u) :
    SMulInvariantMeasure G X (μ.restrict u) :=
  ⟨fun g v hv => by
    have hmp := (measurePreserving_smul g μ).restrict_preimage hum
    rw [huinv g] at hmp
    exact hmp.measure_preimage hv.nullMeasurableSet⟩

end MeasureTheory
