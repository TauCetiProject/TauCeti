/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The Borel σ-algebra of the units topology

The units `Mˣ` of a topological monoid carry the topology induced by the embedding
`u ↦ (u, u⁻¹)` into `M × Mᵐᵒᵖ`, which in general is not the subspace topology along `Units.val`
(for example for the ideles, the units of the adele ring). Mathlib's `Units.instMeasurableSpace`
gives `Mˣ` the pullback σ-algebra along `Units.val` whenever `M` is measurable, so this σ-algebra
need not be the Borel σ-algebra of the units topology.

`Units.borelMeasurableSpace M` is the Borel σ-algebra of the units topology, as a definition and
not an instance, so that it does not form a diamond with `Units.instMeasurableSpace`. Haar measures
on unit groups such as the ideles and `GL_n` of the adeles live on it.

## Main results

* `Units.borelMeasurableSpace`: the Borel σ-algebra of the units topology on `Mˣ`.
* `Units.borelSpace_borelMeasurableSpace`: it is a Borel structure.
-/

public section

namespace Units

variable (M : Type*) [Monoid M] [TopologicalSpace M]

/-- The Borel σ-algebra on `Mˣ` for its units topology. It is not an instance: Mathlib's
`Units.instMeasurableSpace` already gives the units of a measurable monoid the pullback
σ-algebra along `Units.val`, and the units topology need not be the subspace topology. -/
@[instance_reducible]
def borelMeasurableSpace : MeasurableSpace Mˣ := borel Mˣ

/-- `Units.borelMeasurableSpace M` is the Borel σ-algebra of the units topology on `Mˣ`. -/
theorem borelSpace_borelMeasurableSpace : @BorelSpace Mˣ _ (borelMeasurableSpace M) :=
  @BorelSpace.mk _ _ (borelMeasurableSpace M) rfl

end Units
