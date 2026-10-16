/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.UniformSpace.Completion

/-!
# Neighbourhoods and fibres of the map to the separated completion

If the neighbourhood filter of a point of a uniform space is countably generated, so is the
neighbourhood filter of its image in the separated completion. Nothing is assumed of the space
beyond its uniformity — no separation, no completeness, no algebraic structure.

`TauCeti.Topology.Algebra.GroupCompletion` specialises this to the zero of a uniform
space with a zero, which is the form typeclass resolution consumes.

Two points of a uniform space have the same image in the separated completion exactly when they
are inseparable. Mathlib's `UniformSpace.Completion.coe_inj` is the case of a `T0Space`, where
inseparable points are equal; without separation the canonical map identifies precisely the
points that the separation quotient identifies.

## Main results

* `UniformSpace.Completion.isCountablyGenerated_nhds_coe`.
* `UniformSpace.Completion.coe_eq_coe_iff_inseparable`.
-/

public section

open Filter
open scoped Topology

namespace UniformSpace.Completion

/-- **Countable generation of `𝓝 x` passes to the separated completion.** -/
theorem isCountablyGenerated_nhds_coe {α : Type*} [UniformSpace α] {x : α}
    [(𝓝 x).IsCountablyGenerated] : (𝓝 (x : Completion α)).IsCountablyGenerated := by
  obtain ⟨V, hV⟩ := (𝓝 x).exists_antitone_basis
  exact (hV.toHasBasis.hasBasis_of_isDenseInducing isDenseInducing_coe).isCountablyGenerated

/-- Two points of a uniform space have the same image in the separated completion exactly when
they are inseparable. -/
theorem coe_eq_coe_iff_inseparable {α : Type*} [UniformSpace α] {a b : α} :
    (a : Completion α) = b ↔ Inseparable a b := by
  rw [← inseparable_iff_eq, isDenseInducing_coe.isInducing.inseparable_iff]

end UniformSpace.Completion

end
