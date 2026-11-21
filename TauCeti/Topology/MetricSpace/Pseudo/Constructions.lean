/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# Structures induced by maps with the same distances, and distances on `ℝ≥0`

Two maps `f : X → Y` and `g : X → Z` into pseudometric spaces with
`dist (f a) (f b) = dist (g a) (g b)` for all `a b` induce the same pseudometric on `X`
(`TauCeti.pseudoMetricSpace_induced_eq_of_dist_eq`), hence the same uniform structure
(`TauCeti.uniformSpace_comap_eq_of_dist_eq`) and topology. This identifies the structure induced
by a map with the one induced by a more convenient map preserving the same distances, for example
a restriction to a set off which the functions involved vanish.

On `ℝ≥0`, the distance from `a` to `b ≥ a` is `b - a` (`NNReal.dist_eq_sub_of_le`), next to
Mathlib's `NNReal.dist_eq`.
-/

public section

namespace TauCeti

variable {X Y Z : Type*} [PseudoMetricSpace Y] [PseudoMetricSpace Z] {f : X → Y} {g : X → Z}

/-- Two maps into pseudometric spaces that have the same distances induce the same
pseudometric. -/
theorem pseudoMetricSpace_induced_eq_of_dist_eq
    (h : ∀ a b, dist (f a) (f b) = dist (g a) (g b)) :
    PseudoMetricSpace.induced f ‹_› = PseudoMetricSpace.induced g ‹_› :=
  PseudoMetricSpace.ext (by ext a b; exact h a b)

/-- Two maps into pseudometric spaces that have the same distances induce the same uniform
structure. -/
theorem uniformSpace_comap_eq_of_dist_eq (h : ∀ a b, dist (f a) (f b) = dist (g a) (g b)) :
    UniformSpace.comap f inferInstance = UniformSpace.comap g inferInstance :=
  congrArg (fun m : PseudoMetricSpace X ↦ m.toUniformSpace)
    (pseudoMetricSpace_induced_eq_of_dist_eq h)

end TauCeti

/-- On `ℝ≥0`, the distance from `a` to `b ≥ a` is `b - a`. -/
theorem NNReal.dist_eq_sub_of_le {a b : NNReal} (h : a ≤ b) : dist a b = (b : ℝ) - a := by
  rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 h))]
