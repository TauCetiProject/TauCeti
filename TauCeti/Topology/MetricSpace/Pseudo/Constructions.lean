/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# Topologies induced by maps with the same distances

Two maps `f : X → Y` and `g : X → Z` into pseudometric spaces with
`dist (f a) (f b) = dist (g a) (g b)` for all `a b` induce the same pseudometric on `X`
(`PseudoMetricSpace.induced`), hence the same topology
(`PseudoMetricSpace.induced_topology_eq_of_dist_eq`). This identifies the topology induced by a
map with the one induced by a more convenient map preserving the same distances, for example a
restriction to a set off which the functions involved vanish.
-/

public section

/-- Two maps into pseudometric spaces that have the same distances induce the same topology. -/
theorem PseudoMetricSpace.induced_topology_eq_of_dist_eq {X Y Z : Type*} [PseudoMetricSpace Y]
    [PseudoMetricSpace Z] {f : X → Y} {g : X → Z} (h : ∀ a b, dist (f a) (f b) = dist (g a) (g b)) :
    TopologicalSpace.induced f inferInstance = TopologicalSpace.induced g inferInstance := by
  have hm : PseudoMetricSpace.induced f inferInstance = PseudoMetricSpace.induced g inferInstance :=
    PseudoMetricSpace.ext (by ext a b; exact h a b)
  exact congrArg (fun m : PseudoMetricSpace X ↦ m.toUniformSpace.toTopologicalSpace) hm
