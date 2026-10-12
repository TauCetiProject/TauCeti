/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.CompactOpen
public import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Metrizable.ContinuousMap

/-!
# Polish spaces of continuous homomorphisms

The compact-open space of continuous homomorphisms from a second-countable locally compact
monoid to a Polish topological monoid is Polish. In particular, this supplies the regularity
of spaces of characters needed for uniqueness of Fourier–Stieltjes measures.
-/

public section

namespace TauCeti

/-- Continuous homomorphisms from a second-countable locally compact monoid to a Polish
topological monoid form a Polish space in the compact-open topology. -/
instance _root_.ContinuousMonoidHom.instPolishSpace {A B : Type*}
    [Monoid A] [TopologicalSpace A] [LocallyCompactSpace A] [SecondCountableTopology A]
    [Monoid B] [TopologicalSpace B] [ContinuousMul B] [PolishSpace B] :
    PolishSpace (A →ₜ* B) := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable B
  have : PolishSpace C(A, B) := inferInstance
  exact (ContinuousMonoidHom.isClosedEmbedding_toContinuousMap A B).polishSpace

end TauCeti
