/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Basic
public import TauCeti.Topology.Algebra.CliffordAlgebra.Basic
public import Mathlib.Topology.Algebra.Group.Units

/-!
# Continuity of the Spin and Pin inclusions

The Pin group inherits the subtype topology from the Clifford algebra with its module topology.
Its inclusion into the Lipschitz group is continuous for the subgroup topology inside the units
of the Clifford algebra. Both unit coordinates are continuous: the forward coordinate is the
subtype coercion, and the inverse coordinate is Clifford star. This inclusion allows continuity
of the Lipschitz representation to restrict to Pin and Spin.
The Spin inclusion into Pin is continuous for their Clifford-algebra subtype topologies.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

namespace TauCeti

namespace CliffordAlgebra

open _root_.CliffordAlgebra

variable {R V : Type*} [CommRing R] [TopologicalSpace R]
  [AddCommGroup V] [Module R V] (Q : QuadraticForm R V)

/-- The Spin inclusion into the Pin group is continuous for their canonical
Clifford-algebra subtype topologies. -/
@[fun_prop]
theorem continuous_spinToPin : Continuous (spinToPin Q) := by
  apply continuous_induced_rng.mpr
  exact continuous_subtype_val.congr fun x => (coe_spinToPin_apply x).symm

/-- The Pin inclusion into the Lipschitz group is continuous for the canonical
Clifford-algebra and unit-group topologies. -/
@[fun_prop]
theorem continuous_pinToLipschitz : Continuous (pinToLipschitz Q) := by
  apply continuous_induced_rng.mpr
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_subtype_val.congr fun x => (coe_pinToLipschitz_apply Q x).symm
  · exact continuous_subtype_val.star.congr fun x => (coe_inv_pinToLipschitz x).symm

end CliffordAlgebra

end TauCeti
