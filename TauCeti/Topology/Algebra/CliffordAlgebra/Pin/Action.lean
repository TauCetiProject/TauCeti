/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Action
public import TauCeti.Topology.Algebra.CliffordAlgebra.Pin.Basic
public import TauCeti.Topology.Algebra.CliffordAlgebra.Lipschitz.Action

/-!
# Continuity of the Pin representation

For a finite-dimensional quadratic space over a topological field with `2` invertible, the
Pin representation into the orthogonal group is continuous. The domain has the subtype topology
from the Clifford algebra, and the codomain has the subgroup topology from the linear
automorphism group. The result restricts the continuous Lipschitz representation along the
continuous Pin inclusion and enables the later restriction to Spin.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

namespace TauCeti

namespace CliffordAlgebra

open _root_.CliffordAlgebra

variable {K V : Type*} [Field K] [TopologicalSpace K] [IsTopologicalSemiring K]
  [Invertible (2 : K)] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (Q : QuadraticForm K V)

/-- The Pin representation into the orthogonal group is continuous for the canonical
Clifford-algebra and linear-automorphism topologies. -/
@[fun_prop]
theorem continuous_pinToOrthogonal : Continuous (pinToOrthogonal Q) := by
  let _ : TopologicalSpace V := moduleTopology K V
  have h := (_root_.CliffordAlgebra.continuous_lipschitzToOrthogonal Q).comp
    (continuous_pinToLipschitz Q)
  exact h.congr fun x => (pinToOrthogonal_eq_lipschitzToOrthogonal x).symm

end CliffordAlgebra

end TauCeti
