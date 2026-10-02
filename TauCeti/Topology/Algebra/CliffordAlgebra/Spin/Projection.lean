/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpecialOrthogonal
public import TauCeti.Topology.Algebra.CliffordAlgebra.Pin.Action

/-!
# Continuity of the Spin projection

For a finite-dimensional quadratic space over a topological field with `2` invertible, the
Spin projections to the orthogonal and special orthogonal groups are continuous. The groups
inherit the canonical topologies from the Clifford algebra and the linear automorphism group,
respectively. The latter topology records both the forward and inverse endomorphisms.

The results apply without choosing coordinates or assuming nondegeneracy, separation, or local
compactness. They provide the continuous point-group maps used to compare local Spin and special
orthogonal subgroups. The inclusion into the Lipschitz group is continuous because a Spin
element's inverse in the Clifford algebra is its star; the projections then restrict the existing
continuous Lipschitz representation.

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

/-- The Spin representation into the orthogonal group is continuous for the canonical
Clifford-algebra and linear-automorphism topologies. -/
@[fun_prop]
theorem continuous_spinToOrthogonal : Continuous (spinToOrthogonal Q) := by
  exact ((continuous_pinToOrthogonal Q).comp (continuous_spinToPin Q)).congr fun x =>
    pinToOrthogonal_spinToPin x

/-- The Spin projection into the special orthogonal group is continuous for its subgroup
topology in the linear automorphism group. -/
@[fun_prop]
theorem continuous_spinToSpecialOrthogonal : Continuous (spinToSpecialOrthogonal Q) := by
  apply continuous_induced_rng.mpr
  have h := continuous_subtype_val.comp (continuous_spinToOrthogonal Q)
  refine h.congr fun x => ?_
  apply LinearEquiv.ext
  intro v
  simp only [Function.comp_apply, coe_spinToOrthogonal_apply,
    coe_spinToSpecialOrthogonal_apply]

end CliffordAlgebra

end TauCeti
