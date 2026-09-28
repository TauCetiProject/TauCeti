/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup
public import TauCeti.Topology.Algebra.QuadraticForm.Continuity

/-!
# Closedness of the orthogonal group in the endomorphism space

For a quadratic form with separating polar form on a finite free module over a domain, every
endomorphism preserving the form is automatically invertible. Thus the orthogonal group, viewed
in the space of linear endomorphisms, is the common zero set of the equations `Q (f x) = Q x`.
When the form is continuous, this image is closed. This description is useful when passing from
the topology of linear endomorphisms to local orthogonal point groups.

The result holds over a Hausdorff commutative domain with module topologies and a finite free
module, provided the form is continuous. If the scalar topology is a topological ring, invertibility
of two supplies continuity; the theorem takes continuity directly. Local compactness is not needed
for closedness.
-/

public section

namespace TauCeti

namespace QuadraticMap

open scoped Topology

variable {R M : Type*} [CommRing R] [TopologicalSpace R] [T2Space R]
  [AddCommGroup M] [Module R M] [Module.Finite R M]
  [TopologicalSpace M] [IsModuleTopology R M]
  [TopologicalSpace (Module.End R M)] [IsModuleTopology R (Module.End R M)]

variable [IsDomain R] [Module.Free R M]

/-- The orthogonal group of a continuous quadratic form with separating polar form on a finite
free module is closed in the endomorphism space, through its underlying linear maps. -/
theorem isClosed_range_orthogonalGroup_toLinearMap
    (Q : QuadraticForm R M) (hQ : Q.polarBilin.SeparatingLeft) (hcont : Continuous Q) :
    IsClosed (Set.range (fun g : orthogonalGroup Q => (g : M ≃ₗ[R] M).toLinearMap)) := by
  rw [range_orthogonalGroup_toLinearMap Q hQ]
  exact Q.isClosed_setOfPred_forall_map_app hcont

end QuadraticMap

end TauCeti
