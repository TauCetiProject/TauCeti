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

For a nondegenerate quadratic form on a finite free module over a domain, every endomorphism
preserving the form is automatically invertible. Thus the orthogonal group, viewed in the space
of linear endomorphisms, is the common zero set of the equations `Q (f x) = Q x`.
The module topology makes each equation continuous, so this image is closed. This description
is useful when passing from the topology of linear endomorphisms to local orthogonal point groups.

The result holds over a Hausdorff topological commutative domain with two invertible and a finite
free module. Local compactness is not needed for closedness.
-/

public section

namespace TauCeti

namespace QuadraticMap

open scoped Topology

variable {R M : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [AddCommGroup M] [Module R M] [Module.Finite R M]
  [TopologicalSpace M] [IsModuleTopology R M]
  [TopologicalSpace (Module.End R M)] [IsModuleTopology R (Module.End R M)]
  [Invertible (2 : R)]

variable [IsDomain R] [Module.Free R M]

/-- The orthogonal group of a nondegenerate quadratic form on a finite free module is closed in
the endomorphism space, through its underlying linear maps. -/
theorem isClosed_range_orthogonalGroup_toLinearMap
    (Q : QuadraticForm R M) (hQ : Q.Nondegenerate) :
    IsClosed (Set.range (fun g : orthogonalGroup Q => (g : M ≃ₗ[R] M).toLinearMap)) := by
  rw [range_orthogonalGroup_toLinearMap Q ((QuadraticMap.nondegenerate_polar_iff).mpr hQ).1]
  exact Q.isClosed_setOfPred_forall_map_app Q.continuous

end QuadraticMap

end TauCeti
