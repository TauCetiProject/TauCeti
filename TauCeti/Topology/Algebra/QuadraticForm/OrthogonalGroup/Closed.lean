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

For a nondegenerate quadratic form on a finite-dimensional space, every endomorphism preserving
the form is automatically invertible. Thus the orthogonal group, viewed in the space of linear
endomorphisms, is the common zero set of the equations `Q (f x) = Q x`. The module topology makes
each equation continuous, so this image is closed. This description is useful when passing from
the topology of linear endomorphisms to local orthogonal point groups.

The result holds over any Hausdorff topological field with two invertible. Local compactness is
not needed for closedness.
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

/-- The endomorphisms preserving a quadratic form are a closed subset of the endomorphism space.
This assertion does not require nondegeneracy. -/
theorem isClosed_setOfPred_forall_map_app (Q : QuadraticForm R M) :
    IsClosed {f : Module.End R M | ∀ x : M, Q (f x) = Q x} := by
  let : ContinuousAdd M := IsModuleTopology.toContinuousAdd R M
  have h (x : M) : IsClosed {f : Module.End R M | Q (f x) = Q x} := by
    have hev : Continuous (fun f : Module.End R M => f x) :=
      IsModuleTopology.continuous_of_linearMap ((LinearMap.applyₗ :
        M →ₗ[R] Module.End R M →ₗ[R] M) x)
    exact isClosed_eq (Q.continuous.comp hev) continuous_const
  simpa only [Set.ofPred_forall] using isClosed_iInter h

variable [IsDomain R] [Module.Free R M]

/-- The orthogonal group of a nondegenerate quadratic form on a finite free module is closed in
the endomorphism space, through its underlying linear maps. -/
theorem isClosed_range_orthogonalGroup_toLinearMap
    (Q : QuadraticForm R M) (hQ : Q.Nondegenerate) :
    IsClosed (Set.range (fun g : orthogonalGroup Q => (g : M ≃ₗ[R] M).toLinearMap)) := by
  rw [range_orthogonalGroup_toLinearMap Q ((QuadraticMap.nondegenerate_polar_iff).mpr hQ).1]
  exact isClosed_setOfPred_forall_map_app Q

end QuadraticMap

end TauCeti
