/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Endomorphism
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

variable {K V : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [TopologicalSpace V] [IsModuleTopology K V]
  [TopologicalSpace (Module.End K V)] [IsModuleTopology K (Module.End K V)]
  [Invertible (2 : K)]

/-- The endomorphisms preserving a quadratic form are a closed subset of the endomorphism space.
This assertion does not require nondegeneracy. -/
theorem isClosed_setOf_quadraticForm_preserving (Q : QuadraticForm K V) :
    IsClosed {f : Module.End K V | ∀ x : V, Q (f x) = Q x} := by
  let : ContinuousAdd V := IsModuleTopology.toContinuousAdd K V
  have h (x : V) : IsClosed {f : Module.End K V | Q (f x) = Q x} := by
    have hev : Continuous (fun f : Module.End K V => f x) :=
      IsModuleTopology.continuous_of_linearMap ((LinearMap.applyₗ :
        V →ₗ[K] Module.End K V →ₗ[K] V) x)
    exact isClosed_eq (Q.continuous.comp hev) continuous_const
  simpa only [Set.ofPred_forall] using isClosed_iInter h

/-- The orthogonal group of a nondegenerate finite-dimensional quadratic form is closed in the
endomorphism space, through its underlying linear maps. -/
theorem isClosed_range_orthogonalGroup_toLinearMap
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    IsClosed (Set.range (fun g : orthogonalGroup Q => (g : V ≃ₗ[K] V).toLinearMap)) := by
  rw [range_orthogonalGroup_toLinearMap Q hQ]
  exact isClosed_setOf_quadraticForm_preserving Q

end QuadraticMap

end TauCeti
