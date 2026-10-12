/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Points
public import TauCeti.AlgebraicGeometry.AugmentationPoint.ClosedPoints
public import TauCeti.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Closed points of a projective orbit image

Over an algebraically closed field, every closed point in the full image of a finite-type
affine group's projective orbit morphism is the image of a rational group point. Conversely,
all rational orbit images are closed. The existing rational-fiber characterization therefore
describes every closed point of the image, rather than only a possibly smaller rational subset.

This is the closed-point lifting input for realizing homogeneous spaces as locally closed
projective orbits. The full image may also include nonclosed points. No smoothness or
reducedness hypothesis is imposed on the group.

The comparison uses `range_kernelPoint_eq_closedPoints` and the closed-point image theorem
for locally finite-type morphisms. Together with
`projectiveOrbitMap_kernelPoint_eq_iff_span_eq`, it identifies closed orbit images with
the lines through translated vectors.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f, orbits and homogeneous spaces.
-/

public section

open AlgebraicGeometry WithConv TopologicalSpace

namespace TauCeti.Comodule

universe u

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [AddCommGroup M] [Module k M] [Comodule k H M]
  [Module.Finite k M]

/-- Rational orbit images are exactly the closed points in the full topological image of
the projective orbit morphism. -/
theorem range_projectiveOrbitMap_kernelPoint_eq_range_inter_closedPoints
    (m : M) (hm : Module.IsUnimodular k m) :
    Set.range (fun g : WithConv (H →ₐ[k] k) ↦
      projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint g.ofConv)) =
        Set.range (projectiveOrbitMap (H := H) m hm) ∩
          closedPoints (Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule k
            (Module.Dual k M))) := by
  rw [← (projectiveOrbitMap (H := H) m hm).image_closedPoints_eq_range_inter_closedPoints,
    ← range_kernelPoint_eq_closedPoints (k := k) (A := H), ← Set.range_comp]
  exact (ofConv_surjective (A := H →ₐ[k] k)).range_comp
    (⇑(projectiveOrbitMap (H := H) m hm) ∘ AlgHom.kernelPoint)

end TauCeti.Comodule
