/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.ClosedPoints
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Translation
public import TauCeti.Topology.Algebra.MulAction.Orbit

/-!
# Projective orbit images are locally closed

The full topological image of a finite-type affine group's projective orbit morphism is
locally closed over an algebraically closed field. This includes its nonclosed points;
it is not a statement only about the orbit of rational points. Neither smoothness nor
reducedness of the group is required.

This supplies the locally closed subset on which to construct the orbit scheme, a geometric
model for the homogeneous space of the stabilizer of the chosen line. It does not identify
scheme-theoretic fibers or prove flatness or representability of a quotient sheaf.

The argument combines `isConstructible_range_projectiveOrbitMap`,
`range_projectiveOrbitMap_kernelPoint_eq_range_inter_closedPoints`, translation invariance,
and `isLocallyClosed_of_isConstructible_of_closedPoints_transitive`. Rational translations
are transitive on the closed points of the image, even though they need not be transitive
on all its points.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f, orbits and homogeneous spaces.
-/

public section

open CategoryTheory AlgebraicGeometry WithConv TopologicalSpace

namespace TauCeti.Comodule

universe u

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [AddCommGroup M] [Module k M] [Comodule k H M]
  [Module.Finite k M]

/-- Rational translations are transitive on the closed points of the full projective
orbit image. -/
theorem exists_smul_eq_of_mem_range_projectiveOrbitMap_inter_closedPoints
    (m : M) (hm : Module.IsUnimodular k m)
    {x y : Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M))}
    (hx : x ∈ Set.range (projectiveOrbitMap (H := H) m hm) ∩ closedPoints _)
    (hy : y ∈ Set.range (projectiveOrbitMap (H := H) m hm) ∩ closedPoints _) :
    letI := projectivePointMulAction (R := k) (H := H) (M := M)
    ∃ g : WithConv (H →ₐ[k] k), g • x = y := by
  let := projectivePointMulAction (R := k) (H := H) (M := M)
  rw [← range_projectiveOrbitMap_kernelPoint_eq_range_inter_closedPoints m hm] at hx hy
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨h, rfl⟩ := hy
  refine ⟨h * g⁻¹, ?_⟩
  rw [projectivePoint_smul_def]
  exact (projectivePointTranslation_projectiveOrbitMap_kernelPoint
    (h * g⁻¹) g m hm).trans (by simp)

/-- The entire topological image of a finite-type affine group's projective orbit morphism
is locally closed over an algebraically closed field, including for nonreduced groups. -/
theorem isLocallyClosed_range_projectiveOrbitMap (m : M) (hm : Module.IsUnimodular k m) :
    IsLocallyClosed (Set.range (projectiveOrbitMap (H := H) m hm)) := by
  let := projectivePointMulAction (R := k) (H := H) (M := M)
  have := projectivePointMulAction_continuousConstSMul (R := k) (H := H) (M := M)
  apply isLocallyClosed_of_isConstructible_of_closedPoints_transitive
    (G := WithConv (H →ₐ[k] k)) (isConstructible_range_projectiveOrbitMap m hm)
  · intro g
    rw [Set.preimage_smul, ← Set.image_smul]
    simpa only [projectivePoint_smul_def] using
      image_projectivePointTranslation_range_projectiveOrbitMap g⁻¹ m hm
  · intro x hx y hy
    exact exists_smul_eq_of_mem_range_projectiveOrbitMap_inter_closedPoints m hm hx hy

end TauCeti.Comodule
