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

/-- The entire topological image of a finite-type affine group's projective orbit morphism
is locally closed over an algebraically closed field, including for nonreduced groups. -/
theorem isLocallyClosed_range_projectiveOrbitMap (m : M) (hm : Module.IsUnimodular k m) :
    IsLocallyClosed (Set.range (projectiveOrbitMap (H := H) m hm)) := by
  let X := Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M))
  -- Select the existing individual translations as the action used by the topological
  -- criterion. This local instance makes no assertion about a scheme-valued action family.
  let : MulAction (WithConv (H →ₐ[k] k)) X := {
    smul g x := (projectivePointTranslation (M := M) g).hom x
    one_smul x := by
      -- Expose the smul field currently being constructed before using its scheme identity.
      change (projectivePointTranslation (M := M) 1).hom x = x
      rw [projectivePointTranslation_one]
      rfl
    mul_smul g h x := by
      -- Expose the smul field currently being constructed before using composition.
      change (projectivePointTranslation (M := M) (g * h)).hom x =
        (projectivePointTranslation (M := M) g).hom
          ((projectivePointTranslation (M := M) h).hom x)
      rw [projectivePointTranslation_mul]
      rfl }
  let : ContinuousConstSMul (WithConv (H →ₐ[k] k)) X :=
    ⟨fun g ↦ (projectivePointTranslation (M := M) g).hom.continuous⟩
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace
    (TauCeti.SymmetricAlgebra.projToSpec k (Module.Dual k M))
  apply isLocallyClosed_of_isConstructible_of_closedPoints_transitive
    (G := WithConv (H →ₐ[k] k)) (isConstructible_range_projectiveOrbitMap m hm)
  · intro g
    have h := image_projectivePointTranslation_range_projectiveOrbitMap g⁻¹ m hm
    rw [Set.preimage_smul, ← Set.image_smul]
    exact h
  · intro x hx y hy
    rw [← range_projectiveOrbitMap_kernelPoint_eq_range_inter_closedPoints m hm] at hx hy
    obtain ⟨g, rfl⟩ := hx
    obtain ⟨h, rfl⟩ := hy
    refine ⟨h * g⁻¹, ?_⟩
    exact (projectivePointTranslation_projectiveOrbitMap_kernelPoint
      (h * g⁻¹) g m hm).trans (by simp)

end TauCeti.Comodule
