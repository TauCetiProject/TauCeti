/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Absolute
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Sphere

/-!
# Integrals of closed two-forms on the second homology of a simply connected manifold

Let `M` be a simply connected compact boundaryless manifold and `φ` a closed `C¹` two-form on
`M`. The Hurewicz map `π₂(M, x) → H₂(M; ℤ)` is then an isomorphism at every base point
(`HomotopyGroup.hurewiczAddEquiv`), so the integral of `φ` over the second homotopy group
(`TauCeti.sphereIntegralHom`) descends to a homomorphism
`TauCeti.homologySphereIntegralHom : H₂(M; ℤ) →+ F`. Since both the sphere integral and the
Hurewicz map are invariant under base-point change, it agrees with the sphere integral on the
Hurewicz class of every sphere, at every base point
(`TauCeti.homologySphereIntegralHom_hurewiczIntHom`). For the symplectic form of a simply
connected symplectic manifold this is the symplectic area on `H₂(M; ℤ)` together with the agreement
`hω` under which the capped action `TauCeti.Floer.SphericalCapClass.action` is defined.

## Main definitions

* `TauCeti.homologySphereIntegralHom`: the integral of a closed `C¹` two-form on `H₂(M; ℤ)` for a
  simply connected `M`.

## Main results

* `TauCeti.homologySphereIntegralHom_hurewiczIntHom`: it agrees with the sphere integral on
  Hurewicz classes, at every base point.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.2 (the Hurewicz theorem).
-/

public section

noncomputable section

open AlgebraicTopology HomotopyGroup
open scoped Manifold ContDiff Topology Topology.Homotopy

namespace TauCeti

variable {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [I.Boundaryless]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SimplyConnectedSpace M]
  {φ : RoughForm I M F 2}

/-- **The integral of a closed `C¹` two-form on `H₂(M; ℤ)`** for a simply connected manifold `M`:
the sphere integral at a base point, transported along the Hurewicz isomorphism
`π₂(M, x) ≅ H₂(M; ℤ)` (`HomotopyGroup.hurewiczLift`). It does not depend on the base point: it
agrees with the sphere integral on the Hurewicz class of every sphere, at every base point
(`TauCeti.homologySphereIntegralHom_hurewiczIntHom`). -/
def homologySphereIntegralHom (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of M) →+
      F :=
  hurewiczLift fun x ↦ sphereIntegralHom x hφ hdφ

/-- **The integral of a closed `C¹` two-form on `H₂(M; ℤ)` is the sphere integral on Hurewicz
classes**, at every base point. -/
@[simp]
theorem homologySphereIntegralHom_hurewiczIntHom (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) (x : M) (a : Additive (π_ 2 M x)) :
    homologySphereIntegralHom hφ hdφ (hurewiczIntHom M x 1 a) = sphereIntegralHom x hφ hdφ a :=
  hurewiczLift_hurewiczIntHom (fun γ a ↦ by
    simpa using sphereIntegral_homotopyGroupTransport hφ hdφ γ a) x a

end TauCeti
