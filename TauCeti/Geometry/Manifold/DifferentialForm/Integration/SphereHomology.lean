/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Absolute
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Sphere

/-!
# Integrals of closed two-forms over the second homology of a simply connected manifold

Let `M` be a compact boundaryless simply connected manifold and `φ` a closed `C¹` two-form on `M`
with values in a normed space `F`. The integral of `φ` over spheres is a homomorphism
`TauCeti.sphereIntegralHom : π₂(M, x) → F`. Since `M` is simply connected, the Hurewicz
homomorphism `π₂(M, x) → H₂(M; ℤ)` is an isomorphism (`HomotopyGroup.hurewiczAddEquiv`), so the
integral of `φ` is defined on the whole of `H₂(M; ℤ)`:

`TauCeti.homologySphereIntegralHom x hφ hdφ : H₂(M; ℤ) →+ F`.

Its value on the Hurewicz class of a sphere at any base point `y` is the integral of `φ` over the
sphere (`TauCeti.homologySphereIntegralHom_hurewiczIntHom`), because both the Hurewicz class and
the integral are invariant under change of base point. In particular it does not depend on the
base point `x` used to define it (`TauCeti.homologySphereIntegralHom_eq`).

For the symplectic form of a closed simply connected symplectic manifold, such as a complex
projective space, this is the symplectic area `ω : H₂(M; ℤ) → ℝ` with which capped Hamiltonian
Floer theory forms the spherical period group `TauCeti.Floer.SphericalPeriodGroup ω c` and the
cap classes of contractible loops, and it is the area on spheres that the area and capped action of
cap classes require (`TauCeti.Floer.SphericalCapClass.area_mk`).

## Main definitions

* `TauCeti.homologySphereIntegralHom x hφ hdφ`: the integral of a closed `C¹` two-form over
  `H₂(M; ℤ)` of a simply connected compact manifold.

## Main results

* `TauCeti.homologySphereIntegralHom_hurewiczIntHom`: its value on the Hurewicz class of a sphere
  is the integral over the sphere.
* `TauCeti.homologySphereIntegralHom_eq`: it does not depend on the base point.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.2, Theorem 4.32 (the Hurewicz theorem).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  Section 11.1 (the symplectic area of spherical classes).
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology HomotopyGroup
open scoped Manifold ContDiff Topology Topology.Homotopy

namespace TauCeti

variable {E H F : Type*} {M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  [SimplyConnectedSpace M] {φ : RoughForm I M F 2}

variable (x : M) in
/-- The **integral of a closed two-form over the second homology** of a simply connected compact
manifold: the integral `TauCeti.sphereIntegralHom` of the form over `π₂(M, x)`, composed with the
inverse of the Hurewicz isomorphism `π₂(M, x) ≅ H₂(M; ℤ)`. It does not depend on `x`
(`TauCeti.homologySphereIntegralHom_eq`). -/
def homologySphereIntegralHom (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of M) →+
      F :=
  (sphereIntegralHom x hφ hdφ).comp
    (hurewiczAddEquiv (subsingleton_homotopyGroup_of_lt_two x)).symm.toAddMonoidHom

/-- **The integral over the Hurewicz class of a sphere.** The integral of a closed `C¹` two-form
over the Hurewicz class of a sphere `a ∈ π₂(M, y)`, at any base point `y`, is its integral over
`a`. -/
@[simp]
theorem homologySphereIntegralHom_hurewiczIntHom (x : M) (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) {y : M} (a : Additive (π_ 2 M y)) :
    homologySphereIntegralHom x hφ hdφ (hurewiczIntHom M y 1 a) = sphereIntegral φ y a.toMul := by
  -- Move the sphere to the base point `x`; neither its Hurewicz class nor its integral changes.
  obtain ⟨b, hb⟩ := (homotopyGroupEquivOfPath (PathConnectedSpace.somePath x y)).surjective a.toMul
  rw [homotopyGroupEquivOfPath_apply] at hb
  rw [← ofMul_toMul a, ← hb, hurewiczIntHom_homotopyGroupTransport, toMul_ofMul,
    sphereIntegral_homotopyGroupTransport hφ hdφ, homologySphereIntegralHom,
    AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    ← hurewiczAddEquiv_eq_hurewiczIntHom (subsingleton_homotopyGroup_of_lt_two x),
    AddEquiv.symm_apply_apply, sphereIntegralHom_apply, toMul_ofMul]

/-- **Independence of the base point.** The integral of a closed `C¹` two-form over `H₂(M; ℤ)`
does not depend on the base point at which it is defined. -/
theorem homologySphereIntegralHom_eq (x y : M) (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) :
    homologySphereIntegralHom x hφ hdφ = homologySphereIntegralHom y hφ hdφ := by
  ext z
  obtain ⟨a, rfl⟩ :=
    (hurewiczAddEquiv (subsingleton_homotopyGroup_of_lt_two (X := M) y)).surjective z
  rw [hurewiczAddEquiv_eq_hurewiczIntHom, homologySphereIntegralHom_hurewiczIntHom,
    homologySphereIntegralHom_hurewiczIntHom]

end TauCeti
