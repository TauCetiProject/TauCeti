/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Boundary.Basic

/-!
# Intersections of toric boundary components

For a regular fan, a collection of invariant boundary components has nonempty intersection
exactly when its rays lie in a common cone. Such a collection is precisely the ray set of a
unique cone, and the intersection is the closure of that cone's torus orbit. In particular,
the orbit closure of any cone is the intersection of the boundary components of its rays.

These formulas describe the incidence of the boundary components intrinsically, without
choosing coordinates. Together with their coordinate-hyperplane normal form, they identify
the boundary intersections with the toric orbit closures.

Empty collections and empty fans are allowed: an empty intersection is the whole realization,
and it is nonempty exactly when the fan is nonempty.

## Main declarations

* `TauCeti.Toric.Fan.iInter_analyticBoundaryComponent_eq_closure_analyticConeOrbit`: the
  intersection indexed by the rays of a cone is its orbit closure.
* `TauCeti.Toric.Fan.nonempty_iInter_analyticBoundaryComponent_iff`: boundary components meet
  exactly when their rays lie in a common cone.
* `TauCeti.Toric.Fan.existsUnique_iInter_analyticBoundaryComponent_eq_closure`: every nonempty
  boundary intersection is the orbit closure of the unique cone with the prescribed rays.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§2.1 and 3.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.2 and §4.1.
-/

public section

open Set Topology

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Phi : Fan i) (hPhi : Phi.IsRegular)

/-- The orbit closure of a cone is the intersection of the boundary components indexed by
its rays. For the zero cone this is the whole realization. -/
theorem iInter_analyticBoundaryComponent_eq_closure_analyticConeOrbit (sigma : Phi.cones) :
    (⋂ rho : Phi.Ray, ⋂ (_ : rho.toCone ≤ sigma), Phi.analyticBoundaryComponent hPhi rho) =
      closure (Phi.analyticConeOrbit hPhi sigma) := by
  ext x
  obtain ⟨tau, hx⟩ := Phi.exists_mem_analyticConeOrbit hPhi x
  simp only [mem_iInter, Phi.mem_analyticBoundaryComponent_iff hPhi hx,
    Phi.mem_closure_analyticConeOrbit_iff hPhi hx]
  exact (Phi.le_iff_forall_ray_le).symm

/-- An intersection of boundary components is the union of the torus orbits of cones
containing all its indexing rays. -/
theorem iInter_analyticBoundaryComponent_eq_iUnion (S : Set Phi.Ray) :
    (⋂ rho ∈ S, Phi.analyticBoundaryComponent hPhi rho) =
      ⋃ sigma : Phi.cones, ⋃ (_ : ∀ rho ∈ S, rho.toCone ≤ sigma),
        Phi.analyticConeOrbit hPhi sigma := by
  ext x
  obtain ⟨sigma, hx⟩ := Phi.exists_mem_analyticConeOrbit hPhi x
  simp only [mem_iInter, mem_iUnion, Phi.mem_analyticBoundaryComponent_iff hPhi hx]
  refine ⟨fun h ↦ ⟨sigma, h, hx⟩, fun ⟨tau, h, hy⟩ ↦ ?_⟩
  exact Phi.eq_of_mem_analyticConeOrbit hPhi hy hx ▸ h

/-- Boundary components meet exactly when their rays are contained in a common cone of the
fan. This criterion applies also to the empty collection and the empty fan. -/
theorem nonempty_iInter_analyticBoundaryComponent_iff (S : Set Phi.Ray) :
    (⋂ rho ∈ S, Phi.analyticBoundaryComponent hPhi rho).Nonempty ↔
      ∃ sigma : Phi.cones, ∀ rho ∈ S, rho.toCone ≤ sigma := by
  rw [Phi.iInter_analyticBoundaryComponent_eq_iUnion hPhi S]
  simp only [nonempty_iUnion]
  constructor
  · rintro ⟨sigma, h, _⟩
    exact ⟨sigma, h⟩
  · rintro ⟨sigma, h⟩
    exact ⟨sigma, h, Phi.analyticDistinguishedPoint hPhi sigma,
      Phi.analyticDistinguishedPoint_mem_analyticConeOrbit hPhi sigma⟩

/-- Every nonempty intersection of boundary components is the orbit closure of the unique
cone whose rays are exactly the indexing collection. -/
theorem existsUnique_iInter_analyticBoundaryComponent_eq_closure (S : Set Phi.Ray)
    (hS : (⋂ rho ∈ S, Phi.analyticBoundaryComponent hPhi rho).Nonempty) :
    ∃! sigma : Phi.cones,
      (∀ rho : Phi.Ray, rho.toCone ≤ sigma ↔ rho ∈ S) ∧
        (⋂ rho ∈ S, Phi.analyticBoundaryComponent hPhi rho) =
          closure (Phi.analyticConeOrbit hPhi sigma) := by
  obtain ⟨tau, hTau⟩ := (Phi.nonempty_iInter_analyticBoundaryComponent_iff hPhi S).mp hS
  obtain ⟨sigma, -, hSigma⟩ :=
    Phi.exists_cone_rays_eq (((isRegular_iff.mp hPhi) tau.1 tau.2).isSimplicial Phi.lattice) hTau
  have hEq : (⋂ rho ∈ S, Phi.analyticBoundaryComponent hPhi rho) =
      closure (Phi.analyticConeOrbit hPhi sigma) := by
    rw [← Phi.iInter_analyticBoundaryComponent_eq_closure_analyticConeOrbit hPhi sigma]
    simp only [hSigma]
  refine ⟨sigma, ⟨hSigma, hEq⟩, fun upsilon h ↦ ?_⟩
  apply le_antisymm
  · exact Phi.le_iff_forall_ray_le.mpr fun rho hrho ↦ (hSigma rho).mpr ((h.1 rho).mp hrho)
  · exact Phi.le_iff_forall_ray_le.mpr fun rho hrho ↦ (h.1 rho).mpr ((hSigma rho).mp hrho)

end TauCeti.Toric.Fan
