/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Boundary.Basic
public import TauCeti.Geometry.Toric.Analytic.Fan.Map.Equiv
public import TauCeti.Geometry.Toric.Analytic.Fan.Map.Orbit

/-!
# Naturality of toric boundary components

A fan equivalence transports the ray-indexed boundary components by its induced
biholomorphism. Passing to an open subfan restricts each retained component to the
corresponding component of the subfan, while a component whose ray is omitted has empty
preimage. Thus the intrinsic boundary family is compatible with toric isomorphisms and
restriction to invariant open subspaces, including the empty subfan.

The statements use the canonical maps of analytic realizations. The ray correspondence is
`FanEquiv.rayEquiv` for isomorphisms and `Fan.subfanRayEmbedding` for open subfans.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§2.1 and 3.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.2--3.3 and 4.1.
-/

public section

open CategoryTheory Set

namespace TauCeti.Toric

universe u

variable {N N' V V' : Type u} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Phi : Fan i} {Psi : Fan i'}

namespace FanHom

/-- On a source orbit, membership of its image in a target boundary component is exactly
containment of the target ray in the least target cone. -/
theorem analyticMap_mem_analyticBoundaryComponent_iff (f : FanHom Phi Psi)
    (hPhi : Phi.IsRegular) (hPsi : Psi.IsRegular) {rho : Psi.Ray} {sigma : Phi.cones}
    {x : Phi.analyticRealization hPhi} (hx : x ∈ Phi.analyticConeOrbit hPhi sigma) :
    f.analyticMap hPhi hPsi x ∈ Psi.analyticBoundaryComponent hPsi rho ↔
      rho.toCone.1 ≤ f.leastCone sigma.2 :=
  (Psi.mem_analyticBoundaryComponent_iff hPsi
    (f.mapsTo_analyticConeOrbit hPhi hPsi sigma hx)).trans Subtype.coe_le_coe.symm

end FanHom

namespace FanEquiv

variable (e : FanEquiv Phi Psi) (hPhi : Phi.IsRegular) (hPsi : Psi.IsRegular)

/-- The biholomorphism induced by a fan equivalence preserves membership in the corresponding
ray-indexed boundary components. -/
@[simp]
theorem analyticMap_mem_analyticBoundaryComponent_iff (rho : Phi.Ray)
    (x : Phi.analyticRealization hPhi) :
    e.toFanHom.analyticMap hPhi hPsi x ∈ Psi.analyticBoundaryComponent hPsi (e.rayEquiv rho) ↔
      x ∈ Phi.analyticBoundaryComponent hPhi rho := by
  obtain ⟨sigma, hx⟩ := Phi.exists_mem_analyticConeOrbit hPhi x
  rw [e.toFanHom.analyticMap_mem_analyticBoundaryComponent_iff hPhi hPsi hx,
    e.toFanHom_leastCone, Phi.mem_analyticBoundaryComponent_iff hPhi hx,
    toCone_rayEquiv, Subtype.coe_le_coe]
  exact e.coneEquiv.le_iff_le

/-- Pullback along a fan isomorphism gives the component indexed by the original ray. -/
@[simp]
theorem preimage_analyticMap_analyticBoundaryComponent (rho : Phi.Ray) :
    e.toFanHom.analyticMap hPhi hPsi ⁻¹'
        Psi.analyticBoundaryComponent hPsi (e.rayEquiv rho) =
      Phi.analyticBoundaryComponent hPhi rho := by
  ext x
  exact e.analyticMap_mem_analyticBoundaryComponent_iff hPhi hPsi rho x

/-- The biholomorphism induced by a fan equivalence carries each boundary component onto the
component indexed by the transported ray. -/
theorem image_analyticMap_analyticBoundaryComponent (rho : Phi.Ray) :
    e.toFanHom.analyticMap hPhi hPsi '' Phi.analyticBoundaryComponent hPhi rho =
      Psi.analyticBoundaryComponent hPsi (e.rayEquiv rho) := by
  have hbij := ConcreteCategory.bijective_of_isIso (e.analyticIso hPhi hPsi).hom
  rw [analyticIso_hom] at hbij
  exact ((Set.preimage_eq_iff_eq_image hbij).mp
    (e.preimage_analyticMap_analyticBoundaryComponent hPhi hPsi rho)).symm

end FanEquiv

namespace Fan

variable (Phi) (hPhi : Phi.IsRegular) (S : Set (PointedCone ℝ V)) (hS : S ⊆ Phi.cones)
  (hface : ∀ ⦃sigma tau⦄, sigma ∈ S → tau.IsFaceOf sigma → tau ∈ S)

/-- On an orbit of an open subfan, membership of its image in an ambient boundary component is
exactly containment of the ambient ray in the orbit's cone. -/
theorem subfanAnalyticMap_mem_analyticBoundaryComponent_iff (rho : Phi.Ray)
    {sigma : (Phi.subfan S hS hface).cones}
    {x : (Phi.subfan S hS hface).analyticRealization (hPhi.subfan S hS hface)}
    (hx : x ∈ (Phi.subfan S hS hface).analyticConeOrbit (hPhi.subfan S hS hface) sigma) :
    Phi.subfanAnalyticMap hPhi S hS hface x ∈ Phi.analyticBoundaryComponent hPhi rho ↔
      rho.toCone.1 ≤ sigma.1 := by
  simpa only [FanHom.analyticMap_subfanInclusion, subfanInclusion_leastCone] using
    (Phi.subfanInclusion S hS hface).analyticMap_mem_analyticBoundaryComponent_iff
      (hPhi.subfan S hS hface) hPhi hx

/-- The pullback of a retained boundary component is the corresponding component of the open
subfan. -/
@[simp]
theorem preimage_subfanAnalyticMap_analyticBoundaryComponent
    (rho : (Phi.subfan S hS hface).Ray) :
    Phi.subfanAnalyticMap hPhi S hS hface ⁻¹'
        Phi.analyticBoundaryComponent hPhi (Phi.subfanRayEmbedding S hS hface rho) =
      (Phi.subfan S hS hface).analyticBoundaryComponent (hPhi.subfan S hS hface) rho := by
  ext x
  obtain ⟨sigma, hx⟩ := (Phi.subfan S hS hface).exists_mem_analyticConeOrbit
    (hPhi.subfan S hS hface) x
  rw [mem_preimage, Phi.subfanAnalyticMap_mem_analyticBoundaryComponent_iff hPhi S hS hface _ hx,
    (Phi.subfan S hS hface).mem_analyticBoundaryComponent_iff (hPhi.subfan S hS hface) hx,
    ← Subtype.coe_le_coe, toCone_subfanRayEmbedding]

/-- A boundary component whose ray is omitted from an open subfan has empty preimage. -/
@[simp]
theorem preimage_subfanAnalyticMap_analyticBoundaryComponent_of_notMem
    (rho : Phi.Ray) (hrho : rho.toCone.1 ∉ S) :
    Phi.subfanAnalyticMap hPhi S hS hface ⁻¹' Phi.analyticBoundaryComponent hPhi rho = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨sigma, hxsigma⟩ := (Phi.subfan S hS hface).exists_mem_analyticConeOrbit
    (hPhi.subfan S hS hface) x
  have hle := (Phi.subfanAnalyticMap_mem_analyticBoundaryComponent_iff
    hPhi S hS hface rho hxsigma).mp hx
  exact hrho (hface (by simpa only [subfan_cones] using sigma.2)
    (Phi.isFaceOf_of_le (hS (by simpa only [subfan_cones] using sigma.2)) rho.toCone.2 hle))

/-- A component of an open subfan maps precisely onto the trace of the ambient component on
the open image of the subfan realization. -/
theorem image_subfanAnalyticMap_analyticBoundaryComponent_eq_inter_range
    (rho : (Phi.subfan S hS hface).Ray) :
    Phi.subfanAnalyticMap hPhi S hS hface ''
        (Phi.subfan S hS hface).analyticBoundaryComponent (hPhi.subfan S hS hface) rho =
      Phi.analyticBoundaryComponent hPhi (Phi.subfanRayEmbedding S hS hface rho) ∩
        range (Phi.subfanAnalyticMap hPhi S hS hface) := by
  rw [← Phi.preimage_subfanAnalyticMap_analyticBoundaryComponent hPhi S hS hface rho]
  exact image_preimage_eq_inter_range

end Fan

end TauCeti.Toric
