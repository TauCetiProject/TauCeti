/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Orbit.Basic
public import TauCeti.Geometry.Toric.Analytic.Fan.Subfan.Basic

/-!
# Orbits in open subfans

The invariant open subset associated to a face-closed subfan contains exactly the torus orbits
indexed by cones of that subfan. This characterizes the image of the open-subfan embedding in
terms of the orbit--cone correspondence.

## References

* W. Fulton, *Introduction to Toric Varieties*, §2.1 and §2.4.
-/

public section

open Set

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Phi : Fan i) (hPhi : Phi.IsRegular)
  (S : Set (PointedCone ℝ V)) (hS : S ⊆ Phi.cones)
  (hface : ∀ ⦃sigma tau⦄, sigma ∈ S → tau.IsFaceOf sigma → tau ∈ S)

/-- A point in the orbit of `sigma` lies in the invariant open subset associated to a subfan
exactly when `sigma` is a cone of that subfan. -/
theorem mem_range_subfanAnalyticMap_iff {sigma : Phi.cones}
    {x : Phi.analyticRealization hPhi} (hx : x ∈ Phi.analyticConeOrbit hPhi sigma) :
    x ∈ range (Phi.subfanAnalyticMap hPhi S hS hface) ↔ sigma.1 ∈ S := by
  rw [Phi.range_subfanAnalyticMap hPhi S hS hface, mem_iUnion]
  constructor
  · rintro ⟨tau, h_tau⟩
    have hle := (Phi.mem_range_analyticAffineChartι_iff hPhi hx).mp h_tau
    exact hface (by simpa only [subfan_cones] using tau.2)
      (Phi.isFaceOf_of_le (hS (by simpa only [subfan_cones] using tau.2)) sigma.2 hle)
  · intro h_sigma
    let sigma' : (Phi.subfan S hS hface).cones :=
      ⟨sigma.1, by simpa only [subfan_cones] using h_sigma⟩
    exact ⟨sigma', (Phi.mem_range_analyticAffineChartι_iff hPhi hx).2 le_rfl⟩

end TauCeti.Toric.Fan
