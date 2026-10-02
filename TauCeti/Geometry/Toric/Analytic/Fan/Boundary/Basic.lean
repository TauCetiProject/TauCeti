/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Ray
public import TauCeti.Geometry.Toric.Analytic.Fan.DenseTorus

/-!
# Boundary components of an analytic toric fan realization

For a nonempty regular fan, the orbit of the zero cone is the dense torus. Each ray of the fan
determines a closed invariant boundary component: the closure of its torus orbit. The
orbit--cone correspondence identifies this component with the union of the orbits indexed by
cones containing the ray.

These ray-indexed components form a finite family, and their union is exactly the complement of
the dense torus. On an affine chart, the component of a ray contained in the chart's cone is the
closure of the corresponding affine orbit; a ray not contained in the chart has empty preimage.
This is the intrinsic topological description underlying the later coordinate-hyperplane and
simple-normal-crossings descriptions.

## Main declarations

* `TauCeti.Toric.Fan.analyticBoundaryComponent`: the orbit closure attached to a fan ray.
* `TauCeti.Toric.Fan.analyticBoundaryComponent_eq_iUnion`: a boundary component is the union of
  the orbits of cones containing its ray.
* `TauCeti.Toric.Fan.preimage_analyticAffineChartι_analyticBoundaryComponent`: the component in
  an affine chart.
* `TauCeti.Toric.Fan.iUnion_analyticBoundaryComponent`: the union of the boundary components is
  the complement of the dense torus.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§3.1 and 4.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.2--3.3 and 4.1.
-/

public section

open Set Topology

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Phi : Fan i) (hPhi : Phi.IsRegular)

/-- The boundary component indexed by a ray is the closure of the corresponding torus orbit. -/
def analyticBoundaryComponent (rho : Phi.Ray) : Set (Phi.analyticRealization hPhi) :=
  closure (Phi.analyticConeOrbit hPhi rho.toCone)

/-- A boundary component is the closure of the orbit indexed by its ray. -/
theorem analyticBoundaryComponent_def (rho : Phi.Ray) :
    Phi.analyticBoundaryComponent hPhi rho =
      closure (Phi.analyticConeOrbit hPhi rho.toCone) := by
  apply congrArg closure
  rfl

/-- Every analytic boundary component is closed. -/
theorem isClosed_analyticBoundaryComponent (rho : Phi.Ray) :
    IsClosed (Phi.analyticBoundaryComponent hPhi rho) :=
  isClosed_closure

/-- A point in the orbit of `sigma` belongs to the component indexed by `rho` exactly when the
ray is a face of `sigma`. -/
theorem mem_analyticBoundaryComponent_iff {rho : Phi.Ray} {sigma : Phi.cones}
    {x : Phi.analyticRealization hPhi} (hx : x ∈ Phi.analyticConeOrbit hPhi sigma) :
    x ∈ Phi.analyticBoundaryComponent hPhi rho ↔ rho.toCone ≤ sigma := by
  simpa only [analyticBoundaryComponent] using
    (Phi.mem_closure_analyticConeOrbit_iff hPhi hx :
      x ∈ closure (Phi.analyticConeOrbit hPhi rho.toCone) ↔ rho.toCone ≤ sigma)

/-- Torus translation preserves every analytic boundary component. -/
@[simp]
theorem smul_mem_analyticBoundaryComponent_iff (rho : Phi.Ray) (t : ComplexTorus N)
    (x : Phi.analyticRealization hPhi) :
    t • x ∈ Phi.analyticBoundaryComponent hPhi rho ↔
      x ∈ Phi.analyticBoundaryComponent hPhi rho := by
  rw [analyticBoundaryComponent_def, analyticConeOrbit_eq_orbit]
  constructor
  · intro htx
    have hx := smul_closure_orbit_subset (t⁻¹)
      (Phi.analyticDistinguishedPoint hPhi rho.toCone) (Set.smul_mem_smul_set htx)
    simpa using hx
  · intro hx
    exact smul_closure_orbit_subset t _ (Set.smul_mem_smul_set hx)

/-- The component of a ray is the union of the orbits indexed by cones containing that ray. -/
theorem analyticBoundaryComponent_eq_iUnion (rho : Phi.Ray) :
    Phi.analyticBoundaryComponent hPhi rho =
      ⋃ sigma ∈ Set.Ici rho.toCone, Phi.analyticConeOrbit hPhi sigma := by
  exact Phi.closure_analyticConeOrbit hPhi rho.toCone

/-- In a chart whose cone contains `rho`, the preimage of the boundary component is the closure
of the affine orbit of `rho`, viewed as a face of the chart cone. -/
theorem preimage_analyticAffineChartι_analyticBoundaryComponent
    {rho : Phi.Ray} {sigma : Phi.cones}
    (h : rho.toCone ≤ sigma) :
    Phi.analyticAffineChartι hPhi sigma ⁻¹' Phi.analyticBoundaryComponent hPhi rho =
      @closure ((Phi.analyticAffineChartDiagram hPhi).obj sigma)
        ((Phi.analyticAffineChartDiagram hPhi).obj sigma).str
        (affineConeOrbit Phi.lattice
          (⟨rho.toCone.1, Phi.isFaceOf_of_le sigma.2 rho.toCone.2 h⟩ : sigma.1.Face)) := by
  let hι := Phi.isOpenEmbedding_analyticAffineChartι hPhi sigma
  rw [analyticBoundaryComponent,
    hι.isOpenMap.preimage_closure_eq_closure_preimage hι.continuous,
    Phi.preimage_analyticAffineChartι_analyticConeOrbit hPhi h]

/-- A boundary component has empty preimage in a chart whose cone does not contain its ray. -/
theorem preimage_analyticAffineChartι_analyticBoundaryComponent_of_not_le
    {rho : Phi.Ray} {sigma : Phi.cones}
    (h : ¬rho.toCone ≤ sigma) :
    Phi.analyticAffineChartι hPhi sigma ⁻¹' Phi.analyticBoundaryComponent hPhi rho = ∅ := by
  let hι := Phi.isOpenEmbedding_analyticAffineChartι hPhi sigma
  rw [analyticBoundaryComponent,
    hι.isOpenMap.preimage_closure_eq_closure_preimage hι.continuous,
    Phi.preimage_analyticAffineChartι_analyticConeOrbit_of_not_le hPhi h, closure_empty]

/-- The union of the ray-indexed boundary components is exactly the complement of the dense
torus. -/
theorem iUnion_analyticBoundaryComponent (hPhi0 : Nonempty Phi.cones) :
    (⋃ rho : Phi.Ray, Phi.analyticBoundaryComponent hPhi rho) =
      (Phi.analyticDenseTorus hPhi hPhi0)ᶜ := by
  ext x
  obtain ⟨sigma, hx⟩ := Phi.exists_mem_analyticConeOrbit hPhi x
  rw [Set.mem_iUnion, Set.mem_compl_iff,
    Phi.analyticDenseTorus_eq_analyticConeOrbit_bot hPhi sigma]
  let botCone : Phi.cones := ⟨⊥, Phi.bot_mem sigma.2⟩
  constructor
  · rintro ⟨rho, hrho⟩ hdense
    have hrhoLe := (Phi.mem_analyticBoundaryComponent_iff hPhi hx).1 hrho
    have hsigma : sigma = botCone :=
      Phi.eq_of_mem_analyticConeOrbit hPhi hx hdense
    have hrhoBot : rho.toCone ≤ botCone := hsigma ▸ hrhoLe
    have hbot : botCone ≤ rho.toCone := by
      -- Unwrap the inherited order on the fan's subtype of cones.
      change (⊥ : PointedCone ℝ V) ≤ rho.toCone.1
      exact bot_le
    apply rho.toCone_ne_bot
    exact congrArg Subtype.val (hrhoBot.antisymm hbot)
  · intro hdense
    have hsigma : sigma.1 ≠ ⊥ := by
      intro hsigma
      apply hdense
      have hsigmaBot : sigma = botCone := Subtype.ext hsigma
      simpa [hsigmaBot] using hx
    obtain ⟨rho, hrho⟩ := Phi.exists_ray_le_of_ne_bot sigma hsigma
    exact ⟨rho, (Phi.mem_analyticBoundaryComponent_iff hPhi hx).2 hrho⟩

end TauCeti.Toric.Fan
