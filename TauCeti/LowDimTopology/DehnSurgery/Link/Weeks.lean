/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.KnotTheory.SmoothLink.Whitehead
public import TauCeti.LowDimTopology.DehnSurgery.Link.Surgery
public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Orientation

/-!
# The Weeks manifold

The **Weeks manifold** is the closed orientable hyperbolic `3`-manifold of smallest volume. It is
a Dehn surgery on the Whitehead link with coefficients `5` and `5 / 2` (Weeks; Hodgson, Meyerhoff
and Weeks). This file makes that surgery description the definition: a space `Y` is a Weeks
manifold (`TauCeti.IsWeeksManifold Y`) when it is a Dehn filling of the exterior of the Whitehead
link `TauCeti.whiteheadLink` in the unit sphere `S³` of `ℝ⁴` along the surgery slopes of
coefficients `5` on the unknotted component `0` and `5 / 2` on the Whitehead curve, component `1`
(`TauCeti.IsSolidTorusLinkNeighborhood.surgerySlope`).

Surgery coefficients are read in the preferred framing of each component, and their sign depends
on the orientation of the solid torus neighbourhoods `Φ i` of the components: changing the
orientation of `Φ i` changes the coefficient `r` into `-r`, and the Whitehead link is not
isotopic to its mirror image, so the surgeries with coefficients `5, 5 / 2` and `-5, -5 / 2` are
different manifolds. The definition therefore asks the neighbourhoods to preserve orientation at
their core points (`TauCeti.IsOrientationPreservingAtCore`), for the orientation of `S³` as the
boundary of the unit ball of `ℝ⁴` with its standard orientation, so that the coefficients follow
Rolfsen's conventions. With these conventions the filling with coefficients `5, 5 / 2` of the
link `TauCeti.whiteheadLink` is the Weeks manifold: a numerical computation of hyperbolic volumes
(SnapPy, from a diagram of the explicit parametrization of the link) gives `0.9427…`, the volume
of the Weeks manifold, for it, against `3.0524…` for the coefficients `-5, -5 / 2`. In the
diagram `5²₁` of SnapPy's link table, which is the mirror image of this link, the Weeks manifold
is the surgery with coefficients `-5, -5 / 2`.

Up to homeomorphism the filling does not depend on the choice of the neighbourhoods, which is
classical but not formalized here; the definition asks for some choice. Being a Weeks manifold
is a topological property: it is invariant under homeomorphisms
(`TauCeti.isWeeksManifold_congr`). Existence of the filling is not proved here.

## Main definitions

* `TauCeti.IsWeeksManifold Y`: `Y` is the surgery on the Whitehead link with coefficients `5` and
  `5 / 2`.

## Main results

* `TauCeti.isWeeksManifold_iff`: the definition of `TauCeti.IsWeeksManifold`, restated.
* `TauCeti.IsWeeksManifold.intro`: a filling of the exterior of the Whitehead link along these
  slopes, for orientation-preserving neighbourhoods, is a Weeks manifold.
* `TauCeti.IsWeeksManifold.of_homeomorph`, `TauCeti.isWeeksManifold_congr`: being a Weeks
  manifold is invariant under homeomorphisms.

## References

* J. Weeks, *Hyperbolic structures on three-manifolds*, Ph.D. thesis, Princeton University
  (1985).
* C. D. Hodgson, R. Meyerhoff, J. R. Weeks, *Surgeries on the Whitehead link yield geometrically
  similar manifolds*, in *Topology '90*, de Gruyter (1992), 195–206.
* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 9, Sections 9F and 9G
  (surgery on a link, with the coefficient of each component read in its preferred framing).
* M. Culler, N. M. Dunfield, M. Goerner, J. R. Weeks, *SnapPy*, a computer program for studying
  the geometry and topology of 3-manifolds, http://snappy.computop.org.
-/

public section

noncomputable section

open Metric

namespace TauCeti

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

/-- A space `Y` is a **Weeks manifold** when it is the Dehn surgery on the Whitehead link
`TauCeti.whiteheadLink` in `S³` with coefficient `5` on its unknotted component `0` and `5 / 2` on
the Whitehead curve, its component `1`: for some solid torus neighbourhoods `Φ i` of the two
components with disjoint images, each preserving orientation at its core point for the standard
orientation of `ℝ⁴`, `Y` is a Dehn filling of the link exterior along the surgery slopes with
these coefficients, read in the preferred framing of each component. -/
def IsWeeksManifold (Y : Type*) [TopologicalSpace Y] : Prop :=
  ∃ (Φ : Fin 2 → SolidTorus → sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (h : IsSolidTorusLinkNeighborhood (fun i ↦ whiteheadLink i) Φ),
    (∀ i, IsOrientationPreservingAtCore (Φ i)
      (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.orientation) ∧
    Nonempty (LinkDehnFilling h
      (h.surgerySlope (isZero_reducedSingularHomologyFunctor_one_sphere_euclideanSpace_fin_four _)
        (isZero_reducedSingularHomologyFunctor_two_sphere_euclideanSpace_fin_four _)
        ![((5 : ℚ) : OnePoint ℚ), ((5 / 2 : ℚ) : OnePoint ℚ)]) Y)

variable {Y : Type*} [TopologicalSpace Y] {Y' : Type*} [TopologicalSpace Y']

/-- `Y` is a Weeks manifold exactly when, for some solid torus neighbourhoods of the components of
the Whitehead link preserving orientation at their core points, `Y` is a Dehn filling of the link
exterior along the surgery slopes of coefficients `5` and `5 / 2`. -/
theorem isWeeksManifold_iff : IsWeeksManifold Y ↔
    ∃ (Φ : Fin 2 → SolidTorus → sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
      (h : IsSolidTorusLinkNeighborhood (fun i ↦ whiteheadLink i) Φ),
      (∀ i, IsOrientationPreservingAtCore (Φ i)
        (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.orientation) ∧
      Nonempty (LinkDehnFilling h
        (h.surgerySlope (isZero_reducedSingularHomologyFunctor_one_sphere_euclideanSpace_fin_four _)
          (isZero_reducedSingularHomologyFunctor_two_sphere_euclideanSpace_fin_four _)
          ![((5 : ℚ) : OnePoint ℚ), ((5 / 2 : ℚ) : OnePoint ℚ)]) Y) :=
  Iff.rfl

/-- A Dehn filling of the exterior of the Whitehead link along the surgery slopes of coefficients
`5` and `5 / 2`, for solid torus neighbourhoods preserving orientation at their core points, is a
Weeks manifold. -/
theorem IsWeeksManifold.intro
    {Φ : Fin 2 → SolidTorus → sphere (0 : EuclideanSpace ℝ (Fin 4)) 1}
    {h : IsSolidTorusLinkNeighborhood (fun i ↦ whiteheadLink i) Φ}
    (hΦ : ∀ i, IsOrientationPreservingAtCore (Φ i)
      (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.orientation)
    (F : LinkDehnFilling h
      (h.surgerySlope (isZero_reducedSingularHomologyFunctor_one_sphere_euclideanSpace_fin_four _)
        (isZero_reducedSingularHomologyFunctor_two_sphere_euclideanSpace_fin_four _)
        ![((5 : ℚ) : OnePoint ℚ), ((5 / 2 : ℚ) : OnePoint ℚ)]) Y) :
    IsWeeksManifold Y :=
  isWeeksManifold_iff.2 ⟨Φ, h, hΦ, ⟨F⟩⟩

/-- A space homeomorphic to a Weeks manifold is a Weeks manifold: the Dehn filling is carried
along the homeomorphism. -/
theorem IsWeeksManifold.of_homeomorph (hY : IsWeeksManifold Y) (e : Y ≃ₜ Y') :
    IsWeeksManifold Y' := by
  obtain ⟨Φ, h, hΦ, ⟨F⟩⟩ := isWeeksManifold_iff.1 hY
  exact .intro hΦ (F.transHomeomorph e)

/-- **Being a Weeks manifold is a topological property.** -/
theorem isWeeksManifold_congr (e : Y ≃ₜ Y') : IsWeeksManifold Y ↔ IsWeeksManifold Y' :=
  ⟨fun hY ↦ hY.of_homeomorph e, fun hY ↦ hY.of_homeomorph e.symm⟩

end TauCeti
