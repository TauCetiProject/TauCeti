/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Covering
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Pointed
public import TauCeti.AlgebraicTopology.UniversalCover.Covering
public import TauCeti.Geometry.Manifold.Riemannian.GeometricStructure.Basic
public import TauCeti.Geometry.Manifold.Riemannian.ModelGeometry.SimplyConnected

/-!
# The universal cover of a geometric manifold

A geometric structure presents a space as a free, properly discontinuous quotient of a Thurston
model space. All eight models are simply connected and locally path connected, so the quotient
projection is a universal covering map. This file strengthens the quotient-map characterization
to a quotient covering map and identifies the model with the based-path universal cover over
the base, matching a lift of any prescribed basepoint.

No manifold structure on the base is assumed: local path connectedness and semilocal simple
connectivity follow from the quotient presentation. The comparison homeomorphism respects the
projection, so it can transport covering-space constructions rather than merely compare the
underlying spaces.

## References

* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983), 401–487,
  Section 1.
* W. P. Thurston, *Three-Dimensional Geometry and Topology*, Vol. 1, Princeton University
  Press (1997), Section 3.4.

The covering and uniqueness arguments use Mathlib's `IsQuotientCoveringMap` and Tau Ceti's
`IsCoveringMap.exists_homeomorph_comp_eq_of_simplyConnectedSpace`.
-/

public section

open Topology

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] {G : ModelGeometry}

/-- A geometric structure is equivalently a quotient covering map from its model, with a group
of isometries acting freely and properly discontinuously as its fibre orbits. Since the model
is simply connected, this is a universal covering presentation. -/
theorem hasGeometricStructure_iff_exists_isQuotientCoveringMap :
    HasGeometricStructure M G ↔ ∃ Γ : Subgroup (Isom G.model G.Space),
      ProperlyDiscontinuousSMul Γ G.Space ∧
        ∃ p : G.Space → M, IsQuotientCoveringMap p Γ := by
  rw [hasGeometricStructure_iff_exists_isQuotientMap]
  constructor
  · rintro ⟨Γ, hΓ, hfree, p, hp, hfib⟩
    exact ⟨Γ, hΓ, p, hp.isQuotientCoveringMap_of_properlyDiscontinuousSMul
      (fun {x y} => hfib x y)⟩
  · rintro ⟨Γ, hΓ, p, hp⟩
    exact ⟨Γ, hΓ, hp.isCancelSMul, p, hp.toIsQuotientMap,
      fun x y => hp.apply_eq_iff_mem_orbit⟩

/-- The base of a geometric structure is locally path connected, in its given topology. -/
theorem HasGeometricStructure.locallyPathConnectedSpace (h : HasGeometricStructure M G) :
    LocallyPathConnectedSpace M := by
  obtain ⟨Γ, _, p, hp⟩ :=
    hasGeometricStructure_iff_exists_isQuotientCoveringMap.mp h
  exact hp.toIsQuotientMap.locallyPathConnectedSpace

/-- The base of a geometric structure is semilocally simply connected, so its based-path
universal cover is available without an additional topological hypothesis. -/
theorem HasGeometricStructure.semilocallySimplyConnectedSpace (h : HasGeometricStructure M G) :
    SemilocallySimplyConnectedSpace M := by
  obtain ⟨Γ, _, p, hp⟩ :=
    hasGeometricStructure_iff_exists_isQuotientCoveringMap.mp h
  exact .of_isCoveringMap hp.isCoveringMap hp.surjective

/-- A geometric structure admits a covering presentation identifying the model with the
based-path universal cover over the base. The homeomorphism matches a lift of the prescribed
basepoint with the constant-path lift and commutes with the covering projections. -/
theorem HasGeometricStructure.exists_homeomorph_universalCover (h : HasGeometricStructure M G)
    (x₀ : M) :
    ∃ Γ : Subgroup (Isom G.model G.Space),
      ProperlyDiscontinuousSMul Γ G.Space ∧
        ∃ p : G.Space → M, IsQuotientCoveringMap p Γ ∧
          ∃ x : G.Space, p x = x₀ ∧ ∃ e : G.Space ≃ₜ UniversalCover x₀,
            e x = UniversalCover.basepointLift x₀ ∧ UniversalCover.proj ∘ e = p := by
  have := h.locallyPathConnectedSpace
  have := h.semilocallySimplyConnectedSpace
  obtain ⟨Γ, hΓ, p, hp⟩ :=
    hasGeometricStructure_iff_exists_isQuotientCoveringMap.mp h
  obtain ⟨x, hx⟩ := hp.surjective x₀
  obtain ⟨e, he, hproj⟩ := hp.isCoveringMap.exists_homeomorph_comp_eq_of_simplyConnectedSpace
    (UniversalCover.isCoveringMap x₀) hx (UniversalCover.proj_basepointLift x₀)
  exact ⟨Γ, hΓ, p, hp, x, hx, e, he, hproj⟩

end TauCeti
