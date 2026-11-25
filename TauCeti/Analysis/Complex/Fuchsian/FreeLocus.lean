/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Covolume
public import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Finite
public import TauCeti.Analysis.Complex.Fuchsian.ProperAction
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Manifold
public import TauCeti.Geometry.Manifold.Instances.Quotient
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology

/-!
# The free-locus quotient of a Fuchsian group

Let `Γ ≤ PSL(2, ℝ)` be a discrete subgroup. Its free locus `TauCeti.freeLocus Γ ℍ`, the set of
points of the upper half-plane with trivial stabilizer, is open and `Γ`-invariant, and `Γ` acts on
it freely, properly discontinuously and by biholomorphisms. The orbit space of the free locus is
therefore a Hausdorff, second countable Riemann surface, whose complex charts are pushed forward
along the orbit projection, and the orbit projection is a covering map and a local
biholomorphism.

At a point with nontrivial stabilizer, an elliptic point, the orbit projection of the whole upper
half-plane is not a covering map; its local model there is the power map `u ↦ u ^ m` of
`TauCeti.rootsOfUnityBallQuotientHomeomorph`.

The elliptic points of a countable subgroup form a countable set, so the free locus is the upper
half-plane with countably many points removed, and is path connected. Hence the free-locus quotient
is path connected, and so is the regular part of the coarse quotient, the complement of its
elliptic orbits. Connectedness of the regular part is what makes a locally constant quantity on
it, such as a local sheet count of a covering, globally constant.

## Main declarations

* `Subgroup.isLocalDiffeomorph_quotientMk_freeLocus`: the orbit projection of the free locus is a
  local biholomorphism.
* `Subgroup.isPathConnected_freeLocus`: the free locus of a countable subgroup is path connected.
* `Subgroup.isPathConnected_compl_ellipticOrbits`: the coarse quotient with its elliptic orbits
  removed is path connected.

## References

* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter III §3.
-/

public section

open MulAction TauCeti

open scoped ContDiff Manifold MatrixGroups UpperHalfPlane

namespace Subgroup

variable (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]

/-- The orbit projection of the free locus of a discrete subgroup of `PSL(2, ℝ)` is a local
biholomorphism onto the free-locus quotient Riemann surface. -/
theorem isLocalDiffeomorph_quotientMk_freeLocus :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ∞ (Quotient.mk (orbitRel Γ (freeLocus Γ ℍ))) :=
  isLocalDiffeomorph_quotientMk

-- The free-locus quotient is a Hausdorff, second countable Riemann surface by instance search.
example : IsManifold 𝓘(ℂ) ∞ (orbitRel.Quotient Γ (freeLocus Γ ℍ)) := inferInstance
example : T2Space (orbitRel.Quotient Γ (freeLocus Γ ℍ)) := inferInstance
example : SecondCountableTopology (orbitRel.Quotient Γ (freeLocus Γ ℍ)) := inferInstance

omit [DiscreteTopology Γ] in
/-- **The free locus of a countable subgroup of `PSL(2, ℝ)` is path connected**: its complement,
the set of elliptic points, is countable. -/
theorem isPathConnected_freeLocus [Countable Γ] : IsPathConnected (freeLocus Γ ℍ : Set ℍ) := by
  simpa only [compl_compl] using (countable_compl_freeLocus Γ).isPathConnected_compl_upperHalfPlane

omit [DiscreteTopology Γ] in
/-- The free-locus quotient of a countable subgroup of `PSL(2, ℝ)` is path connected. -/
instance pathConnectedSpace_orbitRel_quotient_freeLocus [Countable Γ] :
    PathConnectedSpace (orbitRel.Quotient Γ (freeLocus Γ ℍ)) :=
  have := isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_freeLocus Γ)
  Quotient.instPathConnectedSpace

omit [DiscreteTopology Γ] in
/-- **The regular part of a Fuchsian quotient is path connected.** Removing the elliptic orbits
from the coarse quotient `Γ \ ℍ` of a countable subgroup leaves a path-connected space, the image
of the path-connected free locus. -/
theorem isPathConnected_compl_ellipticOrbits [Countable Γ] :
    IsPathConnected Γ.ellipticOrbitsᶜ := by
  rw [compl_ellipticOrbits]
  exact (isPathConnected_freeLocus Γ).image continuous_quotient_mk'

end Subgroup
