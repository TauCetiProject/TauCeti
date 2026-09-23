/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.ProperAction
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Manifold
public import TauCeti.Geometry.Manifold.Instances.Quotient

/-!
# The free-locus quotient of a Fuchsian group

Let `Γ ≤ PSL(2, ℝ)` be a discrete subgroup. Its free locus `TauCeti.freeLocus Γ ℍ`, the set of
points of the upper half-plane with trivial stabilizer, is open and `Γ`-invariant, and `Γ` acts on
it freely, properly discontinuously and by biholomorphisms. The orbit space of the free locus is
therefore a Hausdorff, second countable Riemann surface, whose complex charts are pushed forward
along the orbit projection, and the orbit projection is a covering map and a local
biholomorphism.

The complex-manifold structure, Hausdorffness and second countability are found by instance
search, from `TauCeti.instIsManifoldQuotient`, Mathlib's
`t2Space_of_properlyDiscontinuousSMul_of_t2Space` and
`TauCeti.freeLocus.instSecondCountableTopologyQuotient`, and the covering property is
`TauCeti.isCoveringMap_quotientMk_freeLocus`. This file adds the local biholomorphism.

At a point with nontrivial stabilizer, an elliptic point, the orbit projection of the whole upper
half-plane is not a covering map; its local model there is the power map `u ↦ u ^ m` of
`TauCeti.rootsOfUnityBallQuotientHomeomorph`.

## Main declarations

* `Subgroup.isLocalDiffeomorph_quotientMk_freeLocus`: the orbit projection of the free locus is a
  local biholomorphism.

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

end Subgroup
