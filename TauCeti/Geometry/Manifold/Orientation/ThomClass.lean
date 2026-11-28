/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Topology.VectorBundle.Orientation.OfThomClass
import TauCeti.Geometry.Manifold.Topology

/-!
# Orientability and the integral Thom class of the tangent bundle

A manifold `M` of positive dimension `n + 1` is orientable exactly when its tangent bundle has an
integral Thom class `U ∈ Hⁿ⁺¹(TM, TM₀; ℤ)` (`TauCeti.orientable_iff_exists_isThomClass`). A manifold
is orientable exactly when its tangent bundle is
(`TauCeti.orientable_iff_nonempty_vectorBundleOrientation`), and over a locally path-connected
base, such as a manifold modelled on a real normed space, a vector bundle is orientable exactly
when it has an integral Thom class
(`TauCeti.nonempty_vectorBundleOrientation_iff_exists_isThomClass`).

So on a nonorientable manifold, such as an even-dimensional real projective space, the Thom
isomorphism `Hₖ(TM, TM₀; ℤ) ≅ Hₖ₋ₙ₋₁(M; ℤ)` with untwisted integral coefficients has no Thom class
to be built from: the integral Thom isomorphism of such a manifold needs coefficients twisted by
its orientation local system, while with coefficients in `ℤ/2` the tangent bundle has a Thom class
(`TauCeti.exists_isThomClass_of_two_eq_zero`).

## Main results

* `TauCeti.orientable_iff_exists_isThomClass`: a manifold is orientable exactly when its tangent
  bundle has an integral Thom class.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 and Theorem 10.4.
-/

public section

open Module

universe w

namespace TauCeti

variable {E H M : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

/-- **A manifold is orientable exactly when its tangent bundle has an integral Thom class.** For
a manifold of positive dimension `n + 1`, an orientation is the same as a class of
`Hⁿ⁺¹(TM, TM₀; ℤ)` restricting to a generator of the local cohomology of every tangent space. -/
theorem orientable_iff_exists_isThomClass {n : ℕ} (hE : finrank ℝ E = n + 1) :
    Orientable I M ↔ ∃ u : (thomPair E (TangentSpace I : M → Type w)).singularCohomology
      (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) (finrank ℝ E),
      IsThomClass E (TangentSpace I : M → Type w) u := by
  have := I.locallyPathConnectedSpace_of_chartedSpace M
  rw [orientable_iff_nonempty_vectorBundleOrientation,
    ← nonempty_vectorBundleOrientation_iff_exists_isThomClass hE]
  exact (VectorBundleOrientation.reindex (finCongr hE)).nonempty_congr

end TauCeti
