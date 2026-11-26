/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Chart
import TauCeti.Geometry.Manifold.ModelTransport.Diffeomorph

/-!
# The manifold structure of collar coordinates

The collar charts of `Boundary.Collar.Chart` express a manifold modeled on the Euclidean
half-space in tangential and inward-normal coordinates. This file proves that those charts have
`C^k` transition maps. Consequently, the charted space `TauCeti.collarChartedSpace n M` is a
manifold modeled on `(𝓡 n).prod (𝓡∂ 1)` whenever the original half-space charted space is a
`C^k` manifold.

This is the local product-manifold step towards the collar-neighbourhood theorem. It is
deliberately not the global collar theorem: a collar chart still has an arbitrary open target in
the product model, not a target of the form `V × [0, ε)`. The global step must shrink and patch
these local product coordinates along the entire boundary.

The collar charts follow every ambient chart with the inverse collar identification
(`TauCeti.collarChartedSpace_eq_chartedSpaceComp`), which is a `C^k` diffeomorphism from the
half-space onto the product model for every `k`, so the result is an instance of
`Diffeomorph.isManifold_chartedSpaceComp`.

## Main result

* `TauCeti.isManifold_collarChartedSpace`: the collar charted space is a `C^k` manifold over the
  product model.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Theorem 6.1.
* J. Lee, *Introduction to Smooth Manifolds*, Springer GTM 218, 2nd ed. (2013), Theorem 9.25.
-/

public section

noncomputable section

open Function Set Topology

open scoped Manifold ContDiff

namespace TauCeti

variable {n : ℕ} {k : WithTop ℕ∞} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

/-- The collar charts make a `C^k` manifold atlas for the product model
`(𝓡 n).prod (𝓡∂ 1)`. This is the given half-space manifold structure expressed in tangential and
inward-normal coordinates.

The charted-space argument is explicit in the conclusion because `M` already has its original
half-space charted-space instance. A consumer can install the result locally with
`letI := collarChartedSpace n M` followed by `letI := isManifold_collarChartedSpace`. -/
theorem isManifold_collarChartedSpace [IsManifold (𝓡∂ (n + 1)) k M] :
    @IsManifold ℝ _ _ _ _ _ _ ((𝓡 n).prod (𝓡∂ 1)) k M _
      (collarChartedSpace n M) := by
  -- The inverse collar identification, as a `C^k` diffeomorphism onto the product model charted
  -- over itself.
  let Φ : EuclideanHalfSpace (n + 1) ≃ₘ^k⟮𝓡∂ (n + 1), (𝓡 n).prod (𝓡∂ 1)⟯
      ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1) :=
    { toEquiv := (EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).symm.toEquiv
      contMDiff_toFun := EuclideanHalfSpace.contMDiff_collarDiffeomorph_symm_modelProd n
      contMDiff_invFun := EuclideanHalfSpace.contMDiff_collarDiffeomorph_modelProd n }
  rw [collarChartedSpace_eq_chartedSpaceComp]
  exact Φ.isManifold_chartedSpaceComp M

end TauCeti
