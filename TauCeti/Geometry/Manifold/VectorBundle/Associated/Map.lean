/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Associated.Map
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Smooth linear intertwiners on associated bundles

A continuous linear intertwiner defines a smooth section of the native Hom bundle between
associated vector bundles. Its coordinate in any common principal chart is the constant model
operator. Thus the fibrewise linear comparison is smooth as an operator-valued section, not
merely after evaluation on each fixed vector.

The statements compare the specified associated charts, without requiring smooth principal
transitions or finite-dimensional fibres. When those transitions and actions are smooth, the
associated vector bundles themselves are smooth by the separate associated-bundle construction.

## References

* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*,
  Springer, 1993, §§10.7 and 10.9.
-/

public noncomputable section

open Bundle TauCeti TauCeti.AssociatedBundle
open scoped Manifold ContDiff Topology

namespace ContinuousLinearMap

variable {𝕜₀ 𝕜 B G F F' : Type*}
  [NontriviallyNormedField 𝕜₀] [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜₀ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜₀ EB HB}
  [TopologicalSpace B] [ChartedSpace HB B]
  [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [DistribMulAction G F] [SMulCommClass G 𝕜 F] [ContinuousSMul G F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [DistribMulAction G F'] [SMulCommClass G 𝕜 F'] [ContinuousSMul G F']
  [NormedSpace 𝕜₀ (F →L[𝕜] F')]
  [VectorBundle 𝕜 F (AssociatedBundle G P F)]
  [VectorBundle 𝕜 F' (AssociatedBundle G P F')]

/-- An intertwiner gives a smooth operator-valued section of the native Hom bundle. This holds
at any differentiability order because its local operator coordinate is constant. The base field
may differ from the representation field, allowing complex intertwiners over real manifolds. -/
theorem contMDiff_associatedBundleMap {n : ℕ∞ω} (f : F →L[𝕜] F')
    (hf : ∀ (g : G) v, f (g • v) = g • f v) :
    ContMDiff IB (IB.prod 𝓘(𝕜₀, F →L[𝕜] F')) n
      (fun b ↦ TotalSpace.mk' (F →L[𝕜] F') b
        (f.associatedBundleMap (P := P) hf b)) := by
  refine contMDiff_hom_bundle_of_inCoordinates_eq_const (c := fun _ ↦ f) ?_
  intro a b hb _
  exact inCoordinates_associatedBundleMap f hf (by simpa only [baseSet_trivializationAt] using hb)

end ContinuousLinearMap
