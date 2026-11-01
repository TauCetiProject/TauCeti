/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.Descent

/-!
# `C^n` coordinate morphisms of vector bundle cores

Let `Z` and `W` be vector bundle cores over a manifold `B` with `C^n` transition functions
(`VectorBundleCore.IsContMDiff`). A section of Mathlib's Hom bundle between them is `C^n` exactly
when it is `C^n` in every pair of a source chart and a target chart, on their common domain, with
chart expressions `VectorBundleCore.inChartCoordinates`
(`VectorBundleCore.contMDiff_hom_bundle_iff_forall_contMDiffOn`).

For a coordinate morphism `a : VectorBundleCore.CoordinateHom Z W`, these chart expressions of its
descended fibre maps are its chart operators (`VectorBundleCore.CoordinateHom.operator_eq`).
Hence `C^n` chart operators glue to a `C^n` map of total spaces, and conversely for a
finite-dimensional source model. A coordinate morphism is an isomorphism of cocycles when its
fibre maps are invertible. For a finite-dimensional source model, such isomorphisms with `C^n`
chart operators are exactly the coordinate morphisms realized by `C^n` diffeomorphisms of total
spaces (`VectorBundleCore.CoordinateHom.exists_diffeomorph_iff`). Over `ℂ` with `n = ∞` this
identifies holomorphic isomorphisms of transition cocycles of finite rank, given by holomorphic
changes of frame on each chart, with holomorphic bundle equivalences. In the rank-one case these
are the families of nowhere-vanishing holomorphic functions relating two line-bundle cocycles.

This specializes `TauCeti.exists_bundleDiffeomorph_iff`, whose diffeomorphism is
`TauCeti.bundleDiffeomorph`, built from Mathlib's `ContMDiff.clm_bundle_apply` and fibrewise
inversion of Hom-bundle sections.

## References

* Norman Steenrod, *The Topology of Fibre Bundles*, Part I, §2--3 (coordinate transformations
  and equivalence of coordinate bundles).
* Daniel Huybrechts, *Complex Geometry: An Introduction*, §2.2 (holomorphic vector bundles from
  cocycles).
-/

public section

open Bundle Set
open scoped Manifold

namespace VectorBundleCore

variable {𝕜 B F G EB HB ι κ : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : WithTop ℕ∞} {Z : VectorBundleCore 𝕜 B F ι} {W : VectorBundleCore 𝕜 B G κ}
  [Z.IsContMDiff IB n] [W.IsContMDiff IB n]

namespace CoordinateHom

/-- A coordinate morphism with `C^n` chart operators induces a `C^n` map of total spaces. -/
theorem contMDiff_totalSpaceMap (a : CoordinateHom Z W)
    (ha : ∀ i j, ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] G) n
      (fun x ↦ Z.inChartCoordinates W i j x (a.fiberMap x)) (Z.baseSet i ∩ W.baseSet j)) :
    ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, G)) n a.totalSpaceMap := by
  rw [totalSpaceMap_def]
  exact ((contMDiff_hom_bundle_iff_forall_contMDiffOn.2 ha).comp
    (contMDiff_proj Z.Fiber)).clm_bundle_apply contMDiff_id

/-- For a finite-dimensional source model, a coordinate morphism induces a `C^n` map of total
spaces exactly when its chart operators are `C^n`. -/
theorem contMDiff_totalSpaceMap_iff [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    (a : CoordinateHom Z W) :
    ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, G)) n a.totalSpaceMap ↔
      ∀ i j, ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] G) n
        (fun x ↦ Z.inChartCoordinates W i j x (a.fiberMap x)) (Z.baseSet i ∩ W.baseSet j) := by
  rw [totalSpaceMap_def]
  exact (TauCeti.contMDiff_hom_bundle_iff (E₁ := Z.Fiber) (E₂ := W.Fiber) a.fiberMap).symm.trans
    contMDiff_hom_bundle_iff_forall_contMDiffOn

/-- **Cocycle isomorphisms are bundle equivalences.** For a finite-dimensional source model, a
coordinate morphism is realized by a `C^n` diffeomorphism of total spaces exactly when its chart
operators are `C^n` and its fibre maps are invertible. -/
theorem exists_diffeomorph_iff [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    (a : CoordinateHom Z W) :
    (∃ Φ : Z.TotalSpace ≃ₘ^n⟮IB.prod 𝓘(𝕜, F), IB.prod 𝓘(𝕜, G)⟯ W.TotalSpace,
        ⇑Φ = a.totalSpaceMap) ↔
      (∀ i j, ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] G) n
        (fun x ↦ Z.inChartCoordinates W i j x (a.fiberMap x)) (Z.baseSet i ∩ W.baseSet j)) ∧
      ∀ x, (a.fiberMap x).IsInvertible := by
  rw [totalSpaceMap_def]
  exact (TauCeti.exists_bundleDiffeomorph_iff (E₁ := Z.Fiber) (E₂ := W.Fiber) a.fiberMap).trans
    (and_congr_left' contMDiff_hom_bundle_iff_forall_contMDiffOn)

end CoordinateHom

end VectorBundleCore
