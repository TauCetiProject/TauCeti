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
(`VectorBundleCore.contMDiff_hom_bundle_iff_forall_contMDiffOn`). This is the `C^n` counterpart of
`VectorBundleCore.continuous_hom_bundle_iff_forall_continuousOn`.

For a coordinate morphism `a : VectorBundleCore.CoordinateHom Z W`, these chart expressions of its
descended fibre maps are its chart operators (`VectorBundleCore.CoordinateHom.operator_eq`).
Hence `C^n` chart operators glue to a `C^n` map of total spaces, and conversely for a
finite-dimensional source model. A coordinate morphism is an isomorphism of cocycles when its
fibre maps are invertible. Such isomorphisms with `C^n` chart operators are exactly the
coordinate morphisms realized by `C^n` diffeomorphisms of total spaces
(`VectorBundleCore.CoordinateHom.exists_diffeomorph_iff`). Over `ℂ` with `n = ∞` this identifies
holomorphic isomorphisms of transition cocycles, given by holomorphic changes of frame on each
chart, with holomorphic bundle equivalences. In the rank-one case these are the families of
nowhere-vanishing holomorphic functions relating two line-bundle cocycles.

The diffeomorphism is `TauCeti.bundleDiffeomorph`, built from Mathlib's
`ContMDiff.clm_bundle_apply` and fibrewise inversion of Hom-bundle sections.

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

/-- On the common domain of a source chart and a target chart, a section of the Hom bundle
between two cores is `C^n` exactly when its expression in those charts is. -/
theorem contMDiffOn_hom_bundle_iff_inChartCoordinates {f : B → F →L[𝕜] G} (i : ι) (j : κ) :
    ContMDiffOn IB (IB.prod 𝓘(𝕜, F →L[𝕜] G)) n
        (fun x ↦ TotalSpace.mk' (F →L[𝕜] G) (E := fun y ↦ Z.Fiber y →L[𝕜] W.Fiber y) x (f x))
        (Z.baseSet i ∩ W.baseSet j) ↔
      ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] G) n (fun x ↦ Z.inChartCoordinates W i j x (f x))
        (Z.baseSet i ∩ W.baseSet j) := by
  have : MemTrivializationAtlas (Z.localTriv i) := ⟨⟨i, rfl⟩⟩
  have : MemTrivializationAtlas (W.localTriv j) := ⟨⟨j, rfl⟩⟩
  -- Read the section in the Hom-bundle trivialization built from the two fixed charts.
  let e := (Z.localTriv i).continuousLinearMap (RingHom.id 𝕜) (W.localTriv j)
  refine e.contMDiffOn_section_baseSet_iff.trans (contMDiffOn_congr fun x hx ↦ ?_)
  ext v
  simp only [e, Trivialization.continuousLinearMap_apply, localTriv_continuousLinearMapAt _ hx.2,
    localTriv_symmL _ hx.1, inChartCoordinates_apply]
  -- The remaining composite is stated between the core fibres, which are `F` and `G`.
  rfl

/-- A section of the Hom bundle between two cores is `C^n` exactly when it is `C^n` in every pair
of charts, on their common domain. -/
theorem contMDiff_hom_bundle_iff_forall_contMDiffOn {f : B → F →L[𝕜] G} :
    ContMDiff IB (IB.prod 𝓘(𝕜, F →L[𝕜] G)) n
        (fun x ↦ TotalSpace.mk' (F →L[𝕜] G) (E := fun y ↦ Z.Fiber y →L[𝕜] W.Fiber y) x (f x)) ↔
      ∀ i j, ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] G) n (fun x ↦ Z.inChartCoordinates W i j x (f x))
        (Z.baseSet i ∩ W.baseSet j) := by
  refine ⟨fun hf i j ↦ (contMDiffOn_hom_bundle_iff_inChartCoordinates i j).1 hf.contMDiffOn,
    fun h x ↦ ?_⟩
  have hU := (Z.isOpen_baseSet (Z.indexAt x)).inter (W.isOpen_baseSet (W.indexAt x))
  exact ((contMDiffOn_hom_bundle_iff_inChartCoordinates _ _).2 (h _ _)).contMDiffAt
    (hU.mem_nhds ⟨Z.mem_baseSet_at x, W.mem_baseSet_at x⟩)

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
  constructor
  · rintro ⟨Φ, hΦ⟩
    refine ⟨a.contMDiff_totalSpaceMap_iff.1 (hΦ ▸ Φ.contMDiff), fun x ↦ ?_⟩
    have hΦ' (v : F) : Φ ⟨x, v⟩ = ⟨x, a.fiberMap x v⟩ :=
      (congrFun hΦ _).trans (a.totalSpaceMap_mk x v)
    -- The fibre map is bijective because `Φ` is, hence an isomorphism in finite dimension.
    have hinj : Function.Injective (a.fiberMap x) := fun v w h ↦ by
      have hvw : Φ ⟨x, v⟩ = Φ ⟨x, w⟩ := by rw [hΦ', hΦ', h]
      exact TotalSpace.mk_inj.1 (Φ.injective hvw)
    have hsurj : Function.Surjective (a.fiberMap x) := fun w ↦ by
      obtain ⟨⟨y, v⟩, hp⟩ := Φ.surjective ⟨x, w⟩
      have hp' : (⟨y, a.fiberMap y v⟩ : W.TotalSpace) = ⟨x, w⟩ :=
        (a.totalSpaceMap_mk y v).symm.trans ((congrFun hΦ _).symm.trans hp)
      obtain rfl : y = x := congrArg TotalSpace.proj hp'
      exact ⟨v, TotalSpace.mk_inj.1 hp'⟩
    exact ⟨(LinearEquiv.ofBijective (a.fiberMap x).toLinearMap
      ⟨hinj, hsurj⟩).toContinuousLinearEquiv, rfl⟩
  · rintro ⟨ha, hinv⟩
    choose e he using hinv
    have : CompleteSpace F := FiniteDimensional.complete 𝕜 F
    refine ⟨TauCeti.bundleDiffeomorph (E₁ := Z.Fiber) (E₂ := W.Fiber) e ?_, ?_⟩
    · convert contMDiff_hom_bundle_iff_forall_contMDiffOn.2 ha using 3
      exact congrArg _ (he _)
    · funext p
      refine (TauCeti.bundleDiffeomorph_apply (E₁ := Z.Fiber) (E₂ := W.Fiber) e _ p).trans ?_
      rw [totalSpaceMap_def]
      exact congrArg (TotalSpace.mk' G p.proj) (congrArg (fun L : F →L[𝕜] G ↦ L p.2) (he p.proj))

end CoordinateHom

end VectorBundleCore
