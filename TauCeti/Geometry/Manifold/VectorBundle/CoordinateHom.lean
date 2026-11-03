/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.Descent
import TauCeti.Data.Bundle

/-!
# `C^n` cocycle morphisms and `C^n` bundle equivalences

Let `Z` and `W` be vector bundle cores over a manifold `B` whose transition functions are `C^n`
(`VectorBundleCore.IsContMDiff`), so that the bundles glued from them are `C^n` vector bundles.
A morphism of the underlying cocycles, `VectorBundleCore.CoordinateHom`, consists of continuous
chart operators intertwining the two families of transition functions. This file shows that,
for a finite-dimensional source fibre, these operators are `C^n` exactly when the glued map of
total spaces is `C^n`, and that a cocycle morphism with `C^n` operators and bijective fibre maps
glues to a `C^n` diffeomorphism of total spaces covering the identity of `B`. Conversely, every
`C^n` fibrewise linear map of the glued total spaces is the glued map of a unique cocycle
morphism, `CoordinateHom.ofContinuous`, and its operators are then `C^n` by the same criterion.

Over the model `𝓘(ℂ, EB)` and with `n = ∞`, these say that holomorphic cocycle isomorphisms are
the same as holomorphic bundle equivalences of the glued holomorphic vector bundles.

## Main results

* `VectorBundleCore.contMDiff_hom_bundle_iff_forall_contMDiffOn`: a section of the Hom bundle
  between two `C^n` cores is `C^n` exactly when it is `C^n` in every pair of a source chart and
  a target chart, on their common domain.
* `VectorBundleCore.CoordinateHom.contMDiff_totalSpaceMap_iff`: for a finite-dimensional source
  fibre, the glued map of a cocycle morphism is `C^n` exactly when all its chart operators are.
* `VectorBundleCore.CoordinateHom.toDiffeomorph`: a cocycle morphism with `C^n` chart operators
  and bijective fibre maps is a `C^n` diffeomorphism of total spaces.
* `VectorBundleCore.CoordinateHom.exists_diffeomorph_iff`: for a finite-dimensional source fibre,
  the glued map of a cocycle morphism underlies a `C^n` diffeomorphism exactly when its chart
  operators are `C^n` and its fibre maps are bijective.

## References

* Norman Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §2–§3
  (equivalence of coordinate bundles through their transition functions).
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
-/

public section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace VectorBundleCore

variable {𝕜 B F G ι κ : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {Z : VectorBundleCore 𝕜 B F ι} {W : VectorBundleCore 𝕜 B G κ}

/-- A section of the Hom bundle between two `C^n` cores that is `C^n` on the common domain of a
source chart and a target chart is `C^n` in those charts there. -/
theorem contMDiffOn_inChartCoordinates [Z.IsContMDiff IB n] [W.IsContMDiff IB n]
    {f : B → F →L[𝕜] G} {i : ι} {j : κ}
    (hf : ContMDiffOn IB (IB.prod 𝓘(𝕜, F →L[𝕜] G)) n (fun x ↦
      TotalSpace.mk' (F →L[𝕜] G) (E := fun y ↦ Z.Fiber y →L[𝕜] W.Fiber y) x (f x))
      (Z.baseSet i ∩ W.baseSet j)) :
    ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] G) n (fun x ↦ Z.inChartCoordinates W i j x (f x))
      (Z.baseSet i ∩ W.baseSet j) := by
  have : MemTrivializationAtlas (Z.localTriv i) := ⟨⟨i, rfl⟩⟩
  have : MemTrivializationAtlas (W.localTriv j) := ⟨⟨j, rfl⟩⟩
  -- Read the section in the Hom-bundle trivialization built from the two fixed charts.
  let e := (Z.localTriv i).continuousLinearMap (RingHom.id 𝕜) (W.localTriv j)
  have he := (e.contMDiffOn_section_iff ((Z.isOpen_baseSet i).inter (W.isOpen_baseSet j))
    subset_rfl).1 hf
  exact he.congr fun x hx ↦ inChartCoordinates_eq_localTriv_comp hx.1 hx.2 (f x)

/-- A family of fibre maps is a `C^n` section of the Hom bundle between two `C^n` cores exactly
when it is `C^n` in every pair of charts. This is the `C^n` counterpart of
`VectorBundleCore.continuous_hom_bundle_iff_forall_continuousOn`. -/
theorem contMDiff_hom_bundle_iff_forall_contMDiffOn [Z.IsContMDiff IB n] [W.IsContMDiff IB n]
    {f : B → F →L[𝕜] G} :
    ContMDiff IB (IB.prod 𝓘(𝕜, F →L[𝕜] G)) n (fun x ↦
      TotalSpace.mk' (F →L[𝕜] G) (E := fun y ↦ Z.Fiber y →L[𝕜] W.Fiber y) x (f x)) ↔
    ∀ i j, ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] G) n (fun x ↦ Z.inChartCoordinates W i j x (f x))
      (Z.baseSet i ∩ W.baseSet j) := by
  refine ⟨fun hf _ _ ↦ contMDiffOn_inChartCoordinates hf.contMDiffOn, fun h x₀ ↦ ?_⟩
  have hx₀ : x₀ ∈ Z.baseSet (Z.indexAt x₀) ∩ W.baseSet (W.indexAt x₀) :=
    ⟨Z.mem_baseSet_at x₀, W.mem_baseSet_at x₀⟩
  have hU := ((Z.isOpen_baseSet _).inter (W.isOpen_baseSet _)).mem_nhds hx₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ((h _ _).contMDiffAt hU).congr_of_eventuallyEq ?_⟩
  filter_upwards [hU] with x hx
  ext v
  rw [Z.inCoordinates_eq W (f x) hx.1 hx.2, inChartCoordinates_apply]
  -- `ContinuousLinearMap.comp_apply` does not fire on a vector of the core fibre `Z.Fiber`,
  -- which is the model fibre `F` only up to unfolding.
  rfl

namespace CoordinateHom

/-- A cocycle morphism between two `C^n` cores whose chart operators are `C^n` glues to a `C^n`
map of total spaces. Unlike `VectorBundleCore.CoordinateHom.contMDiff_totalSpaceMap_iff`, this
direction needs no finite-dimensionality. -/
theorem contMDiff_totalSpaceMap [Z.IsContMDiff IB n] [W.IsContMDiff IB n] (a : CoordinateHom Z W)
    (ha : ∀ i j, ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] G) n
      (fun x ↦ Z.inChartCoordinates W i j x (a.fiberMap x)) (Z.baseSet i ∩ W.baseSet j)) :
    ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, G)) n a.totalSpaceMap := by
  rw [totalSpaceMap_def]
  exact ((contMDiff_hom_bundle_iff_forall_contMDiffOn.2 ha).comp
    (contMDiff_proj Z.Fiber)).clm_bundle_apply contMDiff_id

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] [Z.IsContMDiff IB n] [W.IsContMDiff IB n]

/-- For a finite-dimensional source fibre, the map of total spaces glued from a cocycle morphism
between two `C^n` cores is `C^n` exactly when every chart operator is `C^n` on its domain. By
`VectorBundleCore.CoordinateHom.operator_eq`, the function on the right-hand side is the chart
operator `a.operator i j` on `Z.baseSet i ∩ W.baseSet j`. -/
theorem contMDiff_totalSpaceMap_iff (a : CoordinateHom Z W) :
    ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, G)) n a.totalSpaceMap ↔
      ∀ i j, ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] G) n
        (fun x ↦ Z.inChartCoordinates W i j x (a.fiberMap x)) (Z.baseSet i ∩ W.baseSet j) := by
  rw [totalSpaceMap_def]
  exact (TauCeti.contMDiff_hom_bundle_iff (E₁ := Z.Fiber) (E₂ := W.Fiber) a.fiberMap).symm.trans
    contMDiff_hom_bundle_iff_forall_contMDiffOn

/-- The fibrewise continuous linear equivalences of a cocycle morphism with bijective fibre
maps. -/
noncomputable def fiberEquiv (a : CoordinateHom Z W)
    (hbij : ∀ x, Function.Bijective (a.fiberMap x)) (x : B) : Z.Fiber x ≃L[𝕜] W.Fiber x :=
  (LinearEquiv.ofBijective (a.fiberMap x).toLinearMap (hbij x)).toContinuousLinearEquiv

@[simp]
theorem fiberEquiv_apply (a : CoordinateHom Z W) (hbij : ∀ x, Function.Bijective (a.fiberMap x))
    (x : B) (v : Z.Fiber x) : a.fiberEquiv hbij x v = a.fiberMap x v :=
  (rfl)

/-- A cocycle morphism between two `C^n` cores whose chart operators are `C^n` and whose fibre
maps are bijective glues to a `C^n` diffeomorphism of total spaces covering the identity of the
base. Over `𝓘(ℂ, EB)` with `n = ∞`, this is the holomorphic bundle equivalence defined by a
holomorphic cocycle isomorphism. -/
noncomputable def toDiffeomorph (a : CoordinateHom Z W)
    (ha : ∀ i j, ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] G) n
      (fun x ↦ Z.inChartCoordinates W i j x (a.fiberMap x)) (Z.baseSet i ∩ W.baseSet j))
    (hbij : ∀ x, Function.Bijective (a.fiberMap x)) :
    Z.TotalSpace ≃ₘ^n⟮IB.prod 𝓘(𝕜, F), IB.prod 𝓘(𝕜, G)⟯ W.TotalSpace :=
  TauCeti.bundleDiffeomorph (a.fiberEquiv hbij) <|
    (a.contMDiff_totalSpaceMap_iff.2 ha).congr fun ⟨x, v⟩ ↦ (a.totalSpaceMap_mk x v).symm

@[simp]
theorem coe_toDiffeomorph (a : CoordinateHom Z W)
    (ha : ∀ i j, ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] G) n
      (fun x ↦ Z.inChartCoordinates W i j x (a.fiberMap x)) (Z.baseSet i ∩ W.baseSet j))
    (hbij : ∀ x, Function.Bijective (a.fiberMap x)) :
    ⇑(a.toDiffeomorph ha hbij) = a.totalSpaceMap :=
  funext fun ⟨x, v⟩ ↦ by simp [toDiffeomorph]

@[simp]
theorem toDiffeomorph_symm_apply (a : CoordinateHom Z W)
    (ha : ∀ i j, ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] G) n
      (fun x ↦ Z.inChartCoordinates W i j x (a.fiberMap x)) (Z.baseSet i ∩ W.baseSet j))
    (hbij : ∀ x, Function.Bijective (a.fiberMap x)) (p : W.TotalSpace) :
    (a.toDiffeomorph ha hbij).symm p = ⟨p.proj, (a.fiberEquiv hbij p.proj).symm p.2⟩ :=
  TauCeti.bundleDiffeomorph_symm_apply _ _ p

/-- Every `C^n` bundle equivalence between the bundles glued from two `C^n` cores, that is, every
`C^n` family of fibrewise linear equivalences, is glued from a cocycle isomorphism with `C^n`
chart operators. The cocycle morphism is unique by
`VectorBundleCore.CoordinateHom.totalSpaceMap_injective`. -/
theorem exists_toDiffeomorph_eq (e : ∀ x, Z.Fiber x ≃L[𝕜] W.Fiber x)
    (he : ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, G)) n
      (fun p : Z.TotalSpace ↦ TotalSpace.mk' G p.proj (e p.proj p.2))) :
    ∃ (a : CoordinateHom Z W)
      (ha : ∀ i j, ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] G) n
        (fun x ↦ Z.inChartCoordinates W i j x (a.fiberMap x)) (Z.baseSet i ∩ W.baseSet j))
      (hbij : ∀ x, Function.Bijective (a.fiberMap x)),
      a.toDiffeomorph ha hbij = TauCeti.bundleDiffeomorph e he := by
  -- The fibre maps, regarded as a family of operators between the model fibres.
  let ϕ : B → F →L[𝕜] G := fun x ↦ (e x : Z.Fiber x →L[𝕜] W.Fiber x)
  have hϕ : ContMDiff IB (IB.prod 𝓘(𝕜, F →L[𝕜] G)) n (fun x ↦
      TotalSpace.mk' (F →L[𝕜] G) (E := fun y ↦ Z.Fiber y →L[𝕜] W.Fiber y) x (ϕ x)) :=
    (TauCeti.contMDiff_hom_bundle_iff (E₁ := Z.Fiber) (E₂ := W.Fiber)
      fun x ↦ (e x : Z.Fiber x →L[𝕜] W.Fiber x)).2 he
  refine ⟨ofContinuous ϕ hϕ.continuous, ?_, fun x ↦ ?_, ?_⟩
  · rw [fiberMap_ofContinuous]
    exact contMDiff_hom_bundle_iff_forall_contMDiffOn.1 hϕ
  · rw [fiberMap_ofContinuous]
    exact (e x).bijective
  · refine Diffeomorph.ext fun ⟨x, v⟩ ↦ ?_
    rw [coe_toDiffeomorph, totalSpaceMap_mk, fiberMap_ofContinuous,
      TauCeti.bundleDiffeomorph_apply]
    -- Both sides apply `e x` to `v`, once through its coercion to a continuous linear map between
    -- the model fibres `F` and `G`; `ContinuousLinearEquiv.coe_coe` does not fire on a vector of
    -- the core fibre `Z.Fiber x`, which is `F` only up to unfolding.
    rfl

/-- **Cocycle isomorphisms are bundle equivalences.** For a finite-dimensional source fibre, a
cocycle morphism between two `C^n` cores glues to the underlying map of a `C^n` diffeomorphism of
total spaces exactly when its chart operators are `C^n` and its fibre maps are bijective. -/
theorem exists_diffeomorph_iff (a : CoordinateHom Z W) :
    (∃ Φ : Z.TotalSpace ≃ₘ^n⟮IB.prod 𝓘(𝕜, F), IB.prod 𝓘(𝕜, G)⟯ W.TotalSpace,
        ⇑Φ = a.totalSpaceMap) ↔
      (∀ i j, ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] G) n
        (fun x ↦ Z.inChartCoordinates W i j x (a.fiberMap x)) (Z.baseSet i ∩ W.baseSet j)) ∧
      ∀ x, Function.Bijective (a.fiberMap x) := by
  refine ⟨fun ⟨Φ, hΦ⟩ ↦ ⟨a.contMDiff_totalSpaceMap_iff.1 (hΦ ▸ Φ.contMDiff), ?_⟩,
    fun ⟨ha, hbij⟩ ↦ ⟨a.toDiffeomorph ha hbij, a.coe_toDiffeomorph ha hbij⟩⟩
  rw [totalSpaceMap_def] at hΦ
  exact TauCeti.bijective_totalSpace_map_iff (E₁ := Z.Fiber) (E₂ := W.Fiber)
    (ϕ := fun x ↦ a.fiberMap x) |>.1 (hΦ ▸ Φ.bijective)

end CoordinateHom

end VectorBundleCore
