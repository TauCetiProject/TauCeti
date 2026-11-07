/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.Descent
import TauCeti.Data.Bundle
import TauCeti.Geometry.Manifold.VectorBundle.Translate

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
* `VectorBundleCore.CoordinateHom.contMDiffOn_inChartCoordinates_id`,
  `VectorBundleCore.CoordinateHom.contMDiffOn_inChartCoordinates_comp`,
  `VectorBundleCore.CoordinateHom.contMDiffOn_inChartCoordinates_add`,
  `VectorBundleCore.CoordinateHom.contMDiffOn_inChartCoordinates_zero`,
  `VectorBundleCore.CoordinateHom.contMDiffOn_inChartCoordinates_neg`, and the corresponding
  `contMDiff_totalSpaceMap_*` lemmas: `C^n` regularity of chart operators and of glued total-space
  maps is preserved by identity, composition, and the group operations.
* `VectorBundleCore.CoordinateHom.toDiffeomorphOfInv`: two mutually inverse cocycle morphisms with
  `C^n` total-space maps form a `C^n` diffeomorphism of total spaces without completeness or
  finite-dimensionality assumptions.
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

/-- On a `C^n` core, the chart operators of the identity cocycle morphism are `C^n`. -/
theorem contMDiffOn_inChartCoordinates_id [Z.IsContMDiff IB n] (i j : ι) :
    ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun x ↦ Z.inChartCoordinates Z i j x ((id Z).fiberMap x))
      (Z.baseSet i ∩ Z.baseSet j) :=
  (Z.contMDiffOn_coordChange IB i j).congr fun x hx ↦ by
    ext v
    simp only [fiberMap_id, inChartCoordinates_apply, ContinuousLinearMap.id_apply]
    exact Z.coordChange_comp i (Z.indexAt x) j x ⟨⟨hx.1, Z.mem_baseSet_at x⟩, hx.2⟩ v

/-- The chart operators of the zero cocycle morphism are `C^n`. -/
theorem contMDiffOn_inChartCoordinates_zero (i : ι) (j : κ) :
    ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] G) n
      (fun x ↦ Z.inChartCoordinates W i j x ((0 : CoordinateHom Z W).fiberMap x))
      (Z.baseSet i ∩ W.baseSet j) :=
  (contMDiffOn_const (c := (0 : F →L[𝕜] G))).congr fun x hx ↦
    ((0 : CoordinateHom Z W).operator_eq i j ⟨x, hx⟩).symm

/-- Pointwise addition of cocycle morphisms preserves `C^n` regularity of chart operators. -/
theorem contMDiffOn_inChartCoordinates_add {a b : CoordinateHom Z W} {i : ι} {j : κ}
    (ha : ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] G) n
      (fun x ↦ Z.inChartCoordinates W i j x (a.fiberMap x)) (Z.baseSet i ∩ W.baseSet j))
    (hb : ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] G) n
      (fun x ↦ Z.inChartCoordinates W i j x (b.fiberMap x)) (Z.baseSet i ∩ W.baseSet j)) :
    ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] G) n
      (fun x ↦ Z.inChartCoordinates W i j x ((a + b).fiberMap x)) (Z.baseSet i ∩ W.baseSet j) := by
  intro x hx
  refine (contDiff_add.comp_contMDiffWithinAt ((ha x hx).prodMk_space (hb x hx))).congr
    (fun y hy ↦ ?_) ?_
  · ext v
    simp [inChartCoordinates_apply]
  · ext v
    simp [inChartCoordinates_apply]

/-- Negation of a cocycle morphism preserves `C^n` regularity of chart operators. -/
theorem contMDiffOn_inChartCoordinates_neg {a : CoordinateHom Z W} {i : ι} {j : κ}
    (ha : ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] G) n
      (fun x ↦ Z.inChartCoordinates W i j x (a.fiberMap x)) (Z.baseSet i ∩ W.baseSet j)) :
    ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] G) n
      (fun x ↦ Z.inChartCoordinates W i j x ((-a).fiberMap x)) (Z.baseSet i ∩ W.baseSet j) := by
  intro x hx
  refine (contDiff_neg.comp_contMDiffWithinAt (ha x hx)).congr (fun y hy ↦ ?_) ?_
  · ext v
    simp [inChartCoordinates_apply]
  · ext v
    simp [inChartCoordinates_apply]

/-- Composition of cocycle morphisms preserves `C^n` regularity of chart operators. -/
theorem contMDiffOn_inChartCoordinates_comp {H ν : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    {V : VectorBundleCore 𝕜 B H ν} {b : CoordinateHom W V} {a : CoordinateHom Z W}
    (hb : ∀ j k, ContMDiffOn IB 𝓘(𝕜, G →L[𝕜] H) n
      (fun x ↦ W.inChartCoordinates V j k x (b.fiberMap x)) (W.baseSet j ∩ V.baseSet k))
    (ha : ∀ i j, ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] G) n
      (fun x ↦ Z.inChartCoordinates W i j x (a.fiberMap x)) (Z.baseSet i ∩ W.baseSet j))
    (i : ι) (k : ν) :
    ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] H) n
      (fun x ↦ Z.inChartCoordinates V i k x ((b.comp a).fiberMap x))
      (Z.baseSet i ∩ V.baseSet k) := by
  intro x₀ hx₀
  -- Near each base point, factor the composite through the preferred intermediate chart of `W`.
  let j := W.indexAt x₀
  let U := (Z.baseSet i ∩ W.baseSet j) ∩ (W.baseSet j ∩ V.baseSet k)
  have hUopen : IsOpen U :=
    ((Z.isOpen_baseSet i).inter (W.isOpen_baseSet j)).inter
      ((W.isOpen_baseSet j).inter (V.isOpen_baseSet k))
  have hx₀U : x₀ ∈ U := ⟨⟨hx₀.1, W.mem_baseSet_at x₀⟩, ⟨W.mem_baseSet_at x₀, hx₀.2⟩⟩
  have hcomp : ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] H) n
      (fun x ↦ Z.inChartCoordinates V i k x ((b.comp a).fiberMap x)) U :=
    (((hb j k).mono inter_subset_right).clm_comp ((ha i j).mono inter_subset_left)).congr
      fun x hx ↦ by
        rw [fiberMap_comp, inChartCoordinates_comp Z W V i k hx.1.2]
  exact ((hcomp x₀ hx₀U).contMDiffAt (hUopen.mem_nhds hx₀U)).contMDiffWithinAt

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

/-- The glued total-space map of the identity cocycle morphism is `C^n`. -/
theorem contMDiff_totalSpaceMap_id (Z : VectorBundleCore 𝕜 B F ι) :
    ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n (id Z).totalSpaceMap := by
  rw [totalSpaceMap_id]
  exact contMDiff_id

/-- The glued total-space map of the zero cocycle morphism is `C^n`. -/
theorem contMDiff_totalSpaceMap_zero :
    ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, G)) n (0 : CoordinateHom Z W).totalSpaceMap :=
  ((contMDiff_zeroSection 𝕜 W.Fiber).comp (contMDiff_proj Z.Fiber)).congr fun _ ↦ by
    rw [totalSpaceMap_def]
    simp only [Function.comp_apply, fiberMap_zero, zeroSection]
    -- The zero element of the core fibre `W.Fiber _` is `0 : G`.
    rfl

/-- Pointwise addition of cocycle morphisms preserves `C^n` regularity of glued total-space
maps. -/
theorem contMDiff_totalSpaceMap_add {a b : CoordinateHom Z W}
    (ha : ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, G)) n a.totalSpaceMap)
    (hb : ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, G)) n b.totalSpaceMap) :
    ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, G)) n (a + b).totalSpaceMap := by
  rw [totalSpaceMap_def] at ha hb ⊢
  refine (ha.add_sectionAlong hb).congr fun p ↦ ?_
  rw [fiberMap_add]
  -- Addition on `F →L[𝕜] G` applied to `p.2 : Z.Fiber p.proj` is addition on `W.Fiber p.proj`.
  rfl

/-- Negation of a cocycle morphism preserves `C^n` regularity of its glued total-space map. -/
theorem contMDiff_totalSpaceMap_neg {a : CoordinateHom Z W}
    (ha : ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, G)) n a.totalSpaceMap) :
    ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, G)) n (-a).totalSpaceMap := by
  intro p₀
  have ha₀ := (Bundle.contMDiffAt_totalSpace.1 (ha p₀)).2
  rw [Bundle.contMDiffAt_totalSpace]
  simp only [totalSpaceMap_proj] at ha₀ ⊢
  refine ⟨(contMDiff_proj Z.Fiber).contMDiffAt, ?_⟩
  refine (contDiff_neg.comp_contMDiffAt ha₀).congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  rintro ⟨x, v⟩
  dsimp only [Function.comp_apply]
  rw [W.trivializationAt, ← W.localTrivAt_def]
  simp only [totalSpaceMap_mk, localTriv_apply, fiberMap_neg]
  exact map_neg (W.coordChange (W.indexAt x) (W.indexAt p₀.proj) x) (a.fiberMap x v)

/-- Composition of cocycle morphisms preserves `C^n` regularity of glued total-space maps. -/
theorem contMDiff_totalSpaceMap_comp {H ν : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    {V : VectorBundleCore 𝕜 B H ν} {b : CoordinateHom W V} {a : CoordinateHom Z W}
    (hb : ContMDiff (IB.prod 𝓘(𝕜, G)) (IB.prod 𝓘(𝕜, H)) n b.totalSpaceMap)
    (ha : ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, G)) n a.totalSpaceMap) :
    ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, H)) n (b.comp a).totalSpaceMap := by
  rw [totalSpaceMap_comp]
  exact hb.comp ha

/-- Two mutually inverse cocycle morphisms whose glued total-space maps are `C^n` form a `C^n`
diffeomorphism of total spaces. Unlike `VectorBundleCore.CoordinateHom.toDiffeomorph`, neither
completeness of the scalar field, finite-dimensionality of the fibre, nor `C^n` regularity of the
cores is needed when an explicit inverse cocycle morphism is given. -/
def toDiffeomorphOfInv (a : CoordinateHom Z W) (b : CoordinateHom W Z)
    (hba : b.comp a = id Z) (hab : a.comp b = id W)
    (ha : ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, G)) n a.totalSpaceMap)
    (hb : ContMDiff (IB.prod 𝓘(𝕜, G)) (IB.prod 𝓘(𝕜, F)) n b.totalSpaceMap) :
    Z.TotalSpace ≃ₘ^n⟮IB.prod 𝓘(𝕜, F), IB.prod 𝓘(𝕜, G)⟯ W.TotalSpace where
  toFun := a.totalSpaceMap
  invFun := b.totalSpaceMap
  left_inv p := by
    have h := congrFun (congrArg totalSpaceMap hba) p
    rwa [totalSpaceMap_comp, Function.comp_apply, totalSpaceMap_id, _root_.id_eq] at h
  right_inv p := by
    have h := congrFun (congrArg totalSpaceMap hab) p
    rwa [totalSpaceMap_comp, Function.comp_apply, totalSpaceMap_id, _root_.id_eq] at h
  contMDiff_toFun := ha
  contMDiff_invFun := hb

@[simp]
theorem coe_toDiffeomorphOfInv (a : CoordinateHom Z W) (b : CoordinateHom W Z)
    (hba : b.comp a = id Z) (hab : a.comp b = id W)
    (ha : ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, G)) n a.totalSpaceMap)
    (hb : ContMDiff (IB.prod 𝓘(𝕜, G)) (IB.prod 𝓘(𝕜, F)) n b.totalSpaceMap) :
    ⇑(toDiffeomorphOfInv a b hba hab ha hb) = a.totalSpaceMap := (rfl)

@[simp]
theorem coe_toDiffeomorphOfInv_symm (a : CoordinateHom Z W) (b : CoordinateHom W Z)
    (hba : b.comp a = id Z) (hab : a.comp b = id W)
    (ha : ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, G)) n a.totalSpaceMap)
    (hb : ContMDiff (IB.prod 𝓘(𝕜, G)) (IB.prod 𝓘(𝕜, F)) n b.totalSpaceMap) :
    ⇑(toDiffeomorphOfInv a b hba hab ha hb).symm = b.totalSpaceMap := (rfl)

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
