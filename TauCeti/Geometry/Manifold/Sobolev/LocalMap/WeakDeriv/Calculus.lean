/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.Sobolev.LocalMap.WeakDeriv.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import TauCeti.Analysis.Sobolev.W1p.ChangeOfVariables
import TauCeti.Analysis.Sobolev.WeakDeriv.ChainRule
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.Geometry.Manifold.Boundary.Basic
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Atlas

/-!
# Chart independence, chain rules, and existence of the weak differential

Building on `TauCeti.Geometry.Manifold.Sobolev.LocalMap.WeakDeriv.Basic`, this file proves chart
independence (`TauCeti.hasWeakMFDerivOnGroupoid_iff_of_subset_maximalAtlas`, `_iff_atlas`,
`_iff_chartAt`), weak chain rules under `C¹` postcomposition and source diffeomorphisms
(`TauCeti.HasWeakMFDerivOnGroupoid.contMDiffOn_comp`,
`Diffeomorph.hasWeakMFDerivOnGroupoid_diffeomorph_comp_iff`,
`Diffeomorph.hasWeakMFDerivOnGroupoid_comp_diffeomorph_iff`), and global existence / `W^{1,p}_loc`
characterizations (`TauCeti.MemWkpLocMapOnGroupoid.exists_hasWeakMFDerivOnGroupoid`,
`TauCeti.memWkpLocMapOnGroupoid_one_iff_exists_hasWeakMFDerivOnGroupoid`) on Lindelöf surfaces with
or without boundary (McDuff–Salamon, *J-holomorphic Curves and Symplectic Topology*, App. B.1).
-/

public section

open Bundle Filter Function MeasureTheory Set TopologicalSpace
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

section Transitions

variable {H' : Type*} [TopologicalSpace H'] {X : Type*} [TopologicalSpace X] [ChartedSpace H' X]
  {G : StructureGroupoid H'} {J : ModelWithCorners ℝ ℂ H'}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {H'' : Type*} [TopologicalSpace H''] {I' : ModelWithCorners ℝ F' H''}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H'' N]
  {p : ENNReal} {u : X → M} {du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x)} {s : Set X}

omit [ChartedSpace H' X] [ChartedSpace H M] in
private theorem isOpen_inter_inter_preimage {U : Set X} {V : Set M}
    (hc : ContinuousOn u s) (hs : IsOpen s) (hU : IsOpen U) (hV : IsOpen V) :
    IsOpen (s ∩ (U ∩ u ⁻¹' V)) := by
  convert (hs.inter hU).inter (hc.isOpen_inter_preimage hs hV) using 1; ext; simp; tauto

private theorem hasWeakFDerivOn_comp_chart_transition
    {φ φ' : OpenPartialHomeomorph X H'} (hφ : φ ∈ IsManifold.maximalAtlas J 1 X)
    (hφ' : φ' ∈ IsManifold.maximalAtlas J 1 X) (ψ : OpenPartialHomeomorph M H) {U W : Opens ℂ}
    (hU : HasWeakFDerivOn volume U (ψ.extend I ∘ u ∘ (φ.extend J).symm)
      (chartTangentHom J I φ ψ u du))
    (hW : (W : Set ℂ) ⊆ interior ((φ'.extend J).target ∩ (φ'.extend J).symm ⁻¹' φ.source))
    (hmaps : MapsTo (φ.extend J ∘ (φ'.extend J).symm) W U) :
    HasWeakFDerivOn volume W (ψ.extend I ∘ u ∘ (φ'.extend J).symm)
      (chartTangentHom J I φ' ψ u du) := by
  have hsrc : (W : Set ℂ) ⊆ (J.extendCoordChange φ' φ).source := by
    rw [ModelWithCorners.extendCoordChange, PartialEquiv.trans_source, PartialEquiv.symm_source,
      φ.extend_source]; exact hW.trans interior_subset
  refine ((hU.comp_contDiffOn_diffeo ((J.contDiffOn_extendCoordChange hφ' hφ).mono hsrc)
    ((J.extendCoordChange φ' φ).injOn.mono hsrc)
    (fun w hw ↦ J.det_fderiv_extendCoordChange_ne_zero one_ne_zero hφ' hφ (hW hw))
    hmaps).congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [ae_restrict_mem W.isOpen.measurableSet] with w hw
    simp only [Function.comp_apply, ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply,
      φ.extend_left_inv (interior_subset (hW hw)).2]
  · filter_upwards [ae_restrict_mem W.isOpen.measurableSet] with w hw
    exact chartTangentHom_comp_fderiv_transition hφ hφ' ψ du (hW hw)

private theorem hasWeakFDerivOn_change_source_chart [CompleteSpace F]
    (hc : ContinuousOn u s) (hs : IsOpen s) {A : Set (OpenPartialHomeomorph X H')}
    (hAJ : A ⊆ IsManifold.maximalAtlas J 1 X) (hAs : ∀ x ∈ s, ∃ φ ∈ A, x ∈ φ.source)
    {φ' : OpenPartialHomeomorph X H'} (hφ' : φ' ∈ IsManifold.maximalAtlas J 1 X)
    (ψ : OpenPartialHomeomorph M H)
    (hAψ : ∀ φ ∈ A, HasWeakFDerivOn volume
      (Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
      (ψ.extend I ∘ u ∘ (φ.extend J).symm) (chartTangentHom J I φ ψ u du)) :
    HasWeakFDerivOn volume
      (Opens.interior ((φ'.extend J).target ∩ (φ'.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
      (ψ.extend I ∘ u ∘ (φ'.extend J).symm) (chartTangentHom J I φ' ψ u du) := by
  refine hasWeakFDerivOn_iff_locally.2 fun z hz ↦ ?_
  obtain ⟨φ, hφA, hxφ⟩ := hAs _ (interior_subset hz).2.1
  refine ⟨Opens.interior ((φ'.extend J).target ∩
      (φ'.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source ∩ φ.source)),
    φ'.mem_interior_extend_target_inter_preimage
      (mem_of_superset (isOpen_interior.mem_nhds hz) (interior_subset.trans inter_subset_left))
      (((hc.isOpen_inter_preimage hs ψ.open_source).inter φ.open_source).mem_nhds
        ⟨(interior_subset hz).2, hxφ⟩),
    hasWeakFDerivOn_comp_chart_transition (hAJ hφA) hφ' ψ (hAψ φ hφA)
      (interior_mono (inter_subset_inter_right _ (preimage_mono inter_subset_right))) fun w hw ↦ ?_⟩
  have hwt : w ∈ (φ'.extend J).target := (interior_subset hw).1
  have hxφ' : (φ'.extend J).symm w ∈ φ'.source :=
    φ'.extend_source (I := J) ▸ (φ'.extend J).map_target hwt
  exact φ.mem_interior_extend_target_inter_preimage (mem_interior_iff_mem_nhds.1
      (ModelWithCorners.mem_interior_extend_target_of_mem_maximalAtlas one_ne_zero hφ' (hAJ hφA)
        hxφ' (interior_subset hw).2.2
        (by rw [(φ'.extend J).right_inv hwt]; exact interior_mono inter_subset_left hw)))
    (by rw [Function.comp_apply, φ.extend_left_inv (interior_subset hw).2.2]
        exact (hc.isOpen_inter_preimage hs ψ.open_source).mem_nhds (interior_subset hw).2.1)

private theorem hasWeakFDerivOn_extend_comp [I.Boundaryless] [CompleteSpace F']
    {φ : OpenPartialHomeomorph X H'} {ψ : OpenPartialHomeomorph M H}
    (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) {ψ' : OpenPartialHomeomorph N H''}
    (hψ' : ψ' ∈ IsManifold.maximalAtlas I' ∞ N) {f : M → N} {t : Set M}
    (hf : ContMDiffOn I I' 1 f t) (ht : IsOpen t) {W : Opens ℂ}
    (hW : HasWeakFDerivOn volume W (ψ.extend I ∘ u ∘ (φ.extend J).symm)
      (chartTangentHom J I φ ψ u du))
    (huc : ContinuousOn (ψ.extend I ∘ u ∘ (φ.extend J).symm) W)
    (hmaps : MapsTo (u ∘ (φ.extend J).symm) W (ψ.source ∩ (t ∩ f ⁻¹' ψ'.source))) :
    HasWeakFDerivOn volume W (ψ'.extend I' ∘ (f ∘ u) ∘ (φ.extend J).symm)
      (chartTangentHom J I' φ ψ' (f ∘ u) (fun x ↦ (mfderiv I I' f (u x)).comp (du x))) := by
  have hψ1 : ψ ∈ IsManifold.maximalAtlas I 1 M :=
    StructureGroupoid.maximalAtlas_mono (contDiffGroupoid_le (by simp)) hψ
  have hψ'1 : ψ' ∈ IsManifold.maximalAtlas I' 1 N :=
    StructureGroupoid.maximalAtlas_mono (contDiffGroupoid_le (by simp)) hψ'
  obtain ⟨hO, hg⟩ := ψ.isOpen_and_contDiffOn_extend_comp hψ1 hψ'1 hf ht
  refine ((hW.contDiffOn_comp huc hO hg fun w hw ↦
    ⟨(ψ.extend I).map_source ((ψ.extend_source (I := I)).symm ▸ (hmaps hw).1),
      by rw [mem_preimage, Function.comp_apply, ψ.extend_left_inv (I := I) (hmaps hw).1]
         exact (hmaps hw).2⟩).congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [ae_restrict_mem W.isOpen.measurableSet] with w hw
    have hws : u ((φ.extend J).symm w) ∈ ψ.source := (hmaps hw).1
    simp only [Function.comp_apply, ψ.extend_left_inv (I := I) hws]
  · filter_upwards [ae_restrict_mem W.isOpen.measurableSet] with w hw
    exact fderiv_extend_comp_chartTangentHom hψ1 hψ'1 hf ht du (hmaps hw)

/-! ### Chart independence and the weak chain rule at groupoid generality -/

/-- **Chart independence of the weak differential** for covering subfamilies `A` and `B` when `M`
is boundaryless (`X` may have boundary). -/
theorem hasWeakMFDerivOnGroupoid_iff_of_subset_maximalAtlas [I.Boundaryless] [CompleteSpace F]
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X) (hs : IsOpen s)
    {A : Set (OpenPartialHomeomorph X H')} (hA : A ⊆ G.maximalAtlas X)
    (hAs : ∀ x ∈ s, ∃ φ ∈ A, x ∈ φ.source) {B : Set (OpenPartialHomeomorph M H)}
    (hB : B ⊆ IsManifold.maximalAtlas I ∞ M) (hBs : ∀ x ∈ s, ∃ ψ ∈ B, u x ∈ ψ.source) :
    HasWeakMFDerivOnGroupoid G J I u du s ↔ ContinuousOn u s ∧ ∀ φ ∈ A, ∀ ψ ∈ B,
      HasWeakFDerivOn volume
        (Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ (φ.extend J).symm) (chartTangentHom J I φ ψ u du) := by
  refine ⟨fun h ↦ ⟨h.continuousOn, fun φ hφ ψ hψ ↦ h.hasWeakFDerivOn_chart (hA hφ) (hB hψ)⟩,
    fun ⟨hc, h⟩ ↦ hasWeakMFDerivOnGroupoid_iff.2
      ⟨hc, fun φ' hφ' ψ' hψ' ↦ hasWeakFDerivOn_iff_locally.2 fun z hz ↦ ?_⟩⟩
  -- First change source charts from `A` to `φ'`, then pass from `ψ ∈ B` to `ψ'` via `id : M → M`.
  obtain ⟨ψ, hψB, hxψ⟩ := hBs _ (interior_subset hz).2.1
  have h1 := hasWeakFDerivOn_change_source_chart hc hs (hA.trans hG) hAs (hG hφ') ψ
    fun φ hφ ↦ h φ hφ ψ hψB
  set W := Opens.interior ((φ'.extend J).target ∩
    (φ'.extend J).symm ⁻¹' (s ∩ u ⁻¹' (ψ.source ∩ ψ'.source)))
  have hWsub : (W : Set ℂ) ⊆
      interior ((φ'.extend J).target ∩ (φ'.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
    interior_mono (inter_subset_inter_right _
      (preimage_mono (inter_subset_inter_right _ (preimage_mono inter_subset_left))))
  refine ⟨W, φ'.mem_interior_extend_target_inter_preimage
      (mem_of_superset (isOpen_interior.mem_nhds hz) (interior_subset.trans inter_subset_left))
      ((hc.isOpen_inter_preimage hs (ψ.open_source.inter ψ'.open_source)).mem_nhds
        ⟨(interior_subset hz).2.1, hxψ, (interior_subset hz).2.2⟩),
    (hasWeakFDerivOn_extend_comp (hB hψB) hψ' contMDiffOn_id isOpen_univ (h1.mono hWsub)
      (φ'.continuousOn_extend_comp_symm ψ hc (hWsub.trans interior_subset))
      fun w hw ↦ ⟨(interior_subset hw).2.2.1, mem_univ _, (interior_subset hw).2.2.2⟩
      ).congr_ae_deriv ?_⟩
  filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with w _
  exact chartTangentHom_congr (by rw [mfderiv_id, ContinuousLinearMap.id_comp])

/-- Global chart independence of `HasWeakMFDerivGroupoid` for covering subfamilies. -/
theorem hasWeakMFDerivGroupoid_iff_of_subset_maximalAtlas [I.Boundaryless] [CompleteSpace F]
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X) {A : Set (OpenPartialHomeomorph X H')}
    (hA : A ⊆ G.maximalAtlas X) (hAs : ∀ x : X, ∃ φ ∈ A, x ∈ φ.source)
    {B : Set (OpenPartialHomeomorph M H)} (hB : B ⊆ IsManifold.maximalAtlas I ∞ M)
    (hBs : ∀ x : X, ∃ ψ ∈ B, u x ∈ ψ.source) :
    HasWeakMFDerivGroupoid G J I u du ↔ Continuous u ∧ ∀ φ ∈ A, ∀ ψ ∈ B,
      HasWeakFDerivOn volume
        (Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ (φ.extend J).symm) (chartTangentHom J I φ ψ u du) := by
  rw [← hasWeakMFDerivOnGroupoid_univ, hasWeakMFDerivOnGroupoid_iff_of_subset_maximalAtlas hG
    isOpen_univ hA (fun x _ ↦ hAs x) hB (fun x _ ↦ hBs x)]
  simp only [continuousOn_univ, univ_inter]

section AtlasChartAt

variable [HasGroupoid X G] [IsManifold I ∞ M] [I.Boundaryless]

/-- Chart independence at groupoid generality: testing `atlas H' X` and `atlas H M` suffices. -/
theorem hasWeakMFDerivOnGroupoid_iff_atlas (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    (hs : IsOpen s) :
    HasWeakMFDerivOnGroupoid G J I u du s ↔ ContinuousOn u s ∧ ∀ φ ∈ atlas H' X, ∀ ψ ∈ atlas H M,
      HasWeakFDerivOn volume
        (Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ (φ.extend J).symm) (chartTangentHom J I φ ψ u du) := by
  refine ⟨fun h ↦ ⟨h.continuousOn, fun φ hφ ψ hψ ↦ h.hasWeakFDerivOn_chart
      (StructureGroupoid.subset_maximalAtlas G hφ) (IsManifold.subset_maximalAtlas hψ)⟩,
    fun ⟨hc, h⟩ ↦ hasWeakMFDerivOnGroupoid_iff.2 ⟨hc, fun φ' hφ' ψ' hψ' ↦ ?_⟩⟩
  have := (h _ (chart_mem_atlas H' (φ'.symm (J.symm 0)))
    _ (chart_mem_atlas H (ψ'.symm (I.symm 0)))).completeSpace
  exact ((hasWeakMFDerivOnGroupoid_iff_of_subset_maximalAtlas hG hs
    (StructureGroupoid.subset_maximalAtlas G)
    (fun x _ ↦ ⟨_, chart_mem_atlas H' x, mem_chart_source H' x⟩) IsManifold.subset_maximalAtlas
    (fun x _ ↦ ⟨_, chart_mem_atlas H (u x), mem_chart_source H (u x)⟩)).2
      ⟨hc, h⟩).hasWeakFDerivOn_chart hφ' hψ'

/-- Global chart independence at groupoid generality via `atlas H' X` and `atlas H M`. -/
theorem hasWeakMFDerivGroupoid_iff_atlas (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X) :
    HasWeakMFDerivGroupoid G J I u du ↔ Continuous u ∧ ∀ φ ∈ atlas H' X, ∀ ψ ∈ atlas H M,
      HasWeakFDerivOn volume
        (Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ (φ.extend J).symm) (chartTangentHom J I φ ψ u du) := by
  rw [← hasWeakMFDerivOnGroupoid_univ, hasWeakMFDerivOnGroupoid_iff_atlas hG isOpen_univ]
  simp only [continuousOn_univ, univ_inter]

/-- Chart independence at groupoid generality: testing `chartAt H' x` and `chartAt H y` suffices. -/
theorem hasWeakMFDerivOnGroupoid_iff_chartAt (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    (hs : IsOpen s) :
    HasWeakMFDerivOnGroupoid G J I u du s ↔ ContinuousOn u s ∧ ∀ x : X, ∀ y : M,
      HasWeakFDerivOn volume
        (Opens.interior ((extChartAt J x).target ∩
          (extChartAt J x).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y).source)))
        (extChartAt I y ∘ u ∘ (extChartAt J x).symm)
        (chartTangentHom J I (chartAt H' x) (chartAt H y) u du) := by
  refine ⟨fun h ↦ ⟨h.continuousOn, fun x y ↦ h.hasWeakFDerivOn_chart
      (StructureGroupoid.chart_mem_maximalAtlas G x) (IsManifold.chart_mem_maximalAtlas y)⟩,
    fun ⟨hc, h⟩ ↦ hasWeakMFDerivOnGroupoid_iff.2 ⟨hc, fun φ' hφ' ψ' hψ' ↦ ?_⟩⟩
  have := (h (φ'.symm (J.symm 0)) (ψ'.symm (I.symm 0))).completeSpace
  exact ((hasWeakMFDerivOnGroupoid_iff_of_subset_maximalAtlas hG hs
    (A := range (chartAt H')) (range_subset_iff.2 (StructureGroupoid.chart_mem_maximalAtlas G))
    (fun x _ ↦ ⟨_, mem_range_self x, mem_chart_source H' x⟩)
    (B := range (chartAt H)) (range_subset_iff.2 IsManifold.chart_mem_maximalAtlas)
    (fun x _ ↦ ⟨_, mem_range_self (u x), mem_chart_source H (u x)⟩)).2
      ⟨hc, by rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; exact h x y⟩).hasWeakFDerivOn_chart hφ' hψ'

/-- Global chart independence at groupoid generality via `chartAt H' x` and `chartAt H y`. -/
theorem hasWeakMFDerivGroupoid_iff_chartAt (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X) :
    HasWeakMFDerivGroupoid G J I u du ↔ Continuous u ∧ ∀ x : X, ∀ y : M,
      HasWeakFDerivOn volume (Opens.interior ((extChartAt J x).target ∩
          (extChartAt J x).symm ⁻¹' (u ⁻¹' (chartAt H y).source)))
        (extChartAt I y ∘ u ∘ (extChartAt J x).symm)
        (chartTangentHom J I (chartAt H' x) (chartAt H y) u du) := by
  rw [← hasWeakMFDerivOnGroupoid_univ, hasWeakMFDerivOnGroupoid_iff_chartAt hG isOpen_univ]
  simp only [continuousOn_univ, univ_inter]

end AtlasChartAt

/-- **The weak chain rule for maps into manifolds.** When `M` is boundaryless and smooth,
postcomposing `u` on open `s` with `C^n` (`1 ≤ n`) `f : M → N` on open `t` gives weak differential
`x ↦ (mfderiv I I' f (u x)).comp (du x)`. Neither `X` nor `N` need be boundaryless. -/
theorem HasWeakMFDerivOnGroupoid.contMDiffOn_comp [IsManifold I ∞ M] [I.Boundaryless]
    [CompleteSpace F'] {n : ℕ∞ω} {f : M → N} {t : Set M}
    (hu : HasWeakMFDerivOnGroupoid G J I u du s) (hf : ContMDiffOn I I' n f t) (hn : 1 ≤ n)
    (hs : IsOpen s) (ht : IsOpen t) (hst : MapsTo u s t) :
    HasWeakMFDerivOnGroupoid G J I' (f ∘ u) (fun x ↦ (mfderiv I I' f (u x)).comp (du x)) s := by
  have hc : ContinuousOn (f ∘ u) s := hf.continuousOn.comp hu.continuousOn hst
  refine hasWeakMFDerivOnGroupoid_iff.2
    ⟨hc, fun φ hφ ψ' hψ' ↦ hasWeakFDerivOn_iff_locally.2 fun z hz ↦ ?_⟩
  let y₀ := u ((φ.extend J).symm z)
  set W := Opens.interior ((φ.extend J).target ∩
    (φ.extend J).symm ⁻¹' (s ∩ (u ⁻¹' (chartAt H y₀).source ∩ (f ∘ u) ⁻¹' ψ'.source)))
  have hWsub : (W : Set ℂ) ⊆
      interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y₀).source)) :=
    interior_mono (inter_subset_inter_right _
      (preimage_mono (inter_subset_inter_right _ inter_subset_left)))
  exact ⟨W, φ.mem_interior_extend_target_inter_preimage
      (mem_of_superset (isOpen_interior.mem_nhds hz) (interior_subset.trans inter_subset_left))
      (mem_of_superset (((hu.continuousOn.isOpen_inter_preimage hs (chartAt H y₀).open_source).inter
        (hc.isOpen_inter_preimage hs ψ'.open_source)).mem_nhds
          ⟨⟨(interior_subset hz).2.1, mem_chart_source H y₀⟩, (interior_subset hz).2⟩)
        fun _ hx ↦ ⟨hx.1.1, hx.1.2, hx.2.2⟩),
    hasWeakFDerivOn_extend_comp (IsManifold.chart_mem_maximalAtlas y₀) hψ' (hf.of_le hn) ht
      ((hu.hasWeakFDerivOn_chart hφ (IsManifold.chart_mem_maximalAtlas y₀)).mono hWsub)
      (φ.continuousOn_extend_comp_symm (chartAt H y₀) hu.continuousOn (hWsub.trans interior_subset))
      fun w hw ↦ ⟨(interior_subset hw).2.2.1, hst (interior_subset hw).2.1,
        (interior_subset hw).2.2.2⟩⟩

/-- Global weak chain rule for postcomposition with a `C^n` (`1 ≤ n`) map `f : M → N`. -/
theorem _root_.ContMDiff.comp_hasWeakMFDerivGroupoid [IsManifold I ∞ M] [I.Boundaryless]
    [CompleteSpace F'] {n : ℕ∞ω} {f : M → N}
    (hf : ContMDiff I I' n f) (hu : HasWeakMFDerivGroupoid G J I u du) (hn : 1 ≤ n) :
    HasWeakMFDerivGroupoid G J I' (f ∘ u) (fun x ↦ (mfderiv I I' f (u x)).comp (du x)) :=
  hasWeakMFDerivOnGroupoid_univ.1 ((hasWeakMFDerivOnGroupoid_univ.2 hu).contMDiffOn_comp
    hf.contMDiffOn hn isOpen_univ isOpen_univ (mapsTo_univ _ _))

/-- Postcomposing `u : X → M` with a `C^n` (`1 ≤ n`) diffeomorphism `e : M ≃ₘ^n⟮I, I'⟯ N` of
boundaryless smooth targets transforms weak differentials on `s` by `mfderiv I I' e`. -/
theorem _root_.Diffeomorph.hasWeakMFDerivOnGroupoid_diffeomorph_comp_iff
    [IsManifold I ∞ M] [I.Boundaryless] [CompleteSpace F]
    [IsManifold I' ∞ N] [I'.Boundaryless] [CompleteSpace F']
    {n : ℕ∞ω} (e : M ≃ₘ^n⟮I, I'⟯ N) (hn : 1 ≤ n) (hs : IsOpen s) :
    HasWeakMFDerivOnGroupoid G J I' (e ∘ u) (fun x ↦ (mfderiv I I' e (u x)).comp (du x)) s ↔
      HasWeakMFDerivOnGroupoid G J I u du s := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.contMDiffOn_comp e.contMDiff.contMDiffOn hn hs isOpen_univ
    (mapsTo_univ _ _)⟩
  refine (h.contMDiffOn_comp e.symm.contMDiff.contMDiffOn hn hs isOpen_univ
    (mapsTo_univ _ _)).congr (fun x _ ↦ e.symm_apply_apply (u x)) fun x _ ↦ ?_
  simp only [Function.comp_apply]
  rw [← ContinuousLinearMap.comp_assoc (mfderiv I' I e.symm _),
    ← e.symm.mfderiv_diffeomorph_comp (zero_lt_one.trans_le hn).ne' e (u x)]
  have hid : ∀ g : M → M, g = id → (tangentSpaceCast I (g (u x)) (u x)).toContinuousLinearMap.comp
      ((mfderiv I I g (u x)).comp (du x)) = du x := by rintro _ rfl; rw [mfderiv_id]; rfl
  exact hid ((e.symm : N → M) ∘ e) (funext e.symm_apply_apply)

/-- Global target-diffeomorphism equivalence for `HasWeakMFDerivGroupoid`. -/
theorem _root_.Diffeomorph.hasWeakMFDerivGroupoid_diffeomorph_comp_iff
    [IsManifold I ∞ M] [I.Boundaryless] [CompleteSpace F]
    [IsManifold I' ∞ N] [I'.Boundaryless] [CompleteSpace F']
    {n : ℕ∞ω} (e : M ≃ₘ^n⟮I, I'⟯ N) (hn : 1 ≤ n) :
    HasWeakMFDerivGroupoid G J I' (e ∘ u) (fun x ↦ (mfderiv I I' e (u x)).comp (du x)) ↔
      HasWeakMFDerivGroupoid G J I u du := by
  rw [← hasWeakMFDerivOnGroupoid_univ, ← hasWeakMFDerivOnGroupoid_univ]
  exact e.hasWeakMFDerivOnGroupoid_diffeomorph_comp_iff hn isOpen_univ

section SourceDiffeomorph

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace H' Y] {G' : StructureGroupoid H'} {n : ℕ∞ω}

/-- Precomposing `u : X → M` with a `C^n` (`1 ≤ n`) diffeomorphism `e : Y ≃ₘ^n⟮J, J⟯ X` whose
inverse transports `G'`-charts into `G`-charts pulls `du` back along `e`. -/
theorem _root_.Diffeomorph.hasWeakMFDerivOnGroupoid_comp_diffeomorph
    (hG' : G'.maximalAtlas Y ⊆ IsManifold.maximalAtlas J 1 Y) (e : Y ≃ₘ^n⟮J, J⟯ X) (hn : 1 ≤ n)
    (he : ∀ φ ∈ G'.maximalAtlas Y,
      e.symm.toHomeomorph.toOpenPartialHomeomorph.trans φ ∈ G.maximalAtlas X)
    (hu : HasWeakMFDerivOnGroupoid G J I u du s) :
    HasWeakMFDerivOnGroupoid G' J I (u ∘ e)
      (fun y ↦ (du (e y)).comp (mfderiv J J e y)) (e ⁻¹' s) := by
  refine hasWeakMFDerivOnGroupoid_iff.2
    ⟨hu.continuousOn.comp e.continuous.continuousOn (mapsTo_preimage e s), fun φ hφ ψ hψ ↦ ?_⟩
  set φ' : OpenPartialHomeomorph X H' := e.symm.toHomeomorph.toOpenPartialHomeomorph.trans φ
  have hchart := hu.hasWeakFDerivOn_chart (φ := φ') (he φ hφ) hψ
  have htgt : (φ'.extend J).target = (φ.extend J).target := by ext; simp [φ', mfld_simps]
  have hs' : ⇑(φ'.extend J).symm = e ∘ ⇑(φ.extend J).symm := by ext; simp [φ', mfld_simps]
  have hdom : Opens.interior ((φ'.extend J).target ∩ (φ'.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) =
      Opens.interior ((φ.extend J).target ∩
        (φ.extend J).symm ⁻¹' (e ⁻¹' s ∩ (u ∘ e) ⁻¹' ψ.source)) :=
    Opens.ext (congrArg interior (by rw [htgt, hs']; ext; simp))
  rw [hdom] at hchart
  refine (hchart.congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards with z; simp only [Function.comp_apply, hs']
  · filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with z hz
    have hzint : z ∈ interior (φ.extend J).target := interior_mono inter_subset_left hz
    have hzR := mem_of_superset (mem_interior_iff_mem_nhds.1 hzint) φ.extend_target_subset_range
    obtain ⟨hdφ, -⟩ := φ.mdifferentiableAt_extend_symm_of_mem_interior (hG' hφ) hzint
    have hgen : ∀ g : ℂ → X, g = e ∘ ⇑(φ.extend J).symm →
        mvfderiv I (ψ.extend I) (u (g z)) ∘L du (g z) ∘L
          (mfderiv 𝓘(ℝ, ℂ) J g z ∘L
            (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm.toContinuousLinearMap) =
        chartTangentHom J I φ ψ (u ∘ e) (fun y ↦ (du (e y)).comp (mfderiv J J e y)) z := by
      rintro _ rfl
      simp only [chartTangentHom_apply, mfderivWithin_of_mem_nhds hzR, Function.comp_apply,
        mfderiv_comp z (e.mdifferentiable (zero_lt_one.trans_le hn).ne' _) hdφ,
        ContinuousLinearMap.comp_assoc]
    rw [chartTangentHom_apply, mfderivWithin_of_mem_nhds hzR]
    exact hgen _ hs'

/-- Equivalence of weak differentials under precomposition with a `C^n` (`1 ≤ n`) diffeomorphism
`e : Y ≃ₘ^n⟮J, J⟯ X` preserving the maximal atlases of `G` and `G'`. -/
theorem _root_.Diffeomorph.hasWeakMFDerivOnGroupoid_comp_diffeomorph_iff
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    (hG' : G'.maximalAtlas Y ⊆ IsManifold.maximalAtlas J 1 Y) (e : Y ≃ₘ^n⟮J, J⟯ X) (hn : 1 ≤ n)
    (he : ∀ φ ∈ G'.maximalAtlas Y,
      e.symm.toHomeomorph.toOpenPartialHomeomorph.trans φ ∈ G.maximalAtlas X)
    (hesymm : ∀ φ ∈ G.maximalAtlas X,
      e.toHomeomorph.toOpenPartialHomeomorph.trans φ ∈ G'.maximalAtlas Y) :
    HasWeakMFDerivOnGroupoid G' J I (u ∘ e)
        (fun y ↦ (du (e y)).comp (mfderiv J J e y)) (e ⁻¹' s) ↔
      HasWeakMFDerivOnGroupoid G J I u du s := by
  refine ⟨fun h ↦ ?_, e.hasWeakMFDerivOnGroupoid_comp_diffeomorph hG' hn he⟩
  have hback := e.symm.hasWeakMFDerivOnGroupoid_comp_diffeomorph hG hn hesymm h
  simp only [preimage_preimage, e.apply_symm_apply, preimage_id'] at hback
  refine hback.congr (fun x _ ↦ congrArg u (e.apply_symm_apply x)) fun x _ ↦ ?_
  rw [ContinuousLinearMap.comp_assoc (du _),
    ← e.mfderiv_diffeomorph_comp (zero_lt_one.trans_le hn).ne' e.symm x]
  have hid : ∀ g : X → X, g = id → (tangentSpaceCast I (u (g x)) (u x)).toContinuousLinearMap.comp
      ((du (g x)).comp (mfderiv J J g x)) = du x := by
    rintro _ rfl; rw [mfderiv_id]; rfl
  exact hid ((e : Y → X) ∘ e.symm) (funext e.apply_symm_apply)

/-- Global source-diffeomorphism equivalence for `HasWeakMFDerivGroupoid`. -/
theorem _root_.Diffeomorph.hasWeakMFDerivGroupoid_comp_diffeomorph_iff
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    (hG' : G'.maximalAtlas Y ⊆ IsManifold.maximalAtlas J 1 Y) (e : Y ≃ₘ^n⟮J, J⟯ X) (hn : 1 ≤ n)
    (he : ∀ φ ∈ G'.maximalAtlas Y,
      e.symm.toHomeomorph.toOpenPartialHomeomorph.trans φ ∈ G.maximalAtlas X)
    (hesymm : ∀ φ ∈ G.maximalAtlas X,
      e.toHomeomorph.toOpenPartialHomeomorph.trans φ ∈ G'.maximalAtlas Y) :
    HasWeakMFDerivGroupoid G' J I (u ∘ e) (fun y ↦ (du (e y)).comp (mfderiv J J e y)) ↔
      HasWeakMFDerivGroupoid G J I u du := by
  rw [← hasWeakMFDerivOnGroupoid_univ, ← hasWeakMFDerivOnGroupoid_univ, ← preimage_univ (f := e)]
  exact e.hasWeakMFDerivOnGroupoid_comp_diffeomorph_iff hG hG' hn he hesymm

end SourceDiffeomorph

/-! ### Existence of a global weak differential -/

private def pullbackChartDeriv [IsManifold J 1 X] [IsManifold I 1 M]
    (u : X → M) (x₀ : X) (y₀ : M) (D : ℂ → ℂ →L[ℝ] F) (x : X) :
    TangentSpace J x →L[ℝ] TangentSpace I (u x) :=
  (trivializationAt F (TangentSpace I) y₀).symmL ℝ (u x) ∘L D (extChartAt J x₀ x) ∘L
    (trivializationAt ℂ (TangentSpace J) x₀).continuousLinearMapAt ℝ x

private theorem chartTangentHom_pullbackChartDeriv [IsManifold J 1 X] [IsManifold I 1 M]
    {x₀ x : X} {y₀ : M} (D : ℂ → ℂ →L[ℝ] F)
    (hx : x ∈ (chartAt H' x₀).source) (hy : u x ∈ (chartAt H y₀).source) :
    chartTangentHom J I (chartAt H' x₀) (chartAt H y₀) u (pullbackChartDeriv u x₀ y₀ D)
        (extChartAt J x₀ x) = D (extChartAt J x₀ x) := by
  rw [chartTangentHom_chartAt_eq_inCoordinates _ hx hy]; ext v
  simp only [ContinuousLinearMap.inCoordinates, pullbackChartDeriv, ContinuousLinearMap.comp_apply,
    (trivializationAt ℂ (TangentSpace J) x₀).continuousLinearMapAt_symmL (R := ℝ)
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hx),
    (trivializationAt F (TangentSpace I) y₀).continuousLinearMapAt_symmL (R := ℝ)
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hy)]

private theorem exists_local_hasWeakMFDerivOnGroupoid
    [IsManifold J 1 X] [HasGroupoid X G] [IsManifold I ∞ M] [I.Boundaryless]
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    (hu : MemWkpLocMapOnGroupoid G J I p 1 u s) (hs : IsOpen s) (x₀ : X) :
    ∃ d : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x), HasWeakMFDerivOnGroupoid G J I u d
      (s ∩ ((chartAt H' x₀).source ∩ u ⁻¹' (chartAt H (u x₀)).source)) := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  obtain ⟨D, hD, -⟩ := (hu.memWkpLoc_chart (StructureGroupoid.chart_mem_maximalAtlas G x₀)
    (IsManifold.chart_mem_maximalAtlas (u x₀))).exists_weakFDeriv
  have := hD.completeSpace
  refine ⟨pullbackChartDeriv u x₀ (u x₀) D,
    (hasWeakMFDerivOnGroupoid_iff_of_subset_maximalAtlas hG
      (isOpen_inter_inter_preimage hu.continuousOn hs (chartAt H' x₀).open_source
        (chartAt H (u x₀)).open_source)
      (singleton_subset_iff.2 (StructureGroupoid.chart_mem_maximalAtlas G x₀))
      (fun _ hx ↦ ⟨_, rfl, hx.2.1⟩)
      (singleton_subset_iff.2 (IsManifold.chart_mem_maximalAtlas (u x₀)))
      (fun _ hx ↦ ⟨_, rfl, hx.2.2⟩)).2 ⟨hu.continuousOn.mono inter_subset_left, ?_⟩⟩
  rintro _ rfl _ rfl
  have hsub : s ∩ ((chartAt H' x₀).source ∩ u ⁻¹' (chartAt H (u x₀)).source) ∩
      u ⁻¹' (chartAt H (u x₀)).source ⊆ s ∩ u ⁻¹' (chartAt H (u x₀)).source :=
    fun _ hx ↦ ⟨hx.1.1, hx.2⟩
  refine (hD.mono (interior_mono (inter_subset_inter_right _ (preimage_mono hsub)))).congr_ae_deriv
    ?_
  filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with z hz
  have heq := chartTangentHom_pullbackChartDeriv (u := u) (J := J) (I := I) D
    (interior_subset hz).2.1.2.1 (interior_subset hz).2.2
  rwa [extChartAt, ((chartAt H' x₀).extend J).right_inv (interior_subset hz).1, eq_comm] at heq

omit [ChartedSpace H' X] in
private theorem exists_nat_subcover [SecondCountableTopology X] (hne : s.Nonempty) {U : X → Set X}
    (hUo : ∀ x₀, IsOpen (U x₀)) (hUmem : ∀ x ∈ s, x ∈ U x) (hUsub : ∀ x₀, U x₀ ⊆ s) :
    ∃ c : ℕ → X, s = ⋃ n : ℕ, U (c n) := by
  obtain ⟨T, hTcnt, hTcov⟩ := isOpen_iUnion_countable (fun i : s ↦ U i.1) (fun i ↦ hUo i.1)
  have hTs : s = ⋃ i ∈ T, U i.1 := Subset.antisymm
    (fun x hxs ↦ by rw [hTcov]; exact mem_iUnion.2 ⟨⟨x, hxs⟩, hUmem x hxs⟩)
    (iUnion₂_subset fun _ _ ↦ hUsub _)
  obtain ⟨x₁, hx₁s⟩ := hne
  rcases mem_iUnion₂.1 (hTs ▸ hx₁s) with ⟨i₀, hi₀T, -⟩
  obtain ⟨q, rfl⟩ := hTcnt.exists_eq_range ⟨i₀, hi₀T⟩
  exact ⟨fun n ↦ (q n).1, by simpa only [biUnion_range] using hTs⟩

private theorem exists_hasWeakMFDerivOnGroupoid_iUnion_nat
    [IsManifold J 1 X] [HasGroupoid X G] [IsManifold I ∞ M] [CompleteSpace F]
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X) {V : ℕ → Set X}
    (hVo : ∀ n, IsOpen (V n)) (hV : ∀ n, ∃ d, HasWeakMFDerivOnGroupoid G J I u d (V n)) :
    ∃ du, HasWeakMFDerivOnGroupoid G J I u du (⋃ n : ℕ, V n) := by
  choose d hd using hV
  classical
  let du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x) := fun x ↦
    if h : ∃ n : ℕ, x ∈ V n then d (Nat.find h) x else 0
  refine ⟨du, (hasWeakMFDerivOnGroupoid_iUnion_iff hVo).2 fun n ↦
    (hd n).congr_deriv_of_isNullSet hG ((IsNullSet.iUnion fun k : ℕ ↦
      ((hd n).mono inter_subset_left).isNullSet_ne ((hVo n).inter (hVo k))
        ((hd k).mono inter_subset_right)).mono fun x ⟨hxn, hxne⟩ ↦ ?_)⟩
  have hex : ∃ k : ℕ, x ∈ V k := ⟨n, hxn⟩
  exact mem_iUnion.2 ⟨Nat.find hex, ⟨hxn, Nat.find_spec hex⟩,
    fun heq ↦ hxne (by simp only [du, hex, ↓reduceDIte, heq])⟩

section Existence

variable [LindelofSpace X] [IsManifold J 1 X] [HasGroupoid X G] [IsManifold I ∞ M] [I.Boundaryless]

/-- **Existence of a global weak differential** on an open subset `s` of a Lindelöf surface `X`
(with or without boundary) for maps of order `1` into a boundaryless smooth manifold `M`. -/
theorem MemWkpLocMapOnGroupoid.exists_hasWeakMFDerivOnGroupoid
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    (hu : MemWkpLocMapOnGroupoid G J I p 1 u s) (hs : IsOpen s) :
    ∃ du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x),
      HasWeakMFDerivOnGroupoid G J I u du s := by
  rcases isEmpty_or_nonempty X with _ | ⟨⟨x₀⟩⟩
  · exact ⟨fun _ ↦ 0, hasWeakMFDerivOnGroupoid_iff.2
      ⟨fun x _ ↦ isEmptyElim x, fun φ _ _ _ ↦ isEmptyElim (φ.symm (J.symm 0))⟩⟩
  have := (hu.memWkpLoc_chart (StructureGroupoid.chart_mem_maximalAtlas G x₀)
    (IsManifold.chart_mem_maximalAtlas (u x₀))).completeSpace
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ ↦ 0, hasWeakMFDerivOnGroupoid_empty⟩
  have := J.secondCountableTopology; have := ChartedSpace.secondCountable_of_lindelof H' X
  let U : X → Set X := fun x₁ ↦ s ∩ ((chartAt H' x₁).source ∩ u ⁻¹' (chartAt H (u x₁)).source)
  have hUo : ∀ x₁, IsOpen (U x₁) := fun x₁ ↦ isOpen_inter_inter_preimage hu.continuousOn hs
    (chartAt H' x₁).open_source (chartAt H (u x₁)).open_source
  obtain ⟨c, hcov⟩ := exists_nat_subcover hne hUo
    (fun x hxs ↦ ⟨hxs, mem_chart_source H' x, mem_chart_source H (u x)⟩) (fun _ ↦ inter_subset_left)
  exact hcov ▸ exists_hasWeakMFDerivOnGroupoid_iUnion_nat hG (fun n ↦ hUo (c n))
    fun n ↦ exists_local_hasWeakMFDerivOnGroupoid hG hu hs (c n)

/-- Global existence of a weak differential for a structure groupoid `G`. -/
theorem MemWkpLocMapGroupoid.exists_hasWeakMFDerivGroupoid
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    (hu : MemWkpLocMapGroupoid G J I p 1 u) :
    ∃ du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x),
      HasWeakMFDerivGroupoid G J I u du :=
  let ⟨du, hdu⟩ := (memWkpLocMapOnGroupoid_univ.2 hu).exists_hasWeakMFDerivOnGroupoid hG isOpen_univ
  ⟨du, hasWeakMFDerivOnGroupoid_univ.1 hdu⟩

/-- **First-order Sobolev characterization at groupoid generality** on open `s ⊆ X`. -/
theorem memWkpLocMapOnGroupoid_one_iff_exists_hasWeakMFDerivOnGroupoid
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X) (hs : IsOpen s) :
    MemWkpLocMapOnGroupoid G J I p 1 u s ↔ ∃ du, HasWeakMFDerivOnGroupoid G J I u du s ∧
      ∀ φ ∈ G.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
        MemLpLoc p ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
          (chartTangentHom J I φ ψ u du) :=
  ⟨fun hu ↦ let ⟨du, hdu⟩ := hu.exists_hasWeakMFDerivOnGroupoid hG hs
    ⟨du, hdu, (hdu.memWkpLocMapOnGroupoid_one_iff hs).1 hu⟩,
   fun ⟨_, hdu, hLp⟩ ↦ (hdu.memWkpLocMapOnGroupoid_one_iff hs).2 hLp⟩

/-- Global first-order Sobolev characterization at groupoid generality. -/
theorem memWkpLocMapGroupoid_one_iff_exists_hasWeakMFDerivGroupoid
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X) :
    MemWkpLocMapGroupoid G J I p 1 u ↔ ∃ du, HasWeakMFDerivGroupoid G J I u du ∧
      ∀ φ ∈ G.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
        MemLpLoc p ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (u ⁻¹' ψ.source))
          (chartTangentHom J I φ ψ u du) := by
  rw [← memWkpLocMapOnGroupoid_univ,
    memWkpLocMapOnGroupoid_one_iff_exists_hasWeakMFDerivOnGroupoid hG isOpen_univ]
  simp only [hasWeakMFDerivOnGroupoid_univ, univ_inter]

end Existence

end Transitions

/-! ### Riemann surfaces without boundary -/

section BoundarylessSurface

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {p : ENNReal} {u : X → M}
  {du : ∀ x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)} {s : Set X}

/-- **Chart independence** on a Riemann surface without boundary: covering subfamilies suffice. -/
theorem hasWeakMFDerivOn_iff_of_subset_maximalAtlas [I.Boundaryless] [CompleteSpace F]
    (hs : IsOpen s) {A : Set (OpenPartialHomeomorph X ℂ)}
    (hA : A ⊆ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) (hAs : ∀ x ∈ s, ∃ φ ∈ A, x ∈ φ.source)
    {B : Set (OpenPartialHomeomorph M H)} (hB : B ⊆ IsManifold.maximalAtlas I ∞ M)
    (hBs : ∀ x ∈ s, ∃ ψ ∈ B, u x ∈ ψ.source) :
    HasWeakMFDerivOn I u du s ↔ ContinuousOn u s ∧ ∀ φ ∈ A, ∀ ψ ∈ B,
      HasWeakFDerivOn volume (Opens.interior (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ φ.symm) (chartTangentHom 𝓘(ℝ, ℂ) I φ ψ u du) := by
  rw [HasWeakMFDerivOn, hasWeakMFDerivOnGroupoid_iff_of_subset_maximalAtlas
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero) hs hA hAs hB hBs]
  simp only [OpenPartialHomeomorph.extend_modelWithCornersSelf,
    OpenPartialHomeomorph.coe_toPartialEquiv_symm]

/-- Global chart independence for covering subfamilies on a Riemann surface without boundary. -/
theorem hasWeakMFDeriv_iff_of_subset_maximalAtlas [I.Boundaryless] [CompleteSpace F]
    {A : Set (OpenPartialHomeomorph X ℂ)} (hA : A ⊆ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hAs : ∀ x : X, ∃ φ ∈ A, x ∈ φ.source) {B : Set (OpenPartialHomeomorph M H)}
    (hB : B ⊆ IsManifold.maximalAtlas I ∞ M) (hBs : ∀ x : X, ∃ ψ ∈ B, u x ∈ ψ.source) :
    HasWeakMFDeriv I u du ↔ Continuous u ∧ ∀ φ ∈ A, ∀ ψ ∈ B,
      HasWeakFDerivOn volume (Opens.interior (φ.target ∩ φ.symm ⁻¹' (u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ φ.symm) (chartTangentHom 𝓘(ℝ, ℂ) I φ ψ u du) := by
  refine hasWeakMFDerivOnGroupoid_univ.symm.trans
    ((hasWeakMFDerivOn_iff_of_subset_maximalAtlas isOpen_univ hA (fun x _ ↦ hAs x) hB
      (fun x _ ↦ hBs x)).trans ?_)
  simp only [continuousOn_univ, univ_inter]

section SurfaceAtlas

variable [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] [I.Boundaryless]

/-- Chart independence: testing the given atlases of `X` and `M` suffices. -/
theorem hasWeakMFDerivOn_iff_atlas (hs : IsOpen s) :
    HasWeakMFDerivOn I u du s ↔ ContinuousOn u s ∧ ∀ φ ∈ atlas ℂ X, ∀ ψ ∈ atlas H M,
      HasWeakFDerivOn volume (Opens.interior (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ φ.symm) (chartTangentHom 𝓘(ℝ, ℂ) I φ ψ u du) := by
  rw [HasWeakMFDerivOn, hasWeakMFDerivOnGroupoid_iff_atlas
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero) hs]
  simp only [OpenPartialHomeomorph.extend_modelWithCornersSelf,
    OpenPartialHomeomorph.coe_toPartialEquiv_symm]

/-- Global chart independence: testing the given atlases of `X` and `M` suffices. -/
theorem hasWeakMFDeriv_iff_atlas :
    HasWeakMFDeriv I u du ↔ Continuous u ∧ ∀ φ ∈ atlas ℂ X, ∀ ψ ∈ atlas H M,
      HasWeakFDerivOn volume (Opens.interior (φ.target ∩ φ.symm ⁻¹' (u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ φ.symm) (chartTangentHom 𝓘(ℝ, ℂ) I φ ψ u du) := by
  refine hasWeakMFDerivOnGroupoid_univ.symm.trans
    ((hasWeakMFDerivOn_iff_atlas isOpen_univ).trans ?_)
  simp only [continuousOn_univ, univ_inter]

/-- Chart independence: testing `chartAt ℂ x` and `chartAt H y` suffices. -/
theorem hasWeakMFDerivOn_iff_chartAt (hs : IsOpen s) :
    HasWeakMFDerivOn I u du s ↔ ContinuousOn u s ∧ ∀ x : X, ∀ y : M, HasWeakFDerivOn volume
      (Opens.interior
        ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y).source)))
      (extChartAt I y ∘ u ∘ (chartAt ℂ x).symm)
      (chartTangentHom 𝓘(ℝ, ℂ) I (chartAt ℂ x) (chartAt H y) u du) := by
  rw [HasWeakMFDerivOn, hasWeakMFDerivOnGroupoid_iff_chartAt
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero) hs]
  simp only [extChartAt, OpenPartialHomeomorph.extend_modelWithCornersSelf,
    OpenPartialHomeomorph.coe_toPartialEquiv_symm]

/-- Global chart independence: testing the preferred charts of `X` and `M` suffices. -/
theorem hasWeakMFDeriv_iff_chartAt :
    HasWeakMFDeriv I u du ↔ Continuous u ∧ ∀ x : X, ∀ y : M, HasWeakFDerivOn volume
      (Opens.interior ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (u ⁻¹' (chartAt H y).source)))
      (extChartAt I y ∘ u ∘ (chartAt ℂ x).symm)
      (chartTangentHom 𝓘(ℝ, ℂ) I (chartAt ℂ x) (chartAt H y) u du) := by
  refine hasWeakMFDerivOnGroupoid_univ.symm.trans
    ((hasWeakMFDerivOn_iff_chartAt isOpen_univ).trans ?_)
  simp only [continuousOn_univ, univ_inter]

end SurfaceAtlas

/-- Equivalence between `HasWeakMFDerivOn 𝓘(ℝ, F)` and `HasWeakFDerivOn volume Ω u` on `Ω ⊆ ℂ`. -/
theorem hasWeakMFDerivOn_model_iff {u : ℂ → F}
    {du : ∀ z : ℂ, TangentSpace 𝓘(ℝ, ℂ) z →L[ℝ] TangentSpace 𝓘(ℝ, F) (u z)} {Ω : Opens ℂ} :
    HasWeakMFDerivOn 𝓘(ℝ, F) u du Ω ↔ ContinuousOn u Ω ∧ HasWeakFDerivOn volume Ω u fun z ↦
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (u z)).toContinuousLinearMap ∘L du z ∘L
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm.toContinuousLinearMap := by
  have hdom (x : ℂ) (y : F) : Opens.interior ((chartAt ℂ x).target ∩
      (chartAt ℂ x).symm ⁻¹' ((Ω : Set ℂ) ∩ u ⁻¹' (chartAt F y).source)) = Ω :=
    Opens.ext (by simp [chartAt_self_eq])
  have hextF (x : ℂ) (y : F) : extChartAt 𝓘(ℝ, F) y ∘ u ∘ (chartAt ℂ x).symm = u := by
    ext; simp [chartAt_self_eq]
  have hch (x : ℂ) (y : F) : chartTangentHom 𝓘(ℝ, ℂ) 𝓘(ℝ, F) (chartAt ℂ x) (chartAt F y) u du =
      fun z ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) (u z)).toContinuousLinearMap ∘L
        du z ∘L (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm.toContinuousLinearMap := by
    rw [chartAt_self_eq, chartAt_self_eq]; exact funext (chartTangentHom_refl du)
  rw [hasWeakMFDerivOn_iff_chartAt Ω.isOpen]; simp only [hdom, hextF, hch]
  exact and_congr_right fun _ ↦ ⟨fun h ↦ h 0 (u 0), fun h _ _ ↦ h⟩

section Biholomorph

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] {n : ℕ∞ω}

private def toRealDiffeomorph (e : Y ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) (hn : 1 ≤ n) :
    Y ≃ₘ^1⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ X :=
  ⟨e.toEquiv,
    by simpa [modelWithCornersSelf_restrictScalars] using (e.contMDiff.of_le hn).restrictScalars ℝ,
    by simpa [modelWithCornersSelf_restrictScalars] using
      (e.symm.contMDiff.of_le hn).restrictScalars ℝ⟩

private theorem mem_maximalAtlas_of_biholomorph {Z W : Type*} [TopologicalSpace Z]
    [ChartedSpace ℂ Z] [TopologicalSpace W] [ChartedSpace ℂ W] [IsManifold 𝓘(ℂ) 1 W]
    {e' : W ≃ₘ^1⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ Z} (e : W ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ Z) (hn : 1 ≤ n)
    (he' : e'.toPartialEquiv = e.toPartialEquiv) {φ : OpenPartialHomeomorph Z ℂ}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 Z) :
    e'.toHomeomorph.toOpenPartialHomeomorph.trans φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 W := by
  have h : e'.toHomeomorph.toOpenPartialHomeomorph =
      (e.toPartialDiffeomorph.ofLE hn).toOpenPartialHomeomorph :=
    OpenPartialHomeomorph.toPartialEquiv_injective
      (he'.trans ((e.toPartialDiffeomorph.ofLE_toPartialEquiv hn).trans
        e.toPartialDiffeomorph_toPartialEquiv).symm)
  exact h ▸ (e.toPartialDiffeomorph.ofLE hn).trans_mem_maximalAtlas hφ

variable [IsManifold 𝓘(ℂ) 1 X]

/-- Precomposing `u : X → M` with a biholomorphism `e : Y ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X` (`1 ≤ n`) pulls `du`
on `s` back to `y ↦ (du (e y)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e y)` on `e ⁻¹' s`. -/
theorem _root_.Diffeomorph.hasWeakMFDerivOn_comp_diffeomorph
    (e : Y ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) (hn : 1 ≤ n) (hu : HasWeakMFDerivOn I u du s) :
    HasWeakMFDerivOn I (u ∘ e) (fun y ↦ (du (e y)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e y)) (e ⁻¹' s) :=
  (toRealDiffeomorph e hn).hasWeakMFDerivOnGroupoid_comp_diffeomorph
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero) le_rfl
    (fun _ hφ ↦ mem_maximalAtlas_of_biholomorph e.symm hn rfl hφ) hu

/-- Global precomposition of a weak differential with a biholomorphism. -/
theorem _root_.Diffeomorph.hasWeakMFDeriv_comp_diffeomorph
    (e : Y ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) (hn : 1 ≤ n) (hu : HasWeakMFDeriv I u du) :
    HasWeakMFDeriv I (u ∘ e) (fun y ↦ (du (e y)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e y)) :=
  hasWeakMFDerivOnGroupoid_univ.1 (by simpa only [preimage_univ] using
    e.hasWeakMFDerivOn_comp_diffeomorph hn (hasWeakMFDerivOnGroupoid_univ.2 hu))

/-- Equivalence of weak differentials under precomposition with a biholomorphism (`1 ≤ n`). -/
theorem _root_.Diffeomorph.hasWeakMFDerivOn_comp_diffeomorph_iff [IsManifold 𝓘(ℂ) 1 Y]
    (e : Y ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) (hn : 1 ≤ n) :
    HasWeakMFDerivOn I (u ∘ e)
        (fun y ↦ (du (e y)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e y)) (e ⁻¹' s) ↔
      HasWeakMFDerivOn I u du s :=
  (toRealDiffeomorph e hn).hasWeakMFDerivOnGroupoid_comp_diffeomorph_iff
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero)
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero) le_rfl
    (fun _ hφ ↦ mem_maximalAtlas_of_biholomorph e.symm hn rfl hφ)
    (fun _ hφ ↦ mem_maximalAtlas_of_biholomorph e hn rfl hφ)

/-- Global equivalence of weak differentials under precomposition with a biholomorphism. -/
theorem _root_.Diffeomorph.hasWeakMFDeriv_comp_diffeomorph_iff [IsManifold 𝓘(ℂ) 1 Y]
    (e : Y ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) (hn : 1 ≤ n) :
    HasWeakMFDeriv I (u ∘ e) (fun y ↦ (du (e y)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e y)) ↔
      HasWeakMFDeriv I u du := by
  rw [HasWeakMFDeriv, HasWeakMFDeriv, ← hasWeakMFDerivOnGroupoid_univ,
    ← hasWeakMFDerivOnGroupoid_univ, ← preimage_univ (f := e)]
  exact e.hasWeakMFDerivOn_comp_diffeomorph_iff hn

end Biholomorph

section SurfaceExistence

variable [LindelofSpace X] [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] [I.Boundaryless]

/-- **Existence of a weak differential on a Riemann surface without boundary.** -/
theorem MemWkpLocMapOn.exists_hasWeakMFDerivOn (hu : MemWkpLocMapOn I p 1 u s) (hs : IsOpen s) :
    ∃ du : ∀ x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x), HasWeakMFDerivOn I u du s :=
  letI : IsManifold 𝓘(ℝ, ℂ) 1 X := IsManifold.restrictScalars_of_ne_zero 1 one_ne_zero inferInstance
  MemWkpLocMapOnGroupoid.exists_hasWeakMFDerivOnGroupoid
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero) hu hs

/-- **Global existence of a weak differential on a Riemann surface without boundary.** -/
theorem MemWkpLocMap.exists_hasWeakMFDeriv (hu : MemWkpLocMap I p 1 u) :
    ∃ du : ∀ x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x), HasWeakMFDeriv I u du :=
  letI : IsManifold 𝓘(ℝ, ℂ) 1 X := IsManifold.restrictScalars_of_ne_zero 1 one_ne_zero inferInstance
  MemWkpLocMapGroupoid.exists_hasWeakMFDerivGroupoid
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero) hu

/-- **First-order Sobolev characterization via preferred charts** on a Lindelöf Riemann surface. -/
theorem memWkpLocMapOn_one_iff_exists_hasWeakMFDerivOn (hs : IsOpen s) :
    MemWkpLocMapOn I p 1 u s ↔ ∃ du : ∀ x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x),
      HasWeakMFDerivOn I u du s ∧ ∀ x : X, ∀ y : M, MemLpLoc p
        ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y).source))
        (chartTangentHom 𝓘(ℝ, ℂ) I (chartAt ℂ x) (chartAt H y) u du) := by
  refine ⟨fun hu ↦ ?_, fun ⟨du, hdu, hLp⟩ ↦ ?_⟩
  · obtain ⟨du, hdu⟩ := MemWkpLocMapOn.exists_hasWeakMFDerivOn hu hs
    exact ⟨du, hdu, fun x y ↦ by
      simpa only [OpenPartialHomeomorph.extend_modelWithCornersSelf,
        OpenPartialHomeomorph.coe_toPartialEquiv_symm] using
          hdu.memLpLoc_chartTangentHom hu hs (IsManifold.chart_mem_maximalAtlas x)
            (IsManifold.chart_mem_maximalAtlas y)⟩
  · rcases isEmpty_or_nonempty X with _ | ⟨⟨x₀⟩⟩
    · exact memWkpLocMapOn_iff.2 ⟨fun x _ ↦ isEmptyElim x, fun φ _ _ _ ↦ isEmptyElim (φ.symm 0)⟩
    have := (hdu.hasWeakFDerivOn_chart (IsManifold.chart_mem_maximalAtlas x₀)
      (IsManifold.chart_mem_maximalAtlas (u x₀))).completeSpace
    refine (memWkpLocMapOn_iff_chartAt le_rfl hs).2 ⟨hdu.continuousOn, fun x y ↦ ?_⟩
    have hweak := hdu.hasWeakFDerivOn_chart (IsManifold.chart_mem_maximalAtlas x)
      (IsManifold.chart_mem_maximalAtlas y)
    simp only [OpenPartialHomeomorph.extend_modelWithCornersSelf,
      OpenPartialHomeomorph.coe_toPartialEquiv_symm] at hweak
    exact memWkpLoc_succ_iff.2 ⟨((chartAt ℂ x).continuousOn_comp_comp_symm
      (((chartAt H y).continuousOn_extend (I := I)).mono (chartAt H y).extend_source.ge)
      hdu.continuousOn).memLpLoc, _, hweak, memWkpLoc_zero_iff.2 (hLp x y)⟩

/-- Global first-order Sobolev characterization via preferred charts on a Riemann surface. -/
theorem memWkpLocMap_one_iff_exists_hasWeakMFDeriv :
    MemWkpLocMap I p 1 u ↔ ∃ du : ∀ x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x),
      HasWeakMFDeriv I u du ∧ ∀ x : X, ∀ y : M, MemLpLoc p
        ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (u ⁻¹' (chartAt H y).source))
        (chartTangentHom 𝓘(ℝ, ℂ) I (chartAt ℂ x) (chartAt H y) u du) := by
  refine memWkpLocMapOnGroupoid_univ.symm.trans
    ((memWkpLocMapOn_one_iff_exists_hasWeakMFDerivOn isOpen_univ).trans ?_)
  simp only [hasWeakMFDerivOnGroupoid_univ, univ_inter]

end SurfaceExistence

end BoundarylessSurface

/-! ### Riemann surfaces with boundary -/

section BorderedSurface

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ClosedUpperHalfPlane X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {p : ENNReal} {u : X → M}
  {du : ∀ x : X, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] TangentSpace I (u x)} {s : Set X}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace ClosedUpperHalfPlane Y] {n : ℕ∞ω}

/-- Chart independence of `HasWeakMFDerivOnBordered` for covering subfamilies. -/
theorem hasWeakMFDerivOnBordered_iff_of_subset_maximalAtlas [I.Boundaryless] [CompleteSpace F]
    (hs : IsOpen s) {A : Set (OpenPartialHomeomorph X ClosedUpperHalfPlane)}
    (hA : A ⊆ borderedHolomorphicGroupoid.maximalAtlas X) (hAs : ∀ x ∈ s, ∃ φ ∈ A, x ∈ φ.source)
    {B : Set (OpenPartialHomeomorph M H)} (hB : B ⊆ IsManifold.maximalAtlas I ∞ M)
    (hBs : ∀ x ∈ s, ∃ ψ ∈ B, u x ∈ ψ.source) :
    HasWeakMFDerivOnBordered I u du s ↔ ContinuousOn u s ∧ ∀ φ ∈ A, ∀ ψ ∈ B, HasWeakFDerivOn volume
      (Opens.interior ((φ.extend closedUpperHalfPlaneModel).target ∩
        (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
      (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm)
      (chartTangentHom closedUpperHalfPlaneModel I φ ψ u du) :=
  hasWeakMFDerivOnGroupoid_iff_of_subset_maximalAtlas
    borderedHolomorphicGroupoid_maximalAtlas_subset hs hA hAs hB hBs

/-- Global chart independence of `HasWeakMFDerivBordered` for covering subfamilies. -/
theorem hasWeakMFDerivBordered_iff_of_subset_maximalAtlas [I.Boundaryless] [CompleteSpace F]
    {A : Set (OpenPartialHomeomorph X ClosedUpperHalfPlane)}
    (hA : A ⊆ borderedHolomorphicGroupoid.maximalAtlas X) (hAs : ∀ x : X, ∃ φ ∈ A, x ∈ φ.source)
    {B : Set (OpenPartialHomeomorph M H)} (hB : B ⊆ IsManifold.maximalAtlas I ∞ M)
    (hBs : ∀ x : X, ∃ ψ ∈ B, u x ∈ ψ.source) :
    HasWeakMFDerivBordered I u du ↔ Continuous u ∧ ∀ φ ∈ A, ∀ ψ ∈ B, HasWeakFDerivOn volume
      (Opens.interior ((φ.extend closedUpperHalfPlaneModel).target ∩
        (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (u ⁻¹' ψ.source)))
      (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm)
      (chartTangentHom closedUpperHalfPlaneModel I φ ψ u du) :=
  hasWeakMFDerivGroupoid_iff_of_subset_maximalAtlas
    borderedHolomorphicGroupoid_maximalAtlas_subset hA hAs hB hBs

/-- Equivalence of weak differentials under precomposition with a bordered biholomorphism on `s`. -/
theorem _root_.Diffeomorph.hasWeakMFDerivOnBordered_comp_diffeomorph_iff
    (e : Y ≃ₘ^n⟮closedUpperHalfPlaneModel, closedUpperHalfPlaneModel⟯ X) (hn : 1 ≤ n)
    (he : ∀ φ ∈ borderedHolomorphicGroupoid.maximalAtlas Y,
      e.symm.toHomeomorph.toOpenPartialHomeomorph.trans φ ∈
        borderedHolomorphicGroupoid.maximalAtlas X)
    (hesymm : ∀ φ ∈ borderedHolomorphicGroupoid.maximalAtlas X,
      e.toHomeomorph.toOpenPartialHomeomorph.trans φ ∈
        borderedHolomorphicGroupoid.maximalAtlas Y) :
    HasWeakMFDerivOnBordered I (u ∘ e)
        (fun y ↦ (du (e y)).comp
          (mfderiv closedUpperHalfPlaneModel closedUpperHalfPlaneModel e y)) (e ⁻¹' s) ↔
      HasWeakMFDerivOnBordered I u du s :=
  e.hasWeakMFDerivOnGroupoid_comp_diffeomorph_iff borderedHolomorphicGroupoid_maximalAtlas_subset
    borderedHolomorphicGroupoid_maximalAtlas_subset hn he hesymm

/-- Global equivalence of weak differentials under precomposition with a bordered biholomorphism. -/
theorem _root_.Diffeomorph.hasWeakMFDerivBordered_comp_diffeomorph_iff
    (e : Y ≃ₘ^n⟮closedUpperHalfPlaneModel, closedUpperHalfPlaneModel⟯ X) (hn : 1 ≤ n)
    (he : ∀ φ ∈ borderedHolomorphicGroupoid.maximalAtlas Y,
      e.symm.toHomeomorph.toOpenPartialHomeomorph.trans φ ∈
        borderedHolomorphicGroupoid.maximalAtlas X)
    (hesymm : ∀ φ ∈ borderedHolomorphicGroupoid.maximalAtlas X,
      e.toHomeomorph.toOpenPartialHomeomorph.trans φ ∈
        borderedHolomorphicGroupoid.maximalAtlas Y) :
    HasWeakMFDerivBordered I (u ∘ e)
        (fun y ↦ (du (e y)).comp
          (mfderiv closedUpperHalfPlaneModel closedUpperHalfPlaneModel e y)) ↔
      HasWeakMFDerivBordered I u du :=
  e.hasWeakMFDerivGroupoid_comp_diffeomorph_iff borderedHolomorphicGroupoid_maximalAtlas_subset
    borderedHolomorphicGroupoid_maximalAtlas_subset hn he hesymm

section BorderedManifold

variable [HasGroupoid X borderedHolomorphicGroupoid] [IsManifold I ∞ M] [I.Boundaryless]

/-- Chart independence of `HasWeakMFDerivOnBordered` via `atlas` on `X` and `M`. -/
theorem hasWeakMFDerivOnBordered_iff_atlas (hs : IsOpen s) :
    HasWeakMFDerivOnBordered I u du s ↔ ContinuousOn u s ∧
      ∀ φ ∈ atlas ClosedUpperHalfPlane X, ∀ ψ ∈ atlas H M, HasWeakFDerivOn volume
        (Opens.interior ((φ.extend closedUpperHalfPlaneModel).target ∩
          (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm)
        (chartTangentHom closedUpperHalfPlaneModel I φ ψ u du) :=
  hasWeakMFDerivOnGroupoid_iff_atlas borderedHolomorphicGroupoid_maximalAtlas_subset hs

/-- Global chart independence of `HasWeakMFDerivBordered` via `atlas` on `X` and `M`. -/
theorem hasWeakMFDerivBordered_iff_atlas :
    HasWeakMFDerivBordered I u du ↔ Continuous u ∧
      ∀ φ ∈ atlas ClosedUpperHalfPlane X, ∀ ψ ∈ atlas H M, HasWeakFDerivOn volume
        (Opens.interior ((φ.extend closedUpperHalfPlaneModel).target ∩
          (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm)
        (chartTangentHom closedUpperHalfPlaneModel I φ ψ u du) :=
  hasWeakMFDerivGroupoid_iff_atlas borderedHolomorphicGroupoid_maximalAtlas_subset

/-- Chart independence of `HasWeakMFDerivOnBordered`: testing preferred charts suffices. -/
theorem hasWeakMFDerivOnBordered_iff_chartAt (hs : IsOpen s) :
    HasWeakMFDerivOnBordered I u du s ↔ ContinuousOn u s ∧ ∀ x : X, ∀ y : M, HasWeakFDerivOn volume
      (Opens.interior ((extChartAt closedUpperHalfPlaneModel x).target ∩
        (extChartAt closedUpperHalfPlaneModel x).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y).source)))
      (extChartAt I y ∘ u ∘ (extChartAt closedUpperHalfPlaneModel x).symm)
      (chartTangentHom closedUpperHalfPlaneModel I
        (chartAt ClosedUpperHalfPlane x) (chartAt H y) u du) :=
  hasWeakMFDerivOnGroupoid_iff_chartAt borderedHolomorphicGroupoid_maximalAtlas_subset hs

/-- Global chart independence of `HasWeakMFDerivBordered`: testing preferred charts suffices. -/
theorem hasWeakMFDerivBordered_iff_chartAt :
    HasWeakMFDerivBordered I u du ↔ Continuous u ∧ ∀ x : X, ∀ y : M, HasWeakFDerivOn volume
      (Opens.interior ((extChartAt closedUpperHalfPlaneModel x).target ∩
        (extChartAt closedUpperHalfPlaneModel x).symm ⁻¹' (u ⁻¹' (chartAt H y).source)))
      (extChartAt I y ∘ u ∘ (extChartAt closedUpperHalfPlaneModel x).symm)
      (chartTangentHom closedUpperHalfPlaneModel I
        (chartAt ClosedUpperHalfPlane x) (chartAt H y) u du) :=
  hasWeakMFDerivGroupoid_iff_chartAt borderedHolomorphicGroupoid_maximalAtlas_subset

/-- **Existence of a weak differential on a Riemann surface with boundary.** -/
theorem MemWkpLocMapOnBordered.exists_hasWeakMFDerivOnBordered [LindelofSpace X]
    (hu : MemWkpLocMapOnBordered I p 1 u s) (hs : IsOpen s) :
    ∃ du, HasWeakMFDerivOnBordered I u du s :=
  MemWkpLocMapOnGroupoid.exists_hasWeakMFDerivOnGroupoid
    borderedHolomorphicGroupoid_maximalAtlas_subset hu hs

/-- **Global existence of a weak differential on a Riemann surface with boundary.** -/
theorem MemWkpLocMapBordered.exists_hasWeakMFDerivBordered [LindelofSpace X]
    (hu : MemWkpLocMapBordered I p 1 u) : ∃ du, HasWeakMFDerivBordered I u du :=
  MemWkpLocMapGroupoid.exists_hasWeakMFDerivGroupoid
    borderedHolomorphicGroupoid_maximalAtlas_subset hu

/-- First-order Sobolev characterization on an open subset of a Lindelöf bordered surface. -/
theorem memWkpLocMapOnBordered_one_iff_exists_hasWeakMFDerivOnBordered [LindelofSpace X]
    (hs : IsOpen s) : MemWkpLocMapOnBordered I p 1 u s ↔ ∃ du, HasWeakMFDerivOnBordered I u du s ∧
      ∀ φ ∈ borderedHolomorphicGroupoid.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
        MemLpLoc p ((φ.extend closedUpperHalfPlaneModel).target ∩
          (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
          (chartTangentHom closedUpperHalfPlaneModel I φ ψ u du) :=
  memWkpLocMapOnGroupoid_one_iff_exists_hasWeakMFDerivOnGroupoid
    borderedHolomorphicGroupoid_maximalAtlas_subset hs

/-- Global first-order Sobolev characterization on a Lindelöf bordered Riemann surface. -/
theorem memWkpLocMapBordered_one_iff_exists_hasWeakMFDerivBordered [LindelofSpace X] :
    MemWkpLocMapBordered I p 1 u ↔ ∃ du, HasWeakMFDerivBordered I u du ∧
      ∀ φ ∈ borderedHolomorphicGroupoid.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
        MemLpLoc p ((φ.extend closedUpperHalfPlaneModel).target ∩
          (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (u ⁻¹' ψ.source))
          (chartTangentHom closedUpperHalfPlaneModel I φ ψ u du) :=
  memWkpLocMapGroupoid_one_iff_exists_hasWeakMFDerivGroupoid
    borderedHolomorphicGroupoid_maximalAtlas_subset

end BorderedManifold

end BorderedSurface

end TauCeti
