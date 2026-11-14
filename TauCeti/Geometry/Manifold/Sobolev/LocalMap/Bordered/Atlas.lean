/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Atlas
public import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Bordered
import TauCeti.Analysis.Sobolev.Local.Examples
import TauCeti.Analysis.Sobolev.Local.HalfPlane
import TauCeti.Analysis.Sobolev.Local.Locality
import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.Double
import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# Chart calculus up to the boundary for local Sobolev maps of order at most one

Let `X` be a Riemann surface with boundary, charted on the closed upper half-plane with chart
changes in `TauCeti.borderedHolomorphicGroupoid`, and let `M` be a smooth manifold modelled on a
real Banach space. The local Sobolev class up to the boundary
`TauCeti.MemWkpLocMapOnBordered I p k u s` tests the coordinate expressions of `u : X → M` in all
charts of the maximal atlases, on relatively open subsets of the closed upper half-plane. For
`k ≤ 1`, open `s` and boundaryless `M` we show that it suffices to test the charts of any
subfamilies of the maximal atlases covering `s` and `u '' s`, and that on the interior of `X` the
class restricts to the class `TauCeti.MemWkpLocMapOn` of the Riemann surface
`TauCeti.borderedInterior X`. Order zero and composition with `C^ℓ` maps are treated for the
classes of any structure groupoid (`TauCeti.memWkpLocMapOnGroupoid_zero_iff`,
`TauCeti.MemWkpLocMapOnGroupoid.contMDiffOn_comp`), so they apply up to the boundary as well.

A change of bordered holomorphic chart `e` is smooth only up to the real axis. Its Schwarz
reflection `TauCeti.ClosedUpperHalfPlane.schwarzDouble e` is a holomorphic chart of `ℂ` that agrees
with `e` on the closed upper half-plane. So the change of holomorphic chart
`TauCeti.memWkpLoc_comp_chart_transition` along the reflection, which holds on arbitrary subsets
of the plane, applies on the relatively open test sets. Changing the chart of `M` is the chain rule
`TauCeti.memWkpLoc_extend_comp`, which also holds on arbitrary subsets of the plane.
The steps are glued with the locality of the planar classes, `memWkpLoc_iff_locally`.

## Main declarations

* `TauCeti.memWkpLocMapOnBordered_iff_of_subset_maximalAtlas`: **chart independence** up to the
  boundary, testing families of charts covering `s` and `u '' s`;
  `TauCeti.memWkpLocMapOnBordered_iff_atlas` and `TauCeti.memWkpLocMapOnBordered_iff_chartAt` for
  the atlases and the preferred charts, and the versions for `TauCeti.MemWkpLocMapBordered`.
* `TauCeti.MemWkpLocMapOnBordered.memWkpLocMapOn_preimage`: a local Sobolev map up to the
  boundary on `s` is a local Sobolev map of the interior on the part of `s` in the interior, the
  converse of `TauCeti.MemWkpLocMapOn.memWkpLocMapOnBordered_image`;
  `TauCeti.memWkpLocMapOnBordered_image_iff` combines the two, and
  `TauCeti.memWkpLocMapOnBordered_borderedInterior_iff` and
  `TauCeti.MemWkpLocMapBordered.memWkpLocMap` are the versions for the whole interior.
* `TauCeti.memWkpLocMapOnBordered_sqrt_im`: on the closed upper half-disc, `z ↦ √(Im z)` is in
  the class of order `1` for every `p < 2`, the companion of
  `TauCeti.not_memWkpLocMapOnBordered_sqrt_im`.

## Implementation notes

As in `TauCeti.Geometry.Manifold.Sobolev.LocalMap.Atlas`, chart independence assumes `M`
boundaryless, and orders `k ≥ 2` are not treated: they need the higher-order change of variables
for the half-disc classes. The restriction to the interior changes only the chart of the surface,
so it holds for targets with boundary or corners.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 and Section 2.4.
-/

public section

open Set Filter MeasureTheory TopologicalSpace
open scoped Manifold ContDiff Topology ComplexConjugate

noncomputable section

namespace TauCeti

open ClosedUpperHalfPlane

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ClosedUpperHalfPlane X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {p : ENNReal} {k : ℕ} {u : X → M} {s : Set X}

/-! ### Change of bordered holomorphic chart -/

/-- **Change of bordered holomorphic chart.** Precomposition with the transition map
`φ ∘ φ'⁻¹` between two bordered holomorphic charts preserves the planar classes of order at most
one on subsets of the overlap. The transition map is read through its Schwarz
reflection, a holomorphic chart of `ℂ` agreeing with it on the closed upper half-plane. -/
private theorem memWkpLoc_comp_bordered_transition
    {φ φ' : OpenPartialHomeomorph X ClosedUpperHalfPlane}
    (hφ : φ ∈ borderedHolomorphicGroupoid.maximalAtlas X)
    (hφ' : φ' ∈ borderedHolomorphicGroupoid.maximalAtlas X)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℂ → E} {V W : Set ℂ} (hk : k ≤ 1)
    (hg : MemWkpLoc p V k g)
    (hWφ : W ⊆ (φ'.extend closedUpperHalfPlaneModel).target ∩
      (φ'.extend closedUpperHalfPlaneModel).symm ⁻¹' φ.source)
    (hmaps : MapsTo (φ.extend closedUpperHalfPlaneModel ∘
      (φ'.extend closedUpperHalfPlaneModel).symm) W V) :
    MemWkpLoc p W k
      (g ∘ φ.extend closedUpperHalfPlaneModel ∘ (φ'.extend closedUpperHalfPlaneModel).symm) := by
  set e := φ'.symm ≫ₕ φ
  have he : e ∈ borderedHolomorphicGroupoid :=
    StructureGroupoid.compatible_of_mem_maximalAtlas hφ' hφ
  have hre : PreservesRealAxis e := preservesRealAxis_of_mem_borderedHolomorphicGroupoid he
  set Φ := schwarzDouble e hre
  have hΦ : Φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 ℂ :=
    (contDiffGroupoid 1 𝓘(ℂ)).mem_maximalAtlas_of_mem_groupoid
      (contDiffGroupoid_le (by exact_mod_cast le_top) (schwarzDouble_mem_contDiffGroupoid hre he))
  have hupper : ∀ z ∈ W, 0 ≤ z.im := fun z hz ↦ by
    simpa using φ'.extend_target_subset_range (hWφ hz).1
  -- On the closed upper half-plane the reflection is the transition map.
  have hagree : ∀ z ∈ W, Φ z =
      (φ.extend closedUpperHalfPlaneModel ∘ (φ'.extend closedUpperHalfPlaneModel).symm) z := by
    intro z hz
    rw [schwarzDouble_apply_of_im_nonneg hre (hupper z hz)]
    simp [e, closedUpperHalfPlaneModel_symm_eq_fold (hupper z hz)]
  have hsub : ∀ z ∈ W, z ∈ Φ.source := fun z hz ↦ by
    obtain ⟨hzt, hzφ⟩ := hWφ hz
    rw [OpenPartialHomeomorph.extend_target] at hzt
    simp only [mem_preimage, OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply] at hzφ
    simp only [Φ, e, schwarzDouble_source, mem_preimage, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, mem_inter_iff,
      ← closedUpperHalfPlaneModel_symm_eq_fold (hupper z hz)]
    exact ⟨hzt.1, hzφ⟩
  refine (memWkpLoc_comp_chart_transition hΦ (contDiffGroupoid 1 𝓘(ℂ)).id_mem_maximalAtlas hk hg
    (fun z hz ↦ ⟨mem_univ z, hsub z hz⟩) fun z hz ↦ ?_).congr fun z hz ↦ ?_
  · simpa only [Function.comp_apply, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply, id_eq, hagree z hz] using hmaps hz
  · simp only [Function.comp_apply, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply, id_eq]
    rw [hagree z hz, Function.comp_apply]

/-! ### Chart independence -/

section ChartIndependence

variable [I.Boundaryless] [CompleteSpace F]

/-- **Chart independence of the local Sobolev class up to the boundary.** For `k ≤ 1` and open
`s`, it suffices to test the coordinate expressions in the charts of a family `A` of bordered
holomorphic charts covering `s` and a family `B` of smooth charts of `M` covering `u '' s`. -/
theorem memWkpLocMapOnBordered_iff_of_subset_maximalAtlas (hk : k ≤ 1) (hs : IsOpen s)
    {A : Set (OpenPartialHomeomorph X ClosedUpperHalfPlane)}
    (hA : A ⊆ borderedHolomorphicGroupoid.maximalAtlas X) (hAs : ∀ x ∈ s, ∃ φ ∈ A, x ∈ φ.source)
    {B : Set (OpenPartialHomeomorph M H)} (hB : B ⊆ IsManifold.maximalAtlas I ∞ M)
    (hBs : ∀ x ∈ s, ∃ ψ ∈ B, u x ∈ ψ.source) :
    MemWkpLocMapOnBordered I p k u s ↔ ContinuousOn u s ∧ ∀ φ ∈ A, ∀ ψ ∈ B,
      MemWkpLoc p ((φ.extend closedUpperHalfPlaneModel).target ∩
        (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) k
        (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) := by
  refine ⟨fun hu ↦ ⟨hu.continuousOn, fun φ hφ ψ hψ ↦ hu.memWkpLoc_chart (hA hφ) (hB hψ)⟩,
    fun ⟨hc, h⟩ ↦ ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk with rfl | rfl
  · exact memWkpLocMapOnGroupoid_zero_iff.2 hc
  refine memWkpLocMapOnGroupoid_iff.2 ⟨hc, fun φ' hφ' ψ' hψ' ↦ ?_⟩
  -- Change the bordered holomorphic chart, for each chart of `B`.
  have h1 : ∀ ψ ∈ B, MemWkpLoc p ((φ'.extend closedUpperHalfPlaneModel).target ∩
      (φ'.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) 1
      (ψ.extend I ∘ u ∘ (φ'.extend closedUpperHalfPlaneModel).symm) := by
    intro ψ hψ
    refine memWkpLoc_iff_locally.2 fun z hz ↦ ?_
    obtain ⟨φ, hφA, hxφ⟩ := hAs _ hz.2.1
    refine ⟨_, inter_mem self_mem_nhdsWithin (nhdsWithin_mono _
      (inter_subset_left.trans φ'.extend_target_subset_range)
      (φ'.extend_target_inter_preimage_mem_nhdsWithin φ.open_source ⟨hz.1, hxφ⟩)),
      (memWkpLoc_comp_bordered_transition (hA hφA) hφ' le_rfl (h φ hφA ψ hψ)
        inter_subset_right fun w hw ↦ ?_).congr fun w hw ↦ ?_⟩
    · obtain ⟨⟨-, hws, hwψ⟩, -, hwφ⟩ := hw
      refine ⟨(φ.extend closedUpperHalfPlaneModel).map_source (by rwa [φ.extend_source]), ?_⟩
      rw [mem_preimage, Function.comp_apply, φ.extend_left_inv hwφ]
      exact ⟨hws, hwψ⟩
    · have hwφ : φ'.symm (closedUpperHalfPlaneModel.symm w) ∈ φ.source := hw.2.2
      simp [φ.left_inv hwφ]
  -- Change the chart of `M`.
  refine memWkpLoc_iff_locally.2 fun z hz ↦ ?_
  obtain ⟨ψ, hψB, hxψ⟩ := hBs _ hz.2.1
  have hO := hc.isOpen_inter_preimage hs ψ.open_source
  refine ⟨_, inter_mem self_mem_nhdsWithin (nhdsWithin_mono _
    (inter_subset_left.trans φ'.extend_target_subset_range)
    (φ'.extend_target_inter_preimage_mem_nhdsWithin hO ⟨hz.1, hz.2.1, hxψ⟩)), ?_⟩
  exact memWkpLoc_extend_comp (hB hψB) hψ' contMDiffOn_id isOpen_univ
    ((h1 ψ hψB).mono inter_subset_right) ((hc.extend_comp_extend_symm φ' ψ).mono inter_subset_right)
    fun w hw ↦ ⟨hw.2.2.2, mem_univ _, hw.1.2.2⟩

/-- **Chart independence up to the boundary on the whole surface.** For `k ≤ 1`, it suffices to
test the coordinate expressions in the charts of a family `A` of bordered holomorphic charts
covering `X` and a family `B` of smooth charts covering the image of `u`. -/
theorem memWkpLocMapBordered_iff_of_subset_maximalAtlas (hk : k ≤ 1)
    {A : Set (OpenPartialHomeomorph X ClosedUpperHalfPlane)}
    (hA : A ⊆ borderedHolomorphicGroupoid.maximalAtlas X) (hAs : ∀ x, ∃ φ ∈ A, x ∈ φ.source)
    {B : Set (OpenPartialHomeomorph M H)} (hB : B ⊆ IsManifold.maximalAtlas I ∞ M)
    (hBs : ∀ x, ∃ ψ ∈ B, u x ∈ ψ.source) :
    MemWkpLocMapBordered I p k u ↔ Continuous u ∧ ∀ φ ∈ A, ∀ ψ ∈ B,
      MemWkpLoc p ((φ.extend closedUpperHalfPlaneModel).target ∩
        (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (u ⁻¹' ψ.source)) k
        (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) := by
  have h : MemWkpLocMapOnBordered I p k u univ ↔ MemWkpLocMapBordered I p k u :=
    memWkpLocMapOnGroupoid_univ
  rw [← h, memWkpLocMapOnBordered_iff_of_subset_maximalAtlas hk isOpen_univ hA
    (fun x _ ↦ hAs x) hB (fun x _ ↦ hBs x)]
  simp only [continuousOn_univ, univ_inter]

variable [HasGroupoid X borderedHolomorphicGroupoid] [IsManifold I ∞ M]

/-- Chart independence up to the boundary: for `k ≤ 1` and open `s`, it suffices to test the
charts of the atlases of `X` and `M`. -/
theorem memWkpLocMapOnBordered_iff_atlas (hk : k ≤ 1) (hs : IsOpen s) :
    MemWkpLocMapOnBordered I p k u s ↔ ContinuousOn u s ∧
      ∀ φ ∈ atlas ClosedUpperHalfPlane X, ∀ ψ ∈ atlas H M,
        MemWkpLoc p ((φ.extend closedUpperHalfPlaneModel).target ∩
          (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) k
          (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) :=
  memWkpLocMapOnBordered_iff_of_subset_maximalAtlas hk hs
    borderedHolomorphicGroupoid.subset_maximalAtlas
    (fun x _ ↦ ⟨_, chart_mem_atlas _ x, mem_chart_source _ x⟩) IsManifold.subset_maximalAtlas
    fun x _ ↦ ⟨_, chart_mem_atlas H (u x), mem_chart_source H (u x)⟩

/-- Chart independence up to the boundary: for `k ≤ 1`, it suffices to test the charts of the
atlases of `X` and `M`. -/
theorem memWkpLocMapBordered_iff_atlas (hk : k ≤ 1) :
    MemWkpLocMapBordered I p k u ↔ Continuous u ∧
      ∀ φ ∈ atlas ClosedUpperHalfPlane X, ∀ ψ ∈ atlas H M,
        MemWkpLoc p ((φ.extend closedUpperHalfPlaneModel).target ∩
          (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (u ⁻¹' ψ.source)) k
          (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) :=
  memWkpLocMapBordered_iff_of_subset_maximalAtlas hk
    borderedHolomorphicGroupoid.subset_maximalAtlas
    (fun x ↦ ⟨_, chart_mem_atlas _ x, mem_chart_source _ x⟩) IsManifold.subset_maximalAtlas
    fun x ↦ ⟨_, chart_mem_atlas H (u x), mem_chart_source H (u x)⟩

/-- Chart independence up to the boundary: for `k ≤ 1` and open `s`, it suffices to test the
preferred charts of `X` and `M`. -/
theorem memWkpLocMapOnBordered_iff_chartAt (hk : k ≤ 1) (hs : IsOpen s) :
    MemWkpLocMapOnBordered I p k u s ↔ ContinuousOn u s ∧ ∀ x : X, ∀ y : M,
      MemWkpLoc p ((extChartAt closedUpperHalfPlaneModel x).target ∩
        (extChartAt closedUpperHalfPlaneModel x).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y).source)) k
        (extChartAt I y ∘ u ∘ (extChartAt closedUpperHalfPlaneModel x).symm) := by
  rw [memWkpLocMapOnBordered_iff_of_subset_maximalAtlas hk hs
    (A := range (chartAt ClosedUpperHalfPlane))
    (range_subset_iff.2 borderedHolomorphicGroupoid.chart_mem_maximalAtlas)
    (fun x _ ↦ ⟨_, mem_range_self x, mem_chart_source _ x⟩)
    (B := range (chartAt H)) (range_subset_iff.2 IsManifold.chart_mem_maximalAtlas)
    fun x _ ↦ ⟨_, mem_range_self (u x), mem_chart_source H (u x)⟩]
  simp only [forall_mem_range, extChartAt]

/-- Chart independence up to the boundary: for `k ≤ 1`, it suffices to test the preferred charts
of `X` and `M`. -/
theorem memWkpLocMapBordered_iff_chartAt (hk : k ≤ 1) :
    MemWkpLocMapBordered I p k u ↔ Continuous u ∧ ∀ x : X, ∀ y : M,
      MemWkpLoc p ((extChartAt closedUpperHalfPlaneModel x).target ∩
        (extChartAt closedUpperHalfPlaneModel x).symm ⁻¹' (u ⁻¹' (chartAt H y).source)) k
        (extChartAt I y ∘ u ∘ (extChartAt closedUpperHalfPlaneModel x).symm) := by
  have h : MemWkpLocMapOnBordered I p k u univ ↔ MemWkpLocMapBordered I p k u :=
    memWkpLocMapOnGroupoid_univ
  rw [← h, memWkpLocMapOnBordered_iff_chartAt hk isOpen_univ]
  simp only [continuousOn_univ, univ_inter]

end ChartIndependence

/-! ### Restriction to the interior -/

section Interior

variable [HasGroupoid X borderedHolomorphicGroupoid] [CompleteSpace F]

/-- On the interior, a local Sobolev map up to the boundary on a set `s` is a local Sobolev map of
the Riemann surface `borderedInterior X` on the part of `s` in the interior, with the same order
`k ≤ 1` and exponent. In the preferred charts the coordinate expressions of the interior
are those up to the boundary, restricted to the open upper half-plane; any other holomorphic chart
of the interior is reached by a change of holomorphic chart. -/
theorem MemWkpLocMapOnBordered.memWkpLocMapOn_preimage (hu : MemWkpLocMapOnBordered I p k u s)
    (hk : k ≤ 1) :
    MemWkpLocMapOn I p k (u ∘ (↑)) ((↑) ⁻¹' s : Set (borderedInterior X)) := by
  have hc : ContinuousOn (u ∘ (↑)) ((↑) ⁻¹' s : Set (borderedInterior X)) :=
    hu.continuousOn.comp continuous_subtype_val.continuousOn (mapsTo_preimage _ _)
  refine memWkpLocMapOn_iff.2 ⟨hc, fun φ hφ ψ hψ ↦ ?_⟩
  -- In the preferred charts of the interior, the coordinate tests are those up to the boundary.
  have hx : ∀ x : borderedInterior X, MemWkpLoc p ((chartAt ℂ x).target ∩
      (chartAt ℂ x).symm ⁻¹' ((↑) ⁻¹' s ∩ (u ∘ (↑)) ⁻¹' ψ.source)) k
      (ψ.extend I ∘ (u ∘ (↑)) ∘ (chartAt ℂ x).symm) := by
    intro x
    -- Every point of the test set of the interior lies in the test set up to the boundary, where
    -- the two coordinate expressions agree.
    have hmem : ∀ z ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹'
        ((↑) ⁻¹' s ∩ (u ∘ (↑)) ⁻¹' ψ.source),
        z ∈ ((chartAt ClosedUpperHalfPlane (x : X)).extend closedUpperHalfPlaneModel).target ∩
          ((chartAt ClosedUpperHalfPlane (x : X)).extend closedUpperHalfPlaneModel).symm ⁻¹'
            (s ∩ u ⁻¹' ψ.source) ∧
        (ψ.extend I ∘ (u ∘ (↑)) ∘ (chartAt ℂ x).symm) z =
          (ψ.extend I ∘ u ∘
            ((chartAt ClosedUpperHalfPlane (x : X)).extend closedUpperHalfPlaneModel).symm) z := by
      rintro z ⟨hzt, hzs, hzψ⟩
      have hsymm := chartAt_borderedInterior_symm_apply x hzt
      simp only [chartAt_borderedInterior_target, mem_inter_iff, mem_preimage, mem_ofPred_eq]
        at hzt
      rw [OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_target,
        range_closedUpperHalfPlaneModel]
      refine ⟨⟨⟨hzt.1, hzt.2.le⟩, ?_, ?_⟩, ?_⟩
      · rw [Function.comp_apply, ← hsymm]
        exact hzs
      · rw [mem_preimage, Function.comp_apply, ← hsymm]
        exact hzψ
      · simp only [Function.comp_apply, hsymm]
    exact ((hu.memWkpLoc_chart (borderedHolomorphicGroupoid.chart_mem_maximalAtlas (x : X))
      hψ).mono fun z hz ↦ (hmem z hz).1).congr fun z hz ↦ (hmem z hz).2
  -- Change from the preferred chart to `φ`.
  refine memWkpLoc_iff_locally.2 fun z hz ↦ ?_
  set x := φ.symm z
  have hN : IsOpen (φ.target ∩ φ.symm ⁻¹' (chartAt ℂ x).source) :=
    φ.isOpen_inter_preimage_symm (chartAt ℂ x).open_source
  refine ⟨_, inter_mem_nhdsWithin _ (hN.mem_nhds ⟨hz.1, mem_chart_source ℂ x⟩),
    (memWkpLoc_comp_chart_transition (IsManifold.chart_mem_maximalAtlas x) hφ hk (hx x)
      inter_subset_right fun w hw ↦ ?_).congr fun w hw ↦ ?_⟩
  · refine ⟨(chartAt ℂ x).map_source hw.2.2, ?_⟩
    rw [mem_preimage, Function.comp_apply, (chartAt ℂ x).left_inv hw.2.2]
    exact hw.1.2
  · simp only [Function.comp_apply, (chartAt ℂ x).left_inv hw.2.2]

/-- On an open subset `s` of the interior of a Riemann surface with boundary, a map is a local
Sobolev map up to the boundary on `s` exactly when it is a local Sobolev map of the Riemann
surface `borderedInterior X` on `s`, for every order `k ≤ 1` and exponent. -/
theorem memWkpLocMapOnBordered_image_iff {s : Set (borderedInterior X)} (hk : k ≤ 1)
    (hs : IsOpen s) :
    MemWkpLocMapOnBordered I p k u ((↑) '' s) ↔ MemWkpLocMapOn I p k (u ∘ (↑)) s := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.memWkpLocMapOnBordered_image hs⟩
  simpa [Subtype.val_injective.preimage_image] using
    h.memWkpLocMapOn_preimage hk

/-- A map is a local Sobolev map up to the boundary on the interior of a Riemann surface with
boundary exactly when it is a local Sobolev map of the Riemann surface `borderedInterior X`, for
every order `k ≤ 1` and exponent. -/
theorem memWkpLocMapOnBordered_borderedInterior_iff (hk : k ≤ 1) :
    MemWkpLocMapOnBordered I p k u (borderedInterior X) ↔
      MemWkpLocMap I p k (u ∘ ((↑) : borderedInterior X → X)) := by
  simpa using memWkpLocMapOnBordered_image_iff (I := I) (p := p) (u := u) hk
    (isOpen_univ : IsOpen (univ : Set (borderedInterior X)))

/-- A local Sobolev map up to the boundary of order `k ≤ 1` restricts to a local Sobolev map of
the Riemann surface `borderedInterior X`, with the same order and exponent. -/
theorem MemWkpLocMapBordered.memWkpLocMap (hu : MemWkpLocMapBordered I p k u) (hk : k ≤ 1) :
    MemWkpLocMap I p k (u ∘ ((↑) : borderedInterior X → X)) :=
  (memWkpLocMapOnBordered_borderedInterior_iff hk).1 hu.memWkpLocMapOnGroupoid

end Interior

/-! ### A square-root profile on the closed upper half-disc -/

/-- On the closed upper half-disc `{z | ‖z‖ < 1}` of `ClosedUpperHalfPlane`, the map
`z ↦ √(Im z)` is a local Sobolev map up to the boundary of order `1` for every exponent `p < 2`:
in the identity charts its coordinate expression is `z ↦ √(Im z)` on
`ball 0 1 ∩ {z | 0 ≤ z.im}`, whose derivative `(2 √(Im z))⁻¹` is `p`-integrable up to the real
axis exactly for `p < 2` (`TauCeti.memWkpLoc_sqrt_im_iff`). For `p ≥ 2` it is not in the class
(`TauCeti.not_memWkpLocMapOnBordered_sqrt_im`). -/
theorem memWkpLocMapOnBordered_sqrt_im (hp : p < 2) :
    MemWkpLocMapOnBordered 𝓘(ℝ) p 1 (fun z : ClosedUpperHalfPlane ↦ √(z : ℂ).im)
      {z | ‖(z : ℂ)‖ < 1} := by
  have hs : IsOpen {z : ClosedUpperHalfPlane | ‖(z : ℂ)‖ < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  rw [memWkpLocMapOnBordered_iff_chartAt le_rfl hs]
  refine ⟨by fun_prop, fun x y ↦ ?_⟩
  have hset : (extChartAt closedUpperHalfPlaneModel x).target ∩
      (extChartAt closedUpperHalfPlaneModel x).symm ⁻¹'
        ({z : ClosedUpperHalfPlane | ‖(z : ℂ)‖ < 1} ∩
          (fun z : ClosedUpperHalfPlane ↦ √(z : ℂ).im) ⁻¹' (chartAt ℝ y).source) =
      Metric.ball (0 : ℂ) 1 ∩ {z | 0 ≤ z.im} := by
    ext z
    simp only [chartAt_self_eq, extChartAt, OpenPartialHomeomorph.extend_target,
      OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.refl_target,
      OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_source,
      OpenPartialHomeomorph.refl_apply, range_closedUpperHalfPlaneModel, preimage_univ,
      inter_univ, mem_inter_iff, mem_preimage, mem_ofPred_eq, Function.comp_apply, id_eq,
      Metric.mem_ball, dist_zero_right, mem_univ, true_and]
    constructor
    · rintro ⟨hz, hzn⟩
      rw [coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz] at hzn
      exact ⟨hzn, hz⟩
    · rintro ⟨hzn, hz⟩
      rw [coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz]
      exact ⟨hz, hzn⟩
  rw [hset]
  refine (memWkpLoc_sqrt_im_iff.2 hp).congr fun z hz ↦ ?_
  simp [chartAt_self_eq, extChartAt, coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz.2]

end TauCeti
