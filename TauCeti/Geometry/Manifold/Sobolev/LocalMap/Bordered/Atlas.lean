/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Bordered
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Analysis.Calculus.TangentCone.Chart
import TauCeti.Analysis.Sobolev.Local.ChainRule
import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables
import TauCeti.Analysis.Sobolev.Local.Examples
import TauCeti.Analysis.Sobolev.Local.HalfPlane
import TauCeti.Analysis.Sobolev.Local.Locality
import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.Double
import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Atlas

/-!
# Chart calculus up to the boundary for local Sobolev maps of order at most one

Let `X` be a Riemann surface with boundary, charted on the closed upper half-plane with chart
changes in `TauCeti.borderedHolomorphicGroupoid`, and let `M` be a smooth manifold without
boundary modelled on a real Banach space. The local Sobolev class up to the boundary
`TauCeti.MemWkpLocMapOnBordered I p k u s` tests the coordinate expressions of `u : X → M` in all
charts of the maximal atlases, on relatively open subsets of the closed upper half-plane. For
`k ≤ 1` and open `s` we show that it suffices to test the charts of any subfamilies of the
maximal atlases covering `s` and `u '' s`, that composition with `C^ℓ` maps, `ℓ ≥ k`, preserves
the class, and that on the interior of `X` it restricts to the class
`TauCeti.MemWkpLocMapOn` of the Riemann surface `TauCeti.borderedInterior X`.

A change of bordered holomorphic chart `e` is smooth only up to the real axis. Its Schwarz
reflection `TauCeti.ClosedUpperHalfPlane.schwarzDouble e` is holomorphic, with holomorphic
inverse, on an open subset of `ℂ` containing the relevant part of the closed upper half-plane,
agrees with `e` there, and sends real points to real points and the upper half-plane to the upper
half-plane. So the change of variables `MemWkpLoc.comp_contDiffOn_diffeo_halfPlane` for the
half-disc classes applies to it. Changing the chart of `M`, or composing with a `C^ℓ` map, is the
chain rule `MemWkpLoc.contDiffOn_comp`, which holds on arbitrary subsets of the plane. The steps
are glued with the locality of the planar classes, `memWkpLoc_iff_locally`.

## Main declarations

* `TauCeti.memWkpLocMapOnBordered_zero_iff`, `TauCeti.memWkpLocMapBordered_zero_iff`: at order
  zero the class is that of continuous maps.
* `TauCeti.memWkpLocMapOnBordered_iff_of_subset_maximalAtlas`: **chart independence** up to the
  boundary, testing families of charts covering `s` and `u '' s`;
  `TauCeti.memWkpLocMapOnBordered_iff_atlas` and `TauCeti.memWkpLocMapOnBordered_iff_chartAt` for
  the atlases and the preferred charts, and the versions for `TauCeti.MemWkpLocMapBordered`.
* `TauCeti.MemWkpLocMapOnBordered.contMDiffOn_comp`, `ContMDiff.comp_memWkpLocMapBordered`:
  composition with `C^ℓ` maps into any manifold modelled on a real Banach space.
* `TauCeti.MemWkpLocMapOnBordered.memWkpLocMapOn_preimage`: a local Sobolev map up to the
  boundary on `s` is a local Sobolev map of the interior on the part of `s` in the interior, the
  converse of `TauCeti.MemWkpLocMapOn.memWkpLocMapOnBordered_image`;
  `TauCeti.memWkpLocMapOnBordered_image_iff` combines the two.
* `TauCeti.memWkpLocMapOnBordered_sqrt_im`: on the closed upper half-disc, `z ↦ √(Im z)` is in
  the class of order `1` for every `p < 2`, the companion of
  `TauCeti.not_memWkpLocMapOnBordered_sqrt_im`.

## Implementation notes

As in `TauCeti.Geometry.Manifold.Sobolev.LocalMap.Atlas`, the target `M` is assumed boundaryless,
and orders `k ≥ 2` are not treated: they need the higher-order change of variables for the
half-disc classes.

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
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ F' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {p : ENNReal} {k : ℕ} {u : X → M} {s : Set X}

/-! ### Auxiliary facts on coordinate expressions -/

omit [ChartedSpace ClosedUpperHalfPlane X] [ChartedSpace H M] in
/-- The coordinate expression of a map continuous on `s` is continuous on its domain. -/
private theorem continuousOn_chart (hu : ContinuousOn u s)
    (φ : OpenPartialHomeomorph X ClosedUpperHalfPlane) (ψ : OpenPartialHomeomorph M H) :
    ContinuousOn (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm)
      ((φ.extend closedUpperHalfPlaneModel).target ∩
        (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) := by
  refine ψ.continuousOn_extend.comp (hu.comp (φ.continuousOn_extend_symm.mono inter_subset_left)
    fun _ hz ↦ hz.2.1) fun _ hz ↦ ?_
  simpa using hz.2.2

omit [ChartedSpace ClosedUpperHalfPlane X] [ChartedSpace H M] in
/-- The domain of a coordinate expression of a map continuous on an open set is relatively open
in the closed upper half-plane. -/
private theorem exists_isOpen_chart (hu : ContinuousOn u s) (hs : IsOpen s)
    (φ : OpenPartialHomeomorph X ClosedUpperHalfPlane) (ψ : OpenPartialHomeomorph M H) :
    ∃ Ω : Set ℂ, IsOpen Ω ∧ (φ.extend closedUpperHalfPlaneModel).target ∩
      (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source) =
        Ω ∩ {z | 0 ≤ z.im} :=
  φ.exists_isOpen_extend_target_inter_preimage (hu.isOpen_inter_preimage hs ψ.open_source)

omit [ChartedSpace ClosedUpperHalfPlane X] [ChartedSpace H M] in
/-- The domain of a coordinate expression of a map continuous on an open set is measurable. -/
private theorem measurableSet_chart (hu : ContinuousOn u s) (hs : IsOpen s)
    (φ : OpenPartialHomeomorph X ClosedUpperHalfPlane) (ψ : OpenPartialHomeomorph M H) :
    MeasurableSet ((φ.extend closedUpperHalfPlaneModel).target ∩
      (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) := by
  obtain ⟨Ω, hΩ, hT⟩ := exists_isOpen_chart hu hs φ ψ
  rw [hT]
  exact hΩ.measurableSet_inter_setOf_im_nonneg

omit [ChartedSpace ClosedUpperHalfPlane X] [ChartedSpace H M] in
/-- The domain of a coordinate expression of a map continuous on an open set is a neighbourhood
of each of its points within the closed upper half-plane. -/
private theorem chart_mem_nhdsWithin (hu : ContinuousOn u s) (hs : IsOpen s)
    (φ : OpenPartialHomeomorph X ClosedUpperHalfPlane) (ψ : OpenPartialHomeomorph M H)
    {S : Set ℂ} (hS : S ⊆ {z | 0 ≤ z.im}) {z : ℂ}
    (hz : z ∈ (φ.extend closedUpperHalfPlaneModel).target ∩
      (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :
    (φ.extend closedUpperHalfPlaneModel).target ∩
      (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source) ∈ 𝓝[S] z := by
  obtain ⟨Ω, hΩ, hT⟩ := exists_isOpen_chart hu hs φ ψ
  rw [hT] at hz ⊢
  exact mem_nhdsWithin.2 ⟨Ω, hΩ, hz.1, fun w hw ↦ ⟨hw.1, hS hw.2⟩⟩

omit [ChartedSpace ClosedUpperHalfPlane X] in
/-- The extended target of a chart into the closed upper half-plane lies in `{z | 0 ≤ z.im}`. -/
private theorem extend_target_subset (φ : OpenPartialHomeomorph X ClosedUpperHalfPlane) :
    (φ.extend closedUpperHalfPlaneModel).target ⊆ {z | 0 ≤ z.im} := fun _ hz ↦ by
  simpa using φ.extend_target_subset_range hz

/-- **Change of bordered holomorphic chart.** Precomposition with the transition map
`φ ∘ φ'⁻¹` between two bordered holomorphic charts preserves the half-disc classes of order at
most one. The transition map is read through its Schwarz reflection, which is holomorphic on an
open set containing `U ∩ {z | 0 ≤ z.im}`. -/
private theorem memWkpLoc_comp_bordered_transition
    {φ φ' : OpenPartialHomeomorph X ClosedUpperHalfPlane}
    (hφ : φ ∈ borderedHolomorphicGroupoid.maximalAtlas X)
    (hφ' : φ' ∈ borderedHolomorphicGroupoid.maximalAtlas X)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℂ → E} {Ω U : Set ℂ} (hk : k ≤ 1)
    (hg : MemWkpLoc p (Ω ∩ {z | 0 ≤ z.im}) k g) (hU : IsOpen U)
    (hUφ : U ∩ {z | 0 ≤ z.im} ⊆ (φ'.extend closedUpperHalfPlaneModel).target ∩
      (φ'.extend closedUpperHalfPlaneModel).symm ⁻¹' φ.source)
    (hmaps : MapsTo (φ.extend closedUpperHalfPlaneModel ∘
      (φ'.extend closedUpperHalfPlaneModel).symm) (U ∩ {z | 0 ≤ z.im}) Ω) :
    MemWkpLoc p (U ∩ {z | 0 ≤ z.im}) k
      (g ∘ φ.extend closedUpperHalfPlaneModel ∘ (φ'.extend closedUpperHalfPlaneModel).symm) := by
  set e := φ'.symm ≫ₕ φ
  have he : e ∈ borderedHolomorphicGroupoid :=
    StructureGroupoid.compatible_of_mem_maximalAtlas hφ' hφ
  have hre : PreservesRealAxis e := preservesRealAxis_of_mem_borderedHolomorphicGroupoid he
  set Φ := schwarzDouble e hre
  have hΦd : DifferentiableOn ℂ Φ Φ.source := differentiableOn_schwarzDouble hre he
  have hΦsd : DifferentiableOn ℂ Φ.symm Φ.target := by
    have h := differentiableOn_schwarzDouble hre.symm (borderedHolomorphicGroupoid.symm he)
    rw [← schwarzDouble_symm] at h
    exact h
  -- On the closed upper half-plane the reflection is the transition map.
  have hagree : ∀ z : ℂ, 0 ≤ z.im → Φ z =
      (φ.extend closedUpperHalfPlaneModel ∘ (φ'.extend closedUpperHalfPlaneModel).symm) z := by
    intro z hz
    rw [schwarzDouble_apply_of_im_nonneg hre hz]
    simp [e, closedUpperHalfPlaneModel_symm_eq_fold hz]
  have hsub : U ∩ {z | 0 ≤ z.im} ⊆ Φ.source := fun z hz ↦ by
    obtain ⟨hzt, hzφ⟩ := hUφ hz
    rw [OpenPartialHomeomorph.extend_target] at hzt
    simp only [mem_preimage, OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply] at hzφ
    simp only [Φ, e, schwarzDouble_source, mem_preimage, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, mem_inter_iff,
      ← closedUpperHalfPlaneModel_symm_eq_fold hz.2]
    exact ⟨hzt.1, hzφ⟩
  set U' := U ∩ Φ.source
  have hU' : IsOpen U' := hU.inter Φ.open_source
  have hU'eq : U' ∩ {z | 0 ≤ z.im} = U ∩ {z | 0 ≤ z.im} := by
    ext z
    exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, hsub h⟩, h.2⟩⟩
  have hcd : ContDiffOn ℝ 1 Φ U' :=
    ((hΦd.contDiffOn (n := 1) Φ.open_source).restrict_scalars ℝ).mono inter_subset_right
  have hdet : ∀ z ∈ U' ∩ {z | 0 ≤ z.im}, (fderiv ℝ Φ z).det ≠ 0 := fun z hz ↦ by
    have hzs : z ∈ Φ.source := hz.1.2
    obtain ⟨A, hA⟩ := Φ.exists_hasFDerivAt_of_chart hzs
      ((hΦd.differentiableAt (Φ.open_source.mem_nhds hzs)).restrictScalars ℝ)
      ((hΦsd.differentiableAt (Φ.open_target.mem_nhds (Φ.map_source hzs))).restrictScalars ℝ)
    rw [hA.fderiv]
    exact A.toLinearEquiv.isUnit_det'.ne_zero
  have hmaps' : MapsTo Φ (U' ∩ {z | 0 ≤ z.im}) Ω := fun z hz ↦ by
    rw [hagree z hz.2]
    exact hmaps (hU'eq ▸ hz)
  have hreal : ∀ z ∈ U', z.im = 0 → (Φ z).im = 0 := fun z hz h0 ↦ by
    have h := schwarzDouble_conj hre hz.2
    rw [Complex.conj_eq_iff_im.2 h0] at h
    exact Complex.conj_eq_iff_im.1 h.symm
  have hupper : ∀ z ∈ U', 0 < z.im → 0 ≤ (Φ z).im := fun z _ hz ↦ by
    rw [schwarzDouble_apply_of_im_nonneg hre hz.le]
    exact (e (fold z)).property
  have h := hg.comp_contDiffOn_diffeo_halfPlane hk hU' hcd (Φ.injOn.mono fun z hz ↦ hz.1.2) hdet
    hmaps' hreal hupper
  rw [hU'eq] at h
  refine h.congr_fun (fun z hz ↦ ?_) hU.measurableSet_inter_setOf_im_nonneg
  simp only [Function.comp_apply]
  rw [hagree z hz.2, Function.comp_apply]

/-- **Change of target chart through a `C¹` map.** If `ψ ∘ v` is a continuous `W^{1,p}_loc` map
on a measurable set `W` with `v` mapping `W` into the source of `ψ`, and `f` is `C¹` on an open
set containing `v '' W`, then `ψ' ∘ f ∘ v` is in `W^{1,p}_loc(W)` for every chart `ψ'` of the
target whose source contains `f '' (v '' W)`. -/
private theorem memWkpLoc_extend_comp_of_measurableSet [I.Boundaryless] [CompleteSpace F']
    {ψ : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M)
    {ψ' : OpenPartialHomeomorph N H'} (hψ' : ψ' ∈ IsManifold.maximalAtlas I' ∞ N)
    {f : M → N} {t : Set M} (hf : ContMDiffOn I I' 1 f t) (ht : IsOpen t)
    {v : ℂ → M} {W : Set ℂ} (hW : MeasurableSet W) (hv : MemWkpLoc p W 1 (ψ.extend I ∘ v))
    (hvc : ContinuousOn (ψ.extend I ∘ v) W)
    (hmaps : MapsTo v W (ψ.source ∩ (t ∩ f ⁻¹' ψ'.source))) :
    MemWkpLoc p W 1 (ψ'.extend I' ∘ f ∘ v) := by
  have hO : IsOpen ((ψ.extend I).target ∩ (ψ.extend I).symm ⁻¹' (t ∩ f ⁻¹' ψ'.source)) :=
    ψ.continuousOn_extend_symm.isOpen_inter_preimage ψ.isOpen_extend_target
      (hf.continuousOn.isOpen_inter_preimage ht ψ'.open_source)
  have hsymm : ContMDiffOn 𝓘(ℝ, F) I 1 (ψ.extend I).symm (ψ.extend I).target := by
    rw [ψ.extend_target']
    exact (contMDiffOn_extend_symm hψ).of_le (by exact_mod_cast le_top)
  have hh : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F') 1 (ψ'.extend I' ∘ f ∘ (ψ.extend I).symm)
      ((ψ.extend I).target ∩ (ψ.extend I).symm ⁻¹' (t ∩ f ⁻¹' ψ'.source)) :=
    ((ψ'.contMDiffOn_extend hψ').of_le (by exact_mod_cast le_top)).comp
      (hf.comp (hsymm.mono inter_subset_left) fun _ hy ↦ hy.2.1) fun _ hy ↦ hy.2.2
  have hmaps' : MapsTo (ψ.extend I ∘ v) W
      ((ψ.extend I).target ∩ (ψ.extend I).symm ⁻¹' (t ∩ f ⁻¹' ψ'.source)) := fun w hw ↦ by
    have hvw := hmaps hw
    refine ⟨(ψ.extend I).map_source (by simpa using hvw.1), ?_⟩
    simpa [ψ.left_inv hvw.1] using hvw.2
  refine (hv.contDiffOn_comp hvc hO (contMDiffOn_iff_contDiffOn.1 hh) hmaps').congr_fun
    (fun w hw ↦ ?_) hW
  simp [ψ.left_inv (hmaps hw).1]

/-! ### Order zero -/

/-- At order zero, the local Sobolev maps up to the boundary on `s` are the maps continuous on
`s`. -/
@[simp]
theorem memWkpLocMapOnBordered_zero_iff : MemWkpLocMapOnBordered I p 0 u s ↔ ContinuousOn u s :=
  ⟨MemWkpLocMapOnGroupoid.continuousOn, fun hu ↦ memWkpLocMapOnGroupoid_iff.2
    ⟨hu, fun φ _ ψ _ ↦ memWkpLoc_zero_iff.2 (continuousOn_chart hu φ ψ).memLpLoc⟩⟩

/-- At order zero, the local Sobolev maps up to the boundary are the continuous maps. -/
@[simp]
theorem memWkpLocMapBordered_zero_iff : MemWkpLocMapBordered I p 0 u ↔ Continuous u := by
  have h : MemWkpLocMapOnBordered I p 0 u univ ↔ MemWkpLocMapBordered I p 0 u :=
    memWkpLocMapOnGroupoid_univ
  rw [← h, memWkpLocMapOnBordered_zero_iff, continuousOn_univ]

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
  · exact memWkpLocMapOnBordered_zero_iff.2 hc
  refine memWkpLocMapOnGroupoid_iff.2 ⟨hc, fun φ' hφ' ψ' hψ' ↦ ?_⟩
  -- Change the bordered holomorphic chart, for each chart of `B`.
  have h1 : ∀ ψ ∈ B, MemWkpLoc p ((φ'.extend closedUpperHalfPlaneModel).target ∩
      (φ'.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) 1
      (ψ.extend I ∘ u ∘ (φ'.extend closedUpperHalfPlaneModel).symm) := by
    intro ψ hψ
    obtain ⟨Ω', hΩ', hT'⟩ := exists_isOpen_chart hc hs φ' ψ
    refine memWkpLoc_iff_locally.2 fun z hz ↦ ?_
    obtain ⟨φ, hφA, hxφ⟩ := hAs _ hz.2.1
    obtain ⟨O, hO, hOeq⟩ := φ'.exists_isOpen_extend_target_inter_preimage φ.open_source
    obtain ⟨Ω, hΩ, hT⟩ := exists_isOpen_chart hc hs φ ψ
    have hzO : z ∈ O ∩ {z | 0 ≤ z.im} := hOeq ▸ ⟨hz.1, hxφ⟩
    rw [hT'] at hz ⊢
    refine ⟨(Ω' ∩ O) ∩ {z | 0 ≤ z.im}, mem_nhdsWithin.2 ⟨O, hO, hzO.1,
      fun w hw ↦ ⟨⟨hw.2.1, hw.1⟩, hw.2.2⟩⟩, ?_⟩
    have hsub : (Ω' ∩ O) ∩ {z | 0 ≤ z.im} ⊆ ((φ'.extend closedUpperHalfPlaneModel).target ∩
        (φ'.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) ∩
        ((φ'.extend closedUpperHalfPlaneModel).target ∩
          (φ'.extend closedUpperHalfPlaneModel).symm ⁻¹' φ.source) := fun w hw ↦
      ⟨hT' ▸ ⟨hw.1.1, hw.2⟩, hOeq ▸ ⟨hw.1.2, hw.2⟩⟩
    have hg := h φ hφA ψ hψ
    rw [hT] at hg
    refine (memWkpLoc_comp_bordered_transition (hA hφA) hφ' le_rfl hg (hΩ'.inter hO)
      (fun w hw ↦ (hsub hw).2) fun w hw ↦ ?_).congr_fun (fun w hw ↦ ?_)
        (hΩ'.inter hO).measurableSet_inter_setOf_im_nonneg
    · obtain ⟨⟨-, hws, hwψ⟩, -, hwφ⟩ := hsub hw
      have hmem : (φ.extend closedUpperHalfPlaneModel ∘
          (φ'.extend closedUpperHalfPlaneModel).symm) w ∈
          (φ.extend closedUpperHalfPlaneModel).target ∩
            (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source) := by
        refine ⟨(φ.extend closedUpperHalfPlaneModel).map_source (by rwa [φ.extend_source]), ?_⟩
        rw [mem_preimage, Function.comp_apply, φ.extend_left_inv hwφ]
        exact ⟨hws, hwψ⟩
      rw [hT] at hmem
      exact hmem.1
    · have hwφ : φ'.symm (closedUpperHalfPlaneModel.symm w) ∈ φ.source := (hsub hw).2.2
      simp [φ.left_inv hwφ]
  -- Change the chart of `M`.
  refine memWkpLoc_iff_locally.2 fun z hz ↦ ?_
  obtain ⟨ψ, hψB, hxψ⟩ := hBs _ hz.2.1
  refine ⟨_, inter_mem self_mem_nhdsWithin (chart_mem_nhdsWithin hc hs φ' ψ
    ((inter_subset_left).trans (extend_target_subset φ')) ⟨hz.1, hz.2.1, hxψ⟩), ?_⟩
  exact memWkpLoc_extend_comp_of_measurableSet (hB hψB) hψ' contMDiffOn_id isOpen_univ
    ((measurableSet_chart hc hs φ' ψ').inter (measurableSet_chart hc hs φ' ψ))
    ((h1 ψ hψB).mono inter_subset_right) ((continuousOn_chart hc φ' ψ).mono inter_subset_right)
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

/-! ### Composition with differentiable maps -/

section Composition

variable [IsManifold I ∞ M] [I.Boundaryless] [CompleteSpace F']

/-- **Composition with `C^ℓ` maps up to the boundary.** If `u` is a local Sobolev map up to the
boundary of order `k ≤ 1` on an open set `s`, mapping `s` into an open set `t` on which
`f : M → N` is `C^ℓ` with `k ≤ ℓ`, then `f ∘ u` is a local Sobolev map up to the boundary of
order `k` on `s`. The manifold `N` may have corners. -/
theorem MemWkpLocMapOnBordered.contMDiffOn_comp {n : ℕ∞ω} {f : M → N} {t : Set M}
    (hu : MemWkpLocMapOnBordered I p k u s) (hk : k ≤ 1) (hf : ContMDiffOn I I' n f t)
    (hkn : (k : ℕ∞ω) ≤ n) (hs : IsOpen s) (ht : IsOpen t) (hst : MapsTo u s t) :
    MemWkpLocMapOnBordered I' p k (f ∘ u) s := by
  have hc : ContinuousOn (f ∘ u) s := hf.continuousOn.comp hu.continuousOn hst
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk with rfl | rfl
  · exact memWkpLocMapOnBordered_zero_iff.2 hc
  refine memWkpLocMapOnGroupoid_iff.2 ⟨hc, fun φ hφ ψ' hψ' ↦ memWkpLoc_iff_locally.2 fun z hz ↦ ?_⟩
  set ψ := chartAt H (u ((φ.extend closedUpperHalfPlaneModel).symm z))
  refine ⟨_, inter_mem self_mem_nhdsWithin (chart_mem_nhdsWithin hu.continuousOn hs φ ψ
    ((inter_subset_left).trans (extend_target_subset φ)) ⟨hz.1, hz.2.1, mem_chart_source _ _⟩),
    ?_⟩
  exact memWkpLoc_extend_comp_of_measurableSet (IsManifold.chart_mem_maximalAtlas _) hψ'
    (hf.of_le hkn) ht
    ((measurableSet_chart hc hs φ ψ').inter (measurableSet_chart hu.continuousOn hs φ ψ))
    ((hu.memWkpLoc_chart hφ (IsManifold.chart_mem_maximalAtlas _)).mono inter_subset_right)
    ((continuousOn_chart hu.continuousOn φ ψ).mono inter_subset_right)
    fun w hw ↦ ⟨hw.2.2.2, hst hw.2.2.1, hw.1.2.2⟩

/-- **Composition with `C^ℓ` maps up to the boundary.** If `u` is a local Sobolev map up to the
boundary of order `k ≤ 1` and `f : M → N` is `C^ℓ` with `k ≤ ℓ`, then `f ∘ u` is a local Sobolev
map up to the boundary of order `k`. -/
theorem _root_.ContMDiff.comp_memWkpLocMapBordered {n : ℕ∞ω} {f : M → N}
    (hf : ContMDiff I I' n f) (hu : MemWkpLocMapBordered I p k u) (hk : k ≤ 1)
    (hkn : (k : ℕ∞ω) ≤ n) : MemWkpLocMapBordered I' p k (f ∘ u) :=
  memWkpLocMapOnGroupoid_univ.mp (MemWkpLocMapOnBordered.contMDiffOn_comp
    (memWkpLocMapOnGroupoid_univ.mpr hu) hk hf.contMDiffOn hkn
    isOpen_univ isOpen_univ (mapsTo_univ _ _))

end Composition

/-! ### Restriction to the interior -/

section Interior

variable [HasGroupoid X borderedHolomorphicGroupoid] [IsManifold I ∞ M] [I.Boundaryless]
  [CompleteSpace F]

/-- On the interior, a local Sobolev map up to the boundary on an open set `s` is a local Sobolev
map of the Riemann surface `borderedInterior X` on the part of `s` in the interior, with the same
order `k ≤ 1` and exponent. In the preferred charts the coordinate expressions of the interior
are those up to the boundary, restricted to the open upper half-plane. -/
theorem MemWkpLocMapOnBordered.memWkpLocMapOn_preimage (hu : MemWkpLocMapOnBordered I p k u s)
    (hk : k ≤ 1) (hs : IsOpen s) :
    MemWkpLocMapOn I p k (u ∘ (↑)) ((↑) ⁻¹' s : Set (borderedInterior X)) := by
  have hs' : IsOpen ((↑) ⁻¹' s : Set (borderedInterior X)) := hs.preimage continuous_subtype_val
  rw [memWkpLocMapOn_iff_chartAt hk hs']
  refine ⟨hu.continuousOn.comp continuous_subtype_val.continuousOn (mapsTo_preimage _ _),
    fun x y ↦ ?_⟩
  have h := hu.memWkpLoc_chart (borderedHolomorphicGroupoid.chart_mem_maximalAtlas (x : X))
    (IsManifold.chart_mem_maximalAtlas y)
  -- Every point of the test set of the interior lies in the test set up to the boundary, where
  -- the two coordinate expressions agree.
  have hmem : ∀ z ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹'
      ((↑) ⁻¹' s ∩ (u ∘ (↑)) ⁻¹' (chartAt H y).source),
      z ∈ ((chartAt ClosedUpperHalfPlane (x : X)).extend closedUpperHalfPlaneModel).target ∩
        ((chartAt ClosedUpperHalfPlane (x : X)).extend closedUpperHalfPlaneModel).symm ⁻¹'
          (s ∩ u ⁻¹' (chartAt H y).source) ∧
      (extChartAt I y ∘ (u ∘ (↑)) ∘ (chartAt ℂ x).symm) z =
        ((chartAt H y).extend I ∘ u ∘
          ((chartAt ClosedUpperHalfPlane (x : X)).extend closedUpperHalfPlaneModel).symm) z := by
    rintro z ⟨hzt, hzs, hzψ⟩
    have hsymm := chartAt_borderedInterior_symm_apply x hzt
    rw [chartAt_borderedInterior_target] at hzt
    rw [OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_target,
      range_closedUpperHalfPlaneModel]
    refine ⟨⟨⟨hzt.1, (show (0 : ℝ) < z.im from hzt.2).le⟩, ?_, ?_⟩, ?_⟩
    · rw [Function.comp_apply, ← hsymm]
      exact hzs
    · rw [mem_preimage, Function.comp_apply, ← hsymm]
      exact hzψ
    · simp only [Function.comp_apply, hsymm, extChartAt]
  refine (h.mono fun z hz ↦ (hmem z hz).1).congr_fun (fun z hz ↦ (hmem z hz).2.symm)
    ((chartAt ℂ x).isOpen_inter_preimage_symm
      ((hu.continuousOn.comp continuous_subtype_val.continuousOn
        (mapsTo_preimage _ _)).isOpen_inter_preimage hs' (chartAt H y).open_source)).measurableSet

/-- On an open subset `s` of the interior of a Riemann surface with boundary, a map is a local
Sobolev map up to the boundary on `s` exactly when it is a local Sobolev map of the Riemann
surface `borderedInterior X` on `s`, for every order `k ≤ 1` and exponent. -/
theorem memWkpLocMapOnBordered_image_iff {s : Set (borderedInterior X)} (hk : k ≤ 1)
    (hs : IsOpen s) :
    MemWkpLocMapOnBordered I p k u ((↑) '' s) ↔ MemWkpLocMapOn I p k (u ∘ (↑)) s := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.memWkpLocMapOnBordered_image hs⟩
  simpa [Subtype.val_injective.preimage_image] using
    h.memWkpLocMapOn_preimage hk ((borderedInterior X).isOpen.isOpenMap_subtype_val s hs)

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
  refine (memWkpLoc_sqrt_im_iff.2 hp).congr_fun (fun z hz ↦ ?_)
    Metric.isOpen_ball.measurableSet_inter_setOf_im_nonneg
  simp [chartAt_self_eq, extChartAt, coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz.2]

end TauCeti
