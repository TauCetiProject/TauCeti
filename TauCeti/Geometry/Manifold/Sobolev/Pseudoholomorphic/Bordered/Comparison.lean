/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sobolev.Pseudoholomorphic.Bordered
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
import TauCeti.Analysis.Complex.ReImTopology
import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart

/-!
# Weak pseudoholomorphic maps up to the boundary of class `C¹` are pseudoholomorphic

Let `X` be a Riemann surface with boundary, with its almost complex structure
`j = TauCeti.SmoothAlmostComplexStructure.ofBorderedHolomorphic X`, and `J₀` a smooth almost
complex structure on a manifold `M` modelled on a boundaryless model. For the zero inhomogeneous
term and a map `u` of class `C¹` on an open set `s ⊆ X`, the weak pseudoholomorphic equation up to
the boundary (`TauCeti.IsWeakPseudoholomorphicOnBordered`) for `J₀`, regarded as a family
independent of the domain point, is pseudoholomorphy of `u` on `s`
(`TauCeti.isWeakPseudoholomorphicOnBordered_iff_isPseudoholomorphicOn`). This is the bordered
form of `TauCeti.isWeakPseudoholomorphicOn_iff_isPseudoholomorphicOn`.

The weak equation is tested in the extended bordered holomorphic charts `φ` of `X`, on a set
`U ⊆ ℂ` that is relatively open in the closed upper half-plane, and only on the interior of `U`.
There a `C¹` weak solution solves the equation pointwise. At a boundary point of `X`, the
derivative of `u` read in the chart at that point is the derivative within the closed upper
half-plane, which is continuous on `U`: the pointwise equation passes from the points of
positive imaginary part to the real axis, and
`TauCeti.ContMDiffAlmostComplexStructure.fderivWithin_chart_comp_add_eq_zero_iff` turns it into
the equation `du ∘ j = J₀ ∘ du`. Conversely, at a point of positive imaginary part the inverse of
a bordered holomorphic chart has complex linear derivative, so pseudoholomorphy of `u` gives the
pointwise equation in every chart.

## Main results

* `TauCeti.isWeakPseudoholomorphicOnBordered_iff_isPseudoholomorphicOn`,
  `TauCeti.isWeakPseudoholomorphicBordered_iff_isPseudoholomorphic`: **comparison with
  pseudoholomorphic maps** for `ν = 0`, `J₀` independent of the domain point and `u` of class
  `C¹`, for every exponent.
* `TauCeti.not_isPseudoholomorphicOn_conj`: conjugation, from the closed upper half-plane to `ℂ`,
  is not pseudoholomorphic on any nonempty open set, read off from
  `TauCeti.not_isWeakPseudoholomorphicOnBordered_conj`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Sections 2.2 and 3.1 and Appendix B.4.
-/

public section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology ComplexConjugate

noncomputable section

namespace TauCeti

open ClosedUpperHalfPlane

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ClosedUpperHalfPlane X]
  [HasGroupoid X borderedHolomorphicGroupoid]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {ℓ : ℕ∞}
  {p : ENNReal} {u : X → M} {s : Set X}

omit [HasGroupoid X borderedHolomorphicGroupoid] [IsManifold I ∞ M] in
/-- A map of class `C¹` on `s`, read in a bordered holomorphic chart `φ` of `X` and a chart `ψ` of
`M`, is of class `C¹` on the part of the extended target of `φ` over `s` where `u` maps into the
source of `ψ`. -/
private theorem contDiffOn_chart (hu : ContMDiffOn closedUpperHalfPlaneModel I 1 u s)
    {φ : OpenPartialHomeomorph X ClosedUpperHalfPlane}
    (hφ : φ ∈ borderedHolomorphicGroupoid.maximalAtlas X)
    {ψ : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    ContDiffOn ℝ 1
      (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm)
      ((φ.extend closedUpperHalfPlaneModel).target ∩
        (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) := by
  rw [ψ.coe_extendTrans_refl I]
  exact φ.contDiffOn_extend_comp
    (borderedHolomorphicGroupoid_maximalAtlas_subset (n := 1) (by exact_mod_cast le_top) hφ)
    (IsManifold.maximalAtlas_subset_of_le (by exact_mod_cast le_top) hψ) hu

/-- **The equation reaches the real axis.** Let `f` be of class `C¹` and `A` continuous on the part
of an open set `O ⊆ ℂ` in the closed upper half-plane. If `∂ₛf + A ∂ₜf = 0` at the points of `O`
of positive imaginary part, then it holds at every point of `O` in the closed upper half-plane for
the derivatives within the closed upper half-plane, which are continuous there. -/
private theorem fderivWithin_add_eq_zero_of_im_pos {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℂ → F} {A : ℂ → F →L[ℝ] F} {O : Set ℂ} (hO : IsOpen O)
    (hf : ContDiffOn ℝ 1 f (O ∩ range closedUpperHalfPlaneModel))
    (hA : ContinuousOn A (O ∩ range closedUpperHalfPlaneModel))
    (h : ∀ z ∈ O ∩ {z : ℂ | 0 < z.im}, fderiv ℝ f z 1 + A z (fderiv ℝ f z Complex.I) = 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ O ∩ range closedUpperHalfPlaneModel) :
    fderivWithin ℝ f (range closedUpperHalfPlaneModel) z₀ 1 +
      A z₀ (fderivWithin ℝ f (range closedUpperHalfPlaneModel) z₀ Complex.I) = 0 := by
  set U := O ∩ range closedUpperHalfPlaneModel
  have hU : U = range closedUpperHalfPlaneModel ∩ O := inter_comm _ _
  have hUD : UniqueDiffOn ℝ U := hU ▸ closedUpperHalfPlaneModel.uniqueDiffOn.inter hO
  have hUH : U = O ∩ {z : ℂ | 0 ≤ z.im} := congrArg (O ∩ ·) range_closedUpperHalfPlaneModel
  have hint : ∀ z ∈ O ∩ {z : ℂ | 0 < z.im}, U ∈ 𝓝 z := fun z hz ↦
    mem_interior_iff_mem_nhds.1
      (by rw [hUH, interior_inter_setOf_im_nonneg hO]; exact hz)
  -- The derivative within `U` is continuous on `U`, and it is the derivative off the real axis.
  have hdf : ContinuousOn (fderivWithin ℝ f U) U := hf.continuousOn_fderivWithin hUD le_rfl
  have hG : ContinuousOn
      (fun z ↦ fderivWithin ℝ f U z 1 + A z (fderivWithin ℝ f U z Complex.I)) U :=
    (hdf.clm_apply continuousOn_const).add (hA.clm_apply (hdf.clm_apply continuousOn_const))
  have hcl : z₀ ∈ closure (O ∩ {z : ℂ | 0 < z.im}) := by
    have h := subset_closure_interior_inter_setOf_im_nonneg hO
    rw [interior_inter_setOf_im_nonneg hO] at h
    exact h (hUH ▸ hz₀)
  have hG₀ : fderivWithin ℝ f U z₀ 1 + A z₀ (fderivWithin ℝ f U z₀ Complex.I) = 0 := by
    have hmem := ((hG z₀ hz₀).mono fun z hz ↦ mem_of_mem_nhds (hint z hz)).mem_closure_image hcl
    refine closure_minimal ?_ isClosed_singleton hmem
    rintro _ ⟨z, hz, rfl⟩
    simp only [mem_singleton_iff]
    rw [fderivWithin_of_mem_nhds (hint z hz)]
    exact h z hz
  rwa [hU, fderivWithin_inter (hO.mem_nhds hz₀.1)] at hG₀

variable [CompleteSpace E]

omit [HasGroupoid X borderedHolomorphicGroupoid] [CompleteSpace E] in
/-- The structure `J₀` pushed forward along a chart `ψ` of `M` is continuous along the coordinate
expression of a map of class `C¹`. -/
private theorem continuousOn_chartPushforward_chart (J₀ : SmoothAlmostComplexStructure I M)
    (hu : ContMDiffOn closedUpperHalfPlaneModel I 1 u s)
    (φ : OpenPartialHomeomorph X ClosedUpperHalfPlane) {ψ : OpenPartialHomeomorph M H}
    (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    ContinuousOn (fun z ↦ (J₀.toContMDiff ℓ).chartPushforward
        (ψ.extendTrans I (Homeomorph.refl E))
        ((ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) z))
      ((φ.extend closedUpperHalfPlaneModel).target ∩
        (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) := by
  have hc : ContinuousOn (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘
      (φ.extend closedUpperHalfPlaneModel).symm)
      ((φ.extend closedUpperHalfPlaneModel).target ∩
        (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
    ((ψ.extendTrans I (Homeomorph.refl E)).continuousOn.comp (hu.continuousOn.comp
      (φ.continuousOn_extend_symm.mono inter_subset_left) fun _ hz ↦ hz.2.1)
        fun _ hz ↦ by simpa using hz.2.2)
  refine ((J₀.toContMDiff ℓ).contDiffOn_chartPushforward
    (ψ.contMDiffOn_extendTrans hψ (Ψ := Homeomorph.refl E) contDiff_id)
    (ψ.contMDiffOn_extendTrans_symm hψ (Ψ := Homeomorph.refl E) contDiff_id)
      le_top).continuousOn.comp hc fun _ hz ↦ ?_
  exact (ψ.extendTrans I (Homeomorph.refl E)).map_source (by simpa using hz.2.2)

omit [CompleteSpace E] in
/-- **The equation in the charts at a point.** If the coordinate expression of `u` in the charts
at `x` and at `u x` solves `∂ₛf + J₀ ∂ₜf = 0` at the chart point, for the derivatives within the
closed upper half-plane, then `u` is pseudoholomorphic at `x`, also at a boundary point of `X`. -/
private theorem isPseudoholomorphicAt_of_fderivWithin_chart
    (J₀ : SmoothAlmostComplexStructure I M) {x : X}
    (hud : MDifferentiableAt closedUpperHalfPlaneModel I u x)
    (h : fderivWithin ℝ ((chartAt H (u x)).extendTrans I (Homeomorph.refl E) ∘ u ∘
        ((chartAt ClosedUpperHalfPlane x).extend closedUpperHalfPlaneModel).symm)
        (range closedUpperHalfPlaneModel)
        ((chartAt ClosedUpperHalfPlane x).extend closedUpperHalfPlaneModel x) 1 +
      (J₀.toContMDiff ℓ).chartPushforward ((chartAt H (u x)).extendTrans I (Homeomorph.refl E))
        (((chartAt H (u x)).extendTrans I (Homeomorph.refl E) ∘ u ∘
          ((chartAt ClosedUpperHalfPlane x).extend closedUpperHalfPlaneModel).symm)
          ((chartAt ClosedUpperHalfPlane x).extend closedUpperHalfPlaneModel x))
        (fderivWithin ℝ ((chartAt H (u x)).extendTrans I (Homeomorph.refl E) ∘ u ∘
          ((chartAt ClosedUpperHalfPlane x).extend closedUpperHalfPlaneModel).symm)
          (range closedUpperHalfPlaneModel)
          ((chartAt ClosedUpperHalfPlane x).extend closedUpperHalfPlaneModel x) Complex.I) = 0) :
    IsPseudoholomorphicAt (SmoothAlmostComplexStructure.ofBorderedHolomorphic X) J₀ u x := by
  set φ := chartAt ClosedUpperHalfPlane x
  set ψ := chartAt H (u x)
  set ψ' := ψ.extendTrans I (Homeomorph.refl E)
  set z₀ := φ.extend closedUpperHalfPlaneModel x
  have hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas _
  have hz₀x : (φ.extend closedUpperHalfPlaneModel).symm z₀ = x :=
    (φ.extend closedUpperHalfPlaneModel).left_inv (by simp [φ])
  have hg : MDifferentiableWithinAt 𝓘(ℝ, ℂ) I (u ∘ (φ.extend closedUpperHalfPlaneModel).symm)
      (range closedUpperHalfPlaneModel) z₀ :=
    MDifferentiableAt.comp_mdifferentiableWithinAt _ (by rwa [hz₀x])
      (mdifferentiableWithinAt_extend_symm (IsManifold.chart_mem_maximalAtlas x)
        ((φ.extend closedUpperHalfPlaneModel).map_source (by simp [φ])))
  have hgz : (u ∘ (φ.extend closedUpperHalfPlaneModel).symm) z₀ = u x := by
    rw [Function.comp_apply, hz₀x]
  have huψ : u x ∈ ψ'.source := by
    rw [OpenPartialHomeomorph.extendTrans_source]
    exact mem_chart_source H (u x)
  have hcr := ((J₀.toContMDiff ℓ).fderivWithin_chart_comp_add_eq_zero_iff hg
    (closedUpperHalfPlaneModel.uniqueDiffOn _ (mem_range_self _)) (hgz ▸ huψ)
    (hgz ▸ (ψ.contMDiffAt_extendTrans hψ contDiff_id (mem_chart_source H (u x))).mdifferentiableAt
      (by simp))
    (hgz ▸ (ψ.contMDiffAt_extendTrans_symm hψ contDiff_id (ψ'.map_source huψ)).mdifferentiableAt
      (by simp))).1 h
  rw [hgz] at hcr
  refine isPseudoholomorphicAt_iff_mfderiv.2 ⟨hud, fun (w : ℂ) ↦ ?_⟩
  rw [SmoothAlmostComplexStructure.ofBorderedHolomorphic_apply, smul_eq_mul,
    hud.mfderiv_eq_mfderivWithin_comp_extChartAt_symm, extChartAt]
  have hcrw := hcr w
  simp only [SmoothAlmostComplexStructure.toContMDiff_apply] at hcrw
  -- `hcrw` is the goal with `w : ℂ` in place of a tangent vector at `z₀` and the products taken in
  -- `ℂ`; the tangent spaces at `z₀` and `x` are `ℂ` by definition.
  exact hcrw

/-- **Weak solutions are pseudoholomorphic, at one point.** For the zero inhomogeneous term and a
map `u` of class `C¹` on an open set `s`, a weak solution up to the boundary is pseudoholomorphic
within `s` at each point `x ∈ s`, also at a boundary point of `X`: read in the charts at `x` and at
`u x`, the pointwise equation off the real axis extends to the real axis by continuity of the
derivative within the closed upper half-plane. -/
private theorem isPseudoholomorphicWithinAt_of_isWeakPseudoholomorphicOnBordered
    (J₀ : SmoothAlmostComplexStructure I M) (hs : IsOpen s)
    (hu : ContMDiffOn closedUpperHalfPlaneModel I 1 u s)
    (h : IsWeakPseudoholomorphicOnBordered (ContMDiffAlmostComplexStructureFamily.const
      (J₀.toContMDiff ℓ)) 0 p u s) {x : X} (hx : x ∈ s) :
    IsPseudoholomorphicWithinAt (SmoothAlmostComplexStructure.ofBorderedHolomorphic X) J₀ u s
      x := by
  set φ := chartAt ClosedUpperHalfPlane x
  set ψ := chartAt H (u x)
  have hφ : φ ∈ borderedHolomorphicGroupoid.maximalAtlas X :=
    StructureGroupoid.chart_mem_maximalAtlas _ x
  have hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas _
  have hxφ : x ∈ (φ.extend closedUpperHalfPlaneModel).source := by simp [φ]
  set U := (φ.extend closedUpperHalfPlaneModel).target ∩
    (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)
  set z₀ := φ.extend closedUpperHalfPlaneModel x
  have hw := h.isWeakCauchyRiemannOn_chart hφ hψ
  rw [ContMDiffAlmostComplexStructureFamily.chartField_const,
    InhomogeneousTerm.chartTermExtend_zero] at hw
  have hf := contDiffOn_chart hu hφ hψ
  have hJ := continuousOn_chartPushforward_chart (ℓ := ℓ) J₀ hu φ hψ
  -- `U` is an open set `O` intersected with the closed upper half-plane.
  set O := closedUpperHalfPlaneModel.symm ⁻¹' (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
  have hO : IsOpen O := (φ.isOpen_inter_preimage_symm (hu.continuousOn.isOpen_inter_preimage hs
    ψ.open_source)).preimage closedUpperHalfPlaneModel.continuous_symm
  have hUO : U = O ∩ range closedUpperHalfPlaneModel := by
    ext z
    simp only [U, O, OpenPartialHomeomorph.extend_target, OpenPartialHomeomorph.extend_coe_symm,
      mem_inter_iff, mem_preimage, Function.comp_apply]
    tauto
  have hz₀x : (φ.extend closedUpperHalfPlaneModel).symm z₀ = x :=
    (φ.extend closedUpperHalfPlaneModel).left_inv hxφ
  have hz₀ : z₀ ∈ U := ⟨(φ.extend closedUpperHalfPlaneModel).map_source hxφ, by
    rw [mem_preimage, hz₀x]
    exact ⟨hx, mem_chart_source H (u x)⟩⟩
  -- Off the real axis `U` is open, and there the weak equation is the pointwise one.
  have hpt := (isWeakCauchyRiemannOn_iff_of_contDiffOn (Ω := Opens.interior U)
    (hf.mono interior_subset) (hJ.mono interior_subset) continuousOn_const).1
      (hw.mono interior_subset)
  have hG₀ := fderivWithin_add_eq_zero_of_im_pos hO (hUO ▸ hf) (hUO ▸ hJ) (fun z hz ↦ hpt z
    (by
      rw [Opens.coe_interior, hUO, range_closedUpperHalfPlaneModel,
        interior_inter_setOf_im_nonneg hO]
      exact hz))
    (hUO ▸ hz₀)
  exact (isPseudoholomorphicAt_of_fderivWithin_chart J₀
    ((hu.contMDiffAt (hs.mem_nhds hx)).mdifferentiableAt one_ne_zero)
    hG₀).isPseudoholomorphicWithinAt

/-- **Pseudoholomorphic maps are weak solutions, in one pair of charts.** For a map `u` of class
`C¹` on an open set `s`, pseudoholomorphic there, the coordinate expression in a bordered
holomorphic chart `φ` of `X` and a chart `ψ` of `M` solves the homogeneous weak equation for `J₀`
pushed forward along `ψ`. The weak equation only sees points of positive imaginary part, where the
inverse of `φ` has complex linear derivative. -/
private theorem isWeakCauchyRiemannOn_chart_of_isPseudoholomorphicOn
    (J₀ : SmoothAlmostComplexStructure I M) (hs : IsOpen s)
    (hu : ContMDiffOn closedUpperHalfPlaneModel I 1 u s)
    (h : IsPseudoholomorphicOn (SmoothAlmostComplexStructure.ofBorderedHolomorphic X) J₀ u s)
    {φ : OpenPartialHomeomorph X ClosedUpperHalfPlane}
    (hφ : φ ∈ borderedHolomorphicGroupoid.maximalAtlas X)
    {ψ : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    IsWeakCauchyRiemannOn p ((φ.extend closedUpperHalfPlaneModel).target ∩
        (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
      (fun _ v ↦ (J₀.toContMDiff ℓ).chartPushforward (ψ.extendTrans I (Homeomorph.refl E)) v)
      (fun _ _ ↦ 0)
      (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) := by
  set ψ' := ψ.extendTrans I (Homeomorph.refl E)
  set U := (φ.extend closedUpperHalfPlaneModel).target ∩
    (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)
  have hf := contDiffOn_chart hu hφ hψ
  have hM : MemWkpLoc p U 1 (ψ' ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) := by
    have hw := (hu.memWkpLocMapOnBordered (p := p) le_rfl hs).memWkpLoc_chart hφ hψ
    rwa [← ψ.coe_extendTrans_refl I] at hw
  refine isWeakCauchyRiemannOn_iff_continuousOn_memWkpLoc_interior.2 ⟨hf.continuousOn, hM,
    isWeakCauchyRiemannOn_of_contDiffOn (Ω := Opens.interior U) (hf.mono interior_subset)
      fun z hz ↦ ?_⟩
  have hzU : z ∈ U := interior_subset hz
  set x := (φ.extend closedUpperHalfPlaneModel).symm z
  -- The interior of `U` lies in the open upper half-plane.
  have hzim : 0 < z.im :=
    interior_subset_setOf_im_pos (inter_subset_left.trans φ.extend_target_subset_range) hz
  have hφs := mdifferentiableAt_extend_symm_of_im_pos one_ne_zero
    (borderedHolomorphicGroupoid_maximalAtlas_subset (n := 1) (by exact_mod_cast le_top) hφ)
    hzU.1 hzim
  have hux : MDifferentiableAt closedUpperHalfPlaneModel I u x :=
    (hu.contMDiffAt (hs.mem_nhds hzU.2.1)).mdifferentiableAt one_ne_zero
  have hy : (u ∘ (φ.extend closedUpperHalfPlaneModel).symm) z ∈ ψ'.source := by
    simpa [ψ'] using hzU.2.2
  have hpx := (isPseudoholomorphicOn_iff.1 h x hzU.2.1).isPseudoholomorphicAt_of_mem_nhds
    (hs.mem_nhds hzU.2.1)
  -- Compose the equation `du ∘ j = J₀ ∘ du` at `x` with the derivative of the inverse chart.
  refine ((J₀.toContMDiff ℓ).fderiv_chart_comp_add_eq_zero_iff (hux.comp z hφs) hy
    ((ψ.contMDiffAt_extendTrans hψ contDiff_id hzU.2.2).mdifferentiableAt (by simp))
    ((ψ.contMDiffAt_extendTrans_symm hψ contDiff_id (ψ'.map_source hy)).mdifferentiableAt
      (by simp))).2 fun w ↦ ?_
  have hc := hpx.mfderiv_apply_commute
    (mfderiv 𝓘(ℝ, ℂ) closedUpperHalfPlaneModel (φ.extend closedUpperHalfPlaneModel).symm z w)
  rw [mfderiv_comp z hux hφs]
  -- Unfold the composite derivative; the tangent spaces of `ℂ` and of `X` are `ℂ` by definition.
  change mfderiv closedUpperHalfPlaneModel I u x (mfderiv 𝓘(ℝ, ℂ) closedUpperHalfPlaneModel
      (φ.extend closedUpperHalfPlaneModel).symm z (Complex.I * w)) =
    (J₀.toContMDiff ℓ) ((u ∘ (φ.extend closedUpperHalfPlaneModel).symm) z)
      (mfderiv closedUpperHalfPlaneModel I u x (mfderiv 𝓘(ℝ, ℂ) closedUpperHalfPlaneModel
        (φ.extend closedUpperHalfPlaneModel).symm z w))
  rw [SmoothAlmostComplexStructure.mfderiv_extend_symm_I_mul_of_mem_maximalAtlas hφ hzU.1 hzim,
    SmoothAlmostComplexStructure.toContMDiff_apply]
  exact hc

/-- **Comparison with `IsPseudoholomorphicOn`.** For the zero inhomogeneous term, a smooth almost
complex structure `J₀` on `M` regarded as a domain-independent family, and a map `u` of class `C¹`
on an open set `s` of a Riemann surface with boundary, the weak pseudoholomorphic equation up to
the boundary, for any exponent, is pseudoholomorphy of `u` on `s` for the structure `j` of `X` and
`J₀`, at the boundary points of `X` as well as at the interior points. -/
theorem isWeakPseudoholomorphicOnBordered_iff_isPseudoholomorphicOn
    (J₀ : SmoothAlmostComplexStructure I M) (hs : IsOpen s)
    (hu : ContMDiffOn closedUpperHalfPlaneModel I 1 u s) :
    IsWeakPseudoholomorphicOnBordered (ContMDiffAlmostComplexStructureFamily.const
        (J₀.toContMDiff ℓ)) 0 p u s ↔
      IsPseudoholomorphicOn (SmoothAlmostComplexStructure.ofBorderedHolomorphic X) J₀ u s := by
  refine ⟨fun h ↦ isPseudoholomorphicOn_iff.2 fun x hx ↦
    isPseudoholomorphicWithinAt_of_isWeakPseudoholomorphicOnBordered J₀ hs hu h hx, fun h ↦
      isWeakPseudoholomorphicOnBordered_iff.2 ⟨hu.memWkpLocMapOnBordered le_rfl hs,
        fun φ hφ ψ hψ ↦ ?_⟩⟩
  rw [ContMDiffAlmostComplexStructureFamily.chartField_const,
    InhomogeneousTerm.chartTermExtend_zero]
  exact isWeakCauchyRiemannOn_chart_of_isPseudoholomorphicOn J₀ hs hu h hφ hψ

/-- **Comparison with `IsPseudoholomorphic`.** For the zero inhomogeneous term, a smooth almost
complex structure `J₀` on `M` regarded as a domain-independent family, and a map `u` of class `C¹`
on a Riemann surface with boundary, the weak pseudoholomorphic equation up to the boundary, for
any exponent, is pseudoholomorphy of `u` for the structure `j` of `X` and `J₀`. -/
theorem isWeakPseudoholomorphicBordered_iff_isPseudoholomorphic
    (J₀ : SmoothAlmostComplexStructure I M) (hu : ContMDiff closedUpperHalfPlaneModel I 1 u) :
    IsWeakPseudoholomorphicBordered (ContMDiffAlmostComplexStructureFamily.const
        (J₀.toContMDiff ℓ)) 0 p u ↔
      IsPseudoholomorphic (SmoothAlmostComplexStructure.ofBorderedHolomorphic X) J₀ u := by
  rw [← isWeakPseudoholomorphicOnBordered_univ, ← isPseudoholomorphicOn_univ]
  exact isWeakPseudoholomorphicOnBordered_iff_isPseudoholomorphicOn J₀ isOpen_univ hu.contMDiffOn

/-! ### Checks on the closed upper half-plane -/

-- The inclusion of the closed upper half-plane into `ℂ`, pseudoholomorphic at the boundary points
-- too, is a weak solution up to the boundary for the structure `i` of `ℂ`.
example : IsWeakPseudoholomorphicBordered (ContMDiffAlmostComplexStructureFamily.const
    ((SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).toContMDiff ℓ)) 0 p
      ((↑) : ClosedUpperHalfPlane → ℂ) :=
  (isWeakPseudoholomorphicBordered_iff_isPseudoholomorphic _
    ClosedUpperHalfPlane.contMDiff_coe).2
      SmoothAlmostComplexStructure.isPseudoholomorphic_coe_ofBorderedHolomorphic

/-- **Conjugation is not pseudoholomorphic.** The map `z ↦ conj z` from the closed upper
half-plane to `ℂ` is not pseudoholomorphic, for the structure of the closed upper half-plane and
the complex structure of `ℂ`, on any nonempty open set: by the comparison it would be a weak
solution, which `TauCeti.not_isWeakPseudoholomorphicOnBordered_conj` excludes. -/
theorem not_isPseudoholomorphicOn_conj {s : Set ClosedUpperHalfPlane} (hs : IsOpen s)
    (hne : s.Nonempty) :
    ¬IsPseudoholomorphicOn (SmoothAlmostComplexStructure.ofBorderedHolomorphic ClosedUpperHalfPlane)
      (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ)
        (fun z : ClosedUpperHalfPlane ↦ conj (z : ℂ)) s := by
  have hu : ContMDiffOn closedUpperHalfPlaneModel 𝓘(ℝ, ℂ) 1
      (fun z : ClosedUpperHalfPlane ↦ conj (z : ℂ)) s :=
    (Complex.conjCLE.contDiff.contMDiff.comp
      ClosedUpperHalfPlane.contMDiff_coe).contMDiffOn
  exact fun h ↦ not_isWeakPseudoholomorphicOnBordered_conj (ℓ := ⊤) (p := 2) hs hne
    ((isWeakPseudoholomorphicOnBordered_iff_isPseudoholomorphicOn _ hs hu).2 h)

end TauCeti
