/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Jacobian determinants of extended coordinate changes

Continuity, strict positivity, and the chain rule for the absolute Jacobian determinant of `C¹`
extended coordinate changes `I.extendCoordChange e e'`, together with continuity of the product of
the Jacobian determinant with a continuous function supported in the target chart's source.

## Main results

* `ModelWithCorners.fderivWithin_extendCoordChange_range_eq_fderivWithin_source`:
  `fderivWithin` over `Set.range I` agrees with `fderivWithin` over the overlap source.
* `ModelWithCorners.continuousOn_abs_det_fderivWithin_extendCoordChange`: continuity of the
  absolute Jacobian determinant on the overlap source.
* `ModelWithCorners.abs_det_fderivWithin_extendCoordChange_pos`: strict positivity of the absolute
  Jacobian determinant on the overlap source.
* `ModelWithCorners.abs_det_fderivWithin_extendCoordChange_comp`: chain rule on triple chart
  overlaps.
* `OpenPartialHomeomorph.continuousOn_abs_det_fderivWithin_extendCoordChange_mul`: continuity
  of the extension-by-zero product with a continuous function supported in the target chart.
-/

public section

open Set
open scoped Manifold Topology

/-- On the source of an extended coordinate change, the `fderivWithin` over `Set.range I` agrees
with the `fderivWithin` over the overlap source. -/
theorem ModelWithCorners.fderivWithin_extendCoordChange_range_eq_fderivWithin_source
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    {M : Type*} [TopologicalSpace M]
    {e e' : OpenPartialHomeomorph M H} {y : E} (hy : y ∈ (I.extendCoordChange e e').source) :
    fderivWithin 𝕜 (I.extendCoordChange e e') (Set.range I) y =
      fderivWithin 𝕜 (I.extendCoordChange e e') (I.extendCoordChange e e').source y := by
  refine fderivWithin_congr_set ?_
  have hsub : (I.extendCoordChange e e').source ⊆ Set.range I := by
    rw [I.extendCoordChange_source]
    exact Set.image_subset_range _ _
  have h := nhdsWithin_restrict'' (Set.range I) (I.extendCoordChange_source_mem_nhdsWithin hy)
  rw [Set.inter_eq_right.2 hsub] at h
  exact nhdsWithin_eq_iff_eventuallyEqSet.1 h

section ExtendCoordChangeDet

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

namespace ModelWithCorners

/-- The absolute Jacobian determinant of a `C¹` extended coordinate change is continuous on
its source. -/
theorem continuousOn_abs_det_fderivWithin_extendCoordChange
    {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (he' : e' ∈ IsManifold.maximalAtlas I 1 M) :
    ContinuousOn
      (fun y ↦ |(fderivWithin ℝ (I.extendCoordChange e e') (Set.range I) y).det|)
      (I.extendCoordChange e e').source := by
  set Φ := I.extendCoordChange e e'
  have hcont : ContinuousOn (fun y ↦ fderivWithin ℝ Φ Φ.source y) Φ.source :=
    (I.contDiffOn_extendCoordChange he he').continuousOn_fderivWithin
      I.uniqueDiffOn_extendCoordChange_source le_rfl
  have hdet : ContinuousOn (fun y ↦ |(fderivWithin ℝ Φ Φ.source y).det|) Φ.source :=
    (continuous_abs.comp ContinuousLinearMap.continuous_det).comp_continuousOn hcont
  exact hdet.congr fun y hy ↦ by
    rw [I.fderivWithin_extendCoordChange_range_eq_fderivWithin_source hy]

/-- The absolute Jacobian determinant of a `C¹` extended coordinate change is strictly
positive at every point of its source. -/
theorem abs_det_fderivWithin_extendCoordChange_pos
    {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (he' : e' ∈ IsManifold.maximalAtlas I 1 M)
    {y : E} (hy : y ∈ (I.extendCoordChange e e').source) :
    0 < |(fderivWithin ℝ (I.extendCoordChange e e') (Set.range I) y).det| := by
  rw [I.fderivWithin_extendCoordChange_range_eq_fderivWithin_source hy, abs_pos]
  obtain ⟨A, hA⟩ := I.isInvertible_fderivWithin_extendCoordChange one_ne_zero he he' hy
  rw [← hA]
  exact A.toLinearEquiv.isUnit_det'.ne_zero

/-- Chain rule for the absolute Jacobian determinants of `C¹` extended coordinate changes on a
triple chart overlap. -/
theorem abs_det_fderivWithin_extendCoordChange_comp
    {e e' e'' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (he' : e' ∈ IsManifold.maximalAtlas I 1 M)
    (he'' : e'' ∈ IsManifold.maximalAtlas I 1 M) {x : M}
    (hxe : x ∈ e.source) (hxe' : x ∈ e'.source) (hxe'' : x ∈ e''.source) :
    |(fderivWithin ℝ (I.extendCoordChange e e'') (Set.range I) (e.extend I x)).det| =
      |(fderivWithin ℝ (I.extendCoordChange e' e'') (Set.range I) (e'.extend I x)).det| *
        |(fderivWithin ℝ (I.extendCoordChange e e') (Set.range I) (e.extend I x)).det| := by
  set y := e.extend I x
  set z := e'.extend I x
  have hy_ee' : y ∈ (I.extendCoordChange e e').source := by
    rw [← OpenPartialHomeomorph.extend_image_source_inter (f := e) (f' := e')]
    exact Set.mem_image_of_mem _ ⟨hxe, hxe'⟩
  have hz_e'e'' : z ∈ (I.extendCoordChange e' e'').source := by
    rw [← OpenPartialHomeomorph.extend_image_source_inter (f := e') (f' := e'')]
    exact Set.mem_image_of_mem _ ⟨hxe', hxe''⟩
  have hΦy : I.extendCoordChange e e' y = z := by
    have hye : x ∈ (e.extend I).source := by rwa [e.extend_source]
    simp only [y, z, ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply,
      (e.extend I).left_inv hye]
  have hd1 : DifferentiableWithinAt ℝ (I.extendCoordChange e e') (Set.range I) y :=
    (I.contDiffWithinAt_extendCoordChange he he' hy_ee').differentiableWithinAt one_ne_zero
  have hd2 : DifferentiableWithinAt ℝ (I.extendCoordChange e' e'') (Set.range I) z :=
    (I.contDiffWithinAt_extendCoordChange he' he'' hz_e'e'').differentiableWithinAt one_ne_zero
  have hU : UniqueDiffWithinAt ℝ (Set.range I) y :=
    I.uniqueDiffOn y (e.extend_target_subset_range
      ((e.extend I).map_source (by rwa [e.extend_source])))
  have hmaps : Set.MapsTo (I.extendCoordChange e e') (Set.range I) (Set.range I) := fun _ _ ↦
    Set.mem_range_self _
  have heq : I.extendCoordChange e e'' =ᶠ[𝓝[Set.range I] y]
      I.extendCoordChange e' e'' ∘ I.extendCoordChange e e' := by
    have hmem : (I.extendCoordChange e e').source ∩ (I.extendCoordChange e e'').source ∈
        𝓝[Set.range I] y :=
      Filter.inter_mem (I.extendCoordChange_source_mem_nhdsWithin' hxe hxe')
        (I.extendCoordChange_source_mem_nhdsWithin' hxe hxe'')
    filter_upwards [hmem] with w hw
    have hxw' : (e.extend I).symm w ∈ (e'.extend I).source := hw.1.2
    simp only [Function.comp_apply, ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply,
      (e'.extend I).left_inv hxw']
  have heq0 : I.extendCoordChange e e'' y =
      (I.extendCoordChange e' e'' ∘ I.extendCoordChange e e') y := by
    have hxw' : x ∈ (e'.extend I).source := by rwa [e'.extend_source]
    have hxe_s : x ∈ (e.extend I).source := by rwa [e.extend_source]
    simp only [Function.comp_apply, y, ModelWithCorners.extendCoordChange,
      PartialEquiv.trans_apply, (e.extend I).left_inv hxe_s, (e'.extend I).left_inv hxw']
  rw [heq.fderivWithin_eq heq0, fderivWithin_comp y (hΦy ▸ hd2) hd1 hmaps hU, hΦy]
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
    abs_mul]

end ModelWithCorners

open Classical in
/-- Multiplying the absolute Jacobian determinant of a `C¹` extended coordinate change by a
continuous function supported in the target chart's source and extending by zero outside the
overlap gives a function continuous on `(e₀.extend I).target`. -/
theorem OpenPartialHomeomorph.continuousOn_abs_det_fderivWithin_extendCoordChange_mul
    (e₀ e₁ : OpenPartialHomeomorph M H) (I : ModelWithCorners ℝ E H)
    (he₀ : e₀ ∈ IsManifold.maximalAtlas I 1 M) (he₁ : e₁ ∈ IsManifold.maximalAtlas I 1 M)
    {f : M → ℝ} (hf : Continuous f) (hsupp : tsupport f ⊆ e₁.source) :
    ContinuousOn
      ((I.extendCoordChange e₀ e₁).source.indicator fun y ↦
        |(fderivWithin ℝ (I.extendCoordChange e₀ e₁) (range I) y).det| *
          f ((e₀.extend I).symm y))
      (e₀.extend I).target := by
  set Φ := I.extendCoordChange e₀ e₁
  intro y hy
  by_cases hyΦ : y ∈ Φ.source
  · have hmem : Φ.source ∈ 𝓝[(e₀.extend I).target] y :=
      nhdsWithin_mono y e₀.extend_target_subset_range
        (I.extendCoordChange_source_mem_nhdsWithin hyΦ)
    have hcont : ContinuousOn
        (fun z ↦ |(fderivWithin ℝ Φ (range I) z).det| * f ((e₀.extend I).symm z)) Φ.source :=
      (I.continuousOn_abs_det_fderivWithin_extendCoordChange he₀ he₁).mul
        (hf.comp_continuousOn (e₀.continuousOn_extend_symm.mono fun _ hz ↦ hz.1))
    refine ((hcont y hyΦ).mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem hmem fun z hz ↦ Set.indicator_of_mem hz _)
      (Set.indicator_of_mem hyΦ _)
  · have hnotSupp : (e₀.extend I).symm y ∉ tsupport f := fun hmem ↦ by
      have hxe : (e₀.extend I).symm y ∈ e₀.source :=
        e₀.extend_source (I := I) ▸ (e₀.extend I).map_target hy
      apply hyΦ
      rw [← OpenPartialHomeomorph.extend_image_source_inter (f := e₀) (f' := e₁)]
      exact ⟨(e₀.extend I).symm y, ⟨hxe, hsupp hmem⟩, (e₀.extend I).right_inv hy⟩
    have hmem : (e₀.extend I).symm ⁻¹' (tsupport f)ᶜ ∈ 𝓝[(e₀.extend I).target] y :=
      (e₀.continuousOn_extend_symm y hy).preimage_mem_nhdsWithin
        ((isClosed_tsupport f).isOpen_compl.mem_nhds hnotSupp)
    refine (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem hmem fun z hz ↦ ?_) (Set.indicator_of_notMem hyΦ _)
    have hf0 : f ((e₀.extend I).symm z) = 0 :=
      (notMem_tsupport_iff_eventuallyEq.1 hz).self_of_nhds
    by_cases hzΦ : z ∈ Φ.source
    · rw [Set.indicator_of_mem hzΦ, hf0, mul_zero]
    · exact Set.indicator_of_notMem hzΦ _

end ExtendCoordChangeDet
