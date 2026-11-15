/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Density.Basic
public import TauCeti.LinearAlgebra.Density.Topology
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Chart.Basic
public import TauCeti.Geometry.Manifold.ExtChartAt
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Coordinate expressions and chart changes for rough densities

A rough density `μ : RoughDensity I M k` is read in the preferred extended chart at `x₀` as the
model-space density field `μ.inChartAt x₀ : E → Density E k`, pulling `μ ((extChartAt I x₀).symm z)`
back along the within-range derivative `mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (range I) z`.
Working within `range I` includes boundary and corner points without extra hypotheses.

On an overlap of two preferred charts, `μ.inChartAt` pulls back by the Fréchet derivative of the
coordinate change within `range I`, so its evaluation on any tuple transforms by the absolute
determinant `|det D(φ_β ∘ φ_α⁻¹)|` (`TauCeti.RoughDensity.inChartAt_apply_eq_abs_det_mul`).
Consequently, by the change-of-variables formula for additive Haar measures, both set integrals and
set integrability of `μ.inChartAt` agree across chart overlaps with no orientation or sign data
(`TauCeti.RoughDensity.setIntegral_inChartAt_changeChart`,
`TauCeti.RoughDensity.integrableOn_inChartAt_changeChart`).

The coordinate and overlap-Jacobian structure parallels the oriented top-form API in
`TauCeti.Geometry.Manifold.DifferentialForm.Chart` and
`TauCeti.Geometry.Manifold.DifferentialForm.Integration.Chart.Basic`, replacing signed Jacobian
cocycle data with the unsigned absolute determinant.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16, Densities.
-/

public section

noncomputable section

open Set Filter MeasureTheory Function
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {k : ℕ}

namespace RoughDensity

/-! ### Topological support of rough densities -/

/-- A point lies in the support of a rough density, taken with the model-space codomain
`Density E k`, exactly when the density is nonzero in the tangent fibre there. -/
theorem mem_support_iff {μ : RoughDensity I M k} {x : M} :
    x ∈ support (M := Density E k) μ ↔ μ x ≠ 0 :=
  Iff.rfl

/-- The zero rough density has compact topological support. -/
theorem isCompact_tsupport_zero :
    IsCompact (_root_.tsupport (α := Density E k) (0 : RoughDensity I M k)) := by
  -- Identify the dependent zero section with a fixed-codomain zero function so `tsupport_zero`
  -- applies directly.
  change IsCompact (_root_.tsupport (0 : M → Density E k))
  simp

/-- Scalar multiplication does not enlarge the topological support of a rough density. -/
theorem tsupport_smul_subset (c : ℝ) (μ : RoughDensity I M k) :
    _root_.tsupport (α := Density E k) (c • μ) ⊆
      _root_.tsupport (α := Density E k) μ := by
  refine closure_minimal ?_ (_root_.isClosed_tsupport (α := Density E k) μ)
  intro x hx
  by_contra hxsupport
  have hμ : μ x = 0 := by
    by_contra h
    exact hxsupport (subset_tsupport (α := Density E k) μ h)
  apply hx
  -- Expose fibrewise scalar multiplication so `hμ` rewrites it to zero.
  change c • μ x = 0
  rw [hμ, smul_zero]

/-- Multiplication by a nonzero constant preserves the topological support of a rough density. -/
theorem tsupport_smul (c : ℝ) (μ : RoughDensity I M k) (hc : c ≠ 0) :
    _root_.tsupport (α := Density E k) (c • μ) =
      _root_.tsupport (α := Density E k) μ := by
  simp only [_root_.tsupport]
  congr 1
  ext x
  -- Expose the fibrewise scalar action so `hc` cancels without unfolding dependent types.
  change c • μ x ≠ 0 ↔ μ x ≠ 0
  exact smul_ne_zero_iff_right hc

/-- Negating a rough density preserves its topological support. -/
@[simp]
theorem tsupport_neg (μ : RoughDensity I M k) :
    _root_.tsupport (α := Density E k) (-μ) = _root_.tsupport (α := Density E k) μ := by
  rw [← neg_one_smul ℝ μ]
  exact tsupport_smul (-1) μ (by norm_num)

/-- The sum of two rough densities with compact topological support has compact topological
support. -/
theorem isCompact_tsupport_add {μ ν : RoughDensity I M k}
    (hμ : IsCompact (_root_.tsupport (α := Density E k) μ))
    (hν : IsCompact (_root_.tsupport (α := Density E k) ν)) :
    IsCompact (_root_.tsupport (α := Density E k) (μ + ν)) :=
  -- Tangent fibres are definitionally `E`, giving the fixed codomain for `HasCompactSupport.add`.
  HasCompactSupport.add (f := (show M → Density E k from μ)) hμ hν

/-! ### Coordinate expression in a preferred chart -/

/-- The coordinate expression of a rough density in the preferred extended chart at `x₀`: its
pullback along `(extChartAt I x₀).symm`, with derivatives taken within `range I`. -/
def inChartAt (μ : RoughDensity I M k) (x₀ : M) (z : E) : Density E k where
  toFun v :=
    μ ((extChartAt I x₀).symm z)
      (fun i ↦ mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (range I) z (v i))
  map_comp T v := by
    let x := (extChartAt I x₀).symm z
    let e := (tangentSpaceCastModel I x).toLinearEquiv
    let f : E →ₗ[ℝ] E :=
      e.toLinearMap.comp
        ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (range I) z).toLinearMap.comp
          (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm.toLinearMap)
    have h := (((μ x).compLinearEquiv e.symm).compLinearMap f).comp_apply T v
    simp only [Density.compLinearMap_apply, Density.compLinearEquiv_apply] at h
    exact h

/-- Pointwise formula for the coordinate expression of a rough density in the preferred extended
chart at `x₀`. -/
theorem inChartAt_apply (μ : RoughDensity I M k) (x₀ : M) (z : E) (v : Fin k → E) :
    μ.inChartAt x₀ z v =
      μ ((extChartAt I x₀).symm z)
        (fun i ↦ mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (range I) z (v i)) :=
  (rfl)

@[simp]
theorem inChartAt_zero (x₀ : M) : (0 : RoughDensity I M k).inChartAt x₀ = 0 := by
  funext z
  ext v
  rfl

@[simp]
theorem inChartAt_add (μ ν : RoughDensity I M k) (x₀ : M) :
    (μ + ν).inChartAt x₀ = μ.inChartAt x₀ + ν.inChartAt x₀ := by
  funext z
  ext v
  rfl

@[simp]
theorem inChartAt_smul (c : ℝ) (μ : RoughDensity I M k) (x₀ : M) :
    (c • μ).inChartAt x₀ = c • μ.inChartAt x₀ := by
  funext z
  ext v
  rfl

@[simp]
theorem inChartAt_neg (μ : RoughDensity I M k) (x₀ : M) :
    (-μ).inChartAt x₀ = -μ.inChartAt x₀ := by
  funext z
  ext v
  rfl

@[simp]
theorem inChartAt_sub (μ ν : RoughDensity I M k) (x₀ : M) :
    (μ - ν).inChartAt x₀ = μ.inChartAt x₀ - ν.inChartAt x₀ := by
  funext z
  ext v
  rfl

/-- Pointwise scalar localization of a rough density multiplies its coordinate expression by the
pulled-back scalar. -/
theorem inChartAt_fun_smul (f : M → ℝ) (μ : RoughDensity I M k) (α : M) (y : E) :
    inChartAt (I := I) (fun x ↦ f x • μ x) α y =
      f ((extChartAt I α).symm y) • μ.inChartAt α y := by
  ext v
  rfl

/-- Restricting a rough density by an indicator function restricts its coordinate expression on the
chart target to the preimage of the set. -/
theorem inChartAt_indicator (s : Set M) (μ : RoughDensity I M k) (α : M) (y : E) (v : Fin k → E) :
    inChartAt (I := I) (fun x ↦ s.indicator (fun _ ↦ (1 : ℝ)) x • μ x) α y v =
      ((extChartAt I α).symm ⁻¹' s).indicator (fun z ↦ μ.inChartAt α z v) y := by
  rw [inChartAt_fun_smul, Density.smul_apply, smul_eq_mul]
  by_cases hs : y ∈ (extChartAt I α).symm ⁻¹' s
  · have hs' : (extChartAt I α).symm y ∈ s := hs
    rw [Set.indicator_of_mem hs', Set.indicator_of_mem hs, one_mul]
  · have hs' : (extChartAt I α).symm y ∉ s := hs
    rw [Set.indicator_of_notMem hs', Set.indicator_of_notMem hs, zero_mul]

/-- If a family of sets `u i` covers `tsupport μ`, then the coordinate coefficient of `μ` in any
preferred chart `α`, restricted by indicator to `(extChartAt I α).target`, is supported inside the
union of the chart images `(extChartAt I α) '' ((extChartAt I α).source ∩ u i)`. -/
theorem support_target_indicator_inChartAt_subset {ι : Type*} (μ : RoughDensity I M k) (α : M)
    (v : Fin k → E) {u : ι → Set M}
    (hcover : _root_.tsupport (α := Density E k) μ ⊆ ⋃ i, u i) :
    support ((extChartAt I α).target.indicator fun y ↦ μ.inChartAt α y v) ⊆
      ⋃ i, (extChartAt I α) '' ((extChartAt I α).source ∩ u i) := by
  intro y hy
  by_cases ht : y ∈ (extChartAt I α).target
  · have hne : μ.inChartAt α y v ≠ 0 := by
      simpa only [Set.indicator_of_mem ht] using Function.mem_support.mp hy
    have hμne : μ ((extChartAt I α).symm y) ≠ 0 := fun hz ↦
      hne (by rw [inChartAt_apply, hz]; rfl)
    obtain ⟨i, hi⟩ := mem_iUnion.mp
      (hcover (_root_.subset_tsupport (α := Density E k) μ hμne))
    exact mem_iUnion.mpr ⟨i, ⟨(extChartAt I α).symm y,
      ⟨(extChartAt I α).map_target ht, hi⟩, (extChartAt I α).right_inv ht⟩⟩
  · exact False.elim (Function.mem_support.mp hy (Set.indicator_of_notMem ht _))

/-- Evaluating a chart expression at a chart image transports each argument through the tangent
coordinate change. -/
theorem inChartAt_chart_apply [IsManifold I 1 M] (μ : RoughDensity I M k) (α : M) {x : M}
    (hx : x ∈ (extChartAt I α).source) (v : Fin k → E) :
    μ.inChartAt α (extChartAt I α x) v =
      μ x (fun i ↦ tangentCoordChange I α x x (v i)) := by
  rw [inChartAt_apply]
  have hx' : x ∈ (chartAt H α).source := by simpa only [extChartAt_source] using hx
  rw [← TangentBundle.symmL_trivializationAt hx', TangentBundle.symmL_trivializationAt_eq_core hx',
    (extChartAt I α).left_inv hx]
  rfl

/-- At the center `x` of the preferred extended chart at `x`, the coordinate expression of a rough
density on a `C¹` manifold equals `μ x`. Not a `simp` lemma because `simp` unfolds `extChartAt` on
the left-hand side before this lemma can fire. -/
theorem inChartAt_extChartAt_self [IsManifold I 1 M] (μ : RoughDensity I M k) (x : M) :
    μ.inChartAt x (extChartAt I x x) = μ x := by
  ext v
  rw [inChartAt_chart_apply μ x (mem_extChartAt_source x)]
  simp only [tangentCoordChange_self (mem_extChartAt_source x)]
  rfl

/-- Over a normed model space `𝓘(ℝ, E)`, the coordinate expression in any chart is the density
itself. -/
@[simp]
theorem inChartAt_model (μ : RoughDensity 𝓘(ℝ, E) E k) (x₀ z : E) :
    μ.inChartAt x₀ z = μ z := by
  ext v
  have hz : z ∈ (extChartAt 𝓘(ℝ, E) x₀).source := by simp
  have h := inChartAt_chart_apply μ x₀ hz v
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq] at h
  rw [h]
  congr 1
  funext i
  exact DFunLike.congr_fun (TangentBundle.coordChange_model_space (𝕜 := ℝ) x₀ z z) (v i)

/-- Evaluating a chart expression at a chart image agrees with evaluation on the inverse local
tangent frame of `trivializationAt`. -/
theorem inChartAt_trivializationAt_apply [IsManifold I 1 M] (μ : RoughDensity I M k) (α : M) {x : M}
    (hx : x ∈ (extChartAt I α).source) (v : Fin k → E) :
    μ.inChartAt α (extChartAt I α x) v =
      μ x (fun i ↦ (trivializationAt E (TangentSpace I) α).symm x (v i)) := by
  rw [inChartAt_chart_apply μ α hx]
  have hx' : x ∈ (chartAt H α).source := by simpa only [extChartAt_source] using hx
  refine congrArg (μ x) (funext fun i ↦ ?_)
  have hcore := DFunLike.congr_fun
    (TangentBundle.symmL_trivializationAt_eq_core (I := I) hx') (v i)
  have hsymm := (trivializationAt E (TangentSpace I) α).symmL_apply (R := ℝ)
    (by simpa using hx') (v i)
  exact hcore.symm.trans hsymm

/-- Two rough densities agreeing on a subset of a chart source have the same coordinate expressions
on its coordinate image. -/
theorem eqOn_inChartAt_image {μ ν : RoughDensity I M k} {s : Set M} (h : ∀ x ∈ s, μ x = ν x)
    (α : M) (hs : s ⊆ (extChartAt I α).source) :
    EqOn (μ.inChartAt α) (ν.inChartAt α) ((extChartAt I α) '' s) := by
  rintro _ ⟨x, hx, rfl⟩
  ext v
  rw [inChartAt_apply, inChartAt_apply, (extChartAt I α).left_inv (hs hx), h x hx]

/-- Two rough densities have the same coordinate expression at the chart image of a point of the
chart source exactly when they agree at that point. -/
theorem inChartAt_chart_eq_iff [IsManifold I 1 M] {μ ν : RoughDensity I M k} {α x : M}
    (hx : x ∈ (extChartAt I α).source) :
    μ.inChartAt α (extChartAt I α x) = ν.inChartAt α (extChartAt I α x) ↔ μ x = ν x := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hinv (w : E) : tangentCoordChange I α x x (tangentCoordChange I x α x w) = w := by
      rw [tangentCoordChange_comp ⟨⟨mem_extChartAt_source x, hx⟩, mem_extChartAt_source x⟩,
        tangentCoordChange_self (mem_extChartAt_source x)]
    ext v
    have hv := congrArg (fun A : Density E k ↦ A fun i ↦ tangentCoordChange I x α x (v i)) h
    rw [inChartAt_chart_apply _ _ hx, inChartAt_chart_apply _ _ hx] at hv
    have hfun : (fun i ↦ tangentCoordChange I α x x (tangentCoordChange I x α x (v i))) = v :=
      funext fun i ↦ hinv (v i)
    rwa [hfun] at hv
  · ext v
    rw [inChartAt_chart_apply _ _ hx, inChartAt_chart_apply _ _ hx, h]

/-- On an overlap of two preferred charts, a rough density read in the first chart is the pullback
of its expression in the second chart along the within-range derivative of the coordinate
change. -/
theorem inChartAt_eq_compLinearMap [IsManifold I 1 M] (μ : RoughDensity I M k)
    {x₀ x : M} {z : E} (hz : z ∈ (extChartAt I x₀).target)
    (hx : (extChartAt I x₀).symm z ∈ (extChartAt I x).source) :
    μ.inChartAt x₀ z =
      (μ.inChartAt x (extChartAt I x ((extChartAt I x₀).symm z))).compLinearMap
        (fderivWithin ℝ (extChartAt I x ∘ (extChartAt I x₀).symm) (range I) z).toLinearMap := by
  have hleft : (extChartAt I x).symm (extChartAt I x ((extChartAt I x₀).symm z)) =
      (extChartAt I x₀).symm z := (extChartAt I x).left_inv hx
  have hpre : (extChartAt I x₀).symm ⁻¹' (extChartAt I x).source ∈ 𝓝[range I] z :=
    (continuousAt_extChartAt_symm'' hz).continuousWithinAt.preimage_mem_nhdsWithin
      (extChartAt_source_mem_nhds' hx)
  have hcoord : ((extChartAt I x).symm ∘ (extChartAt I x ∘ (extChartAt I x₀).symm))
      =ᶠ[𝓝[range I] z] (extChartAt I x₀).symm := by
    filter_upwards [hpre] with a ha
    exact (extChartAt I x).left_inv ha
  have hcomp :
      mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x).symm ∘
        (extChartAt I x ∘ (extChartAt I x₀).symm)) (range I) z =
        (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I)
          (extChartAt I x ((extChartAt I x₀).symm z))).comp
          (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E)
            (extChartAt I x ∘ (extChartAt I x₀).symm) (range I) z) := by
    apply mfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq
      (I' := 𝓘(ℝ, E)) (I'' := I) (u := range I) z
    · exact mdifferentiableWithinAt_extChartAt_symm ((extChartAt I x).map_source hx)
    · exact ((contDiffWithinAt_ext_coord_change (𝕜 := ℝ) (n := 1) x x₀ (by
        rw [PartialEquiv.trans_source]
        exact ⟨by simpa only [PartialEquiv.symm_source] using hz, hx⟩)).differentiableWithinAt
          (by simp)).mdifferentiableWithinAt
    · filter_upwards [hpre] with a ha
      exact extChartAt_target_subset_range x ((extChartAt I x).map_source ha)
    · exact I.uniqueDiffOn.uniqueDiffWithinAt (extChartAt_target_subset_range x₀ hz)
        |>.uniqueMDiffWithinAt
    · rfl
  rw [hcoord.mfderivWithin_eq hleft, mfderivWithin_eq_fderivWithin] at hcomp
  ext v
  rw [inChartAt_apply, Density.compLinearMap_apply, inChartAt_apply, hleft]
  congr 1
  funext i
  exact congrArg (fun L ↦ L (v i)) hcomp

/-- On an overlap of two preferred charts, evaluating the coordinate expression of a rough density
transforms by the absolute determinant of the coordinate-change derivative within `range I`. -/
theorem inChartAt_apply_eq_abs_det_mul [IsManifold I 1 M] (μ : RoughDensity I M k)
    {x₀ x : M} {z : E} (hz : z ∈ (extChartAt I x₀).target)
    (hx : (extChartAt I x₀).symm z ∈ (extChartAt I x).source) (v : Fin k → E) :
    μ.inChartAt x₀ z v =
      |(fderivWithin ℝ (extChartAt I x ∘ (extChartAt I x₀).symm) (range I) z).toLinearMap.det| *
        μ.inChartAt x (extChartAt I x ((extChartAt I x₀).symm z)) v := by
  rw [μ.inChartAt_eq_compLinearMap hz hx, Density.compLinearMap_apply, Density.comp_apply]

/-! ### Change-of-variables invariance on chart overlaps -/

section OverlapMeasure

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M]

/-- On an overlap of two preferred charts, the set integral of a rough density's coordinate
expression against any additive Haar measure on `E` is invariant under the chart change. No
orientation or sign data are required, and boundary and corner models are included. -/
theorem setIntegral_inChartAt_changeChart (μ : RoughDensity I M k) (v : Fin k → E) (α β : M)
    {s : Set M} (hsub : s ⊆ (extChartAt I α).source ∩ (extChartAt I β).source)
    (hs : MeasurableSet ((extChartAt I α) '' s))
    (ν : Measure E) [ν.IsAddHaarMeasure] :
    (∫ y in (extChartAt I α) '' s, μ.inChartAt α y v ∂ν) =
      ∫ y in (extChartAt I β) '' s, μ.inChartAt β y v ∂ν := by
  have himage := TauCeti.extChartAt_coordChange_image α β hsub
  have hinj := TauCeti.injOn_extChartAt_coordChange α β hsub
  have hderiv := TauCeti.hasFDerivWithinAt_extChartAt_coordChange α β hsub
  rw [← himage, integral_image_eq_integral_abs_det_fderiv_smul ν hs hderiv hinj]
  refine setIntegral_congr_fun hs ?_
  rintro _ ⟨x, hx, rfl⟩
  have hβ : (extChartAt I α).symm (extChartAt I α x) ∈ (extChartAt I β).source := by
    rw [(extChartAt I α).left_inv (hsub hx).1]
    exact (hsub hx).2
  have hc := μ.inChartAt_apply_eq_abs_det_mul ((extChartAt I α).map_source (hsub hx).1) hβ v
  rw [(extChartAt I α).left_inv (hsub hx).1] at hc
  simpa only [PartialEquiv.trans_apply, (extChartAt I α).left_inv (hsub hx).1, smul_eq_mul]
    using hc

/-- Set integrability of a rough density's coordinate expression against any additive Haar measure
is invariant under a chart change on overlaps. -/
theorem integrableOn_inChartAt_changeChart (μ : RoughDensity I M k) (v : Fin k → E) (α β : M)
    {s : Set M} (hsub : s ⊆ (extChartAt I α).source ∩ (extChartAt I β).source)
    (hs : MeasurableSet ((extChartAt I α) '' s))
    (ν : Measure E) [ν.IsAddHaarMeasure] :
    IntegrableOn (fun y ↦ μ.inChartAt α y v) ((extChartAt I α) '' s) ν ↔
      IntegrableOn (fun y ↦ μ.inChartAt β y v) ((extChartAt I β) '' s) ν := by
  have himage := TauCeti.extChartAt_coordChange_image α β hsub
  have hinj := TauCeti.injOn_extChartAt_coordChange α β hsub
  have hderiv := TauCeti.hasFDerivWithinAt_extChartAt_coordChange α β hsub
  rw [← himage, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul ν hs hderiv hinj]
  refine (integrableOn_congr_fun ?_ hs).symm
  rintro _ ⟨x, hx, rfl⟩
  have hβ : (extChartAt I α).symm (extChartAt I α x) ∈ (extChartAt I β).source := by
    rw [(extChartAt I α).left_inv (hsub hx).1]
    exact (hsub hx).2
  have hc := μ.inChartAt_apply_eq_abs_det_mul ((extChartAt I α).map_source (hsub hx).1) hβ v
  rw [(extChartAt I α).left_inv (hsub hx).1] at hc
  simpa only [PartialEquiv.trans_apply, (extChartAt I α).left_inv (hsub hx).1, smul_eq_mul]
    using hc.symm

end OverlapMeasure

end RoughDensity

namespace RoughForm

section Support

variable [FiniteDimensional ℝ E] [IsManifold I 1 M]

/-- Passing from a top form to its density on an oriented manifold preserves the topological
support. -/
@[simp]
theorem tsupport_toDensity (φ : RoughForm I M ℝ k) (o : Manifold.Orientation I M (Fin k)) :
    _root_.tsupport (α := Density E k) (φ.toDensity o) =
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ := by
  simp only [_root_.tsupport]
  congr 1
  ext x
  rw [RoughDensity.mem_support_iff, RoughForm.mem_support_iff, not_iff_not,
    RoughForm.toDensity_apply_eq_zero_iff]

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
/-- Passing from a top form to its orientation-free absolute density preserves the topological
support. -/
@[simp]
theorem tsupport_absDensity [Fact (Module.finrank ℝ E = k)] (φ : RoughForm I M ℝ k) :
    _root_.tsupport (α := Density E k) φ.absDensity =
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ := by
  simp only [_root_.tsupport]
  congr 1
  ext x
  rw [RoughDensity.mem_support_iff, RoughForm.mem_support_iff, not_iff_not,
    RoughForm.absDensity_apply_eq_zero_iff]

/-- In any preferred chart of an orientation lift, evaluating the coordinate expression of
`φ.toDensity (Manifold.Orientation.mk l)` on a model basis `b` agrees on the chart target with the
signed chart coefficient of `φ` weighted by `Orientation.signBasis l.modelOrientation b`. -/
theorem toDensity_inChartAt_apply (l : Manifold.OrientationLift I M (Fin k))
    (φ : RoughForm I M ℝ k) (b : Module.Basis (Fin k) ℝ E) (α : M) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    ((φ.toDensity (Manifold.Orientation.mk l)).inChartAt α y) b =
      (Orientation.signBasis l.modelOrientation b : ℝ) *
        φ.signedInChartAt b α (fun z ↦ l.signAt α z) y := by
  let x := (extChartAt I α).symm y
  have hx : x ∈ (extChartAt I α).source := (extChartAt I α).map_target hy
  rw [← (extChartAt I α).right_inv hy]
  have hα : x ∈ (chartAt H α).source := by rwa [extChartAt_source] at hx
  have hxx : x ∈ (chartAt H x).source := mem_chart_source H x
  let D := fderivWithin ℝ (extChartAt I x ∘ (extChartAt I α).symm) (range I) (extChartAt I α x)
  have hd : ((φ.toDensity (Manifold.Orientation.mk l)).inChartAt α (extChartAt I α x)) b =
      |D.toLinearMap.det| * (φ.toDensity (Manifold.Orientation.mk l) x) b := by
    have h1 := (φ.toDensity (Manifold.Orientation.mk l)).inChartAt_apply_eq_abs_det_mul
      ((extChartAt I α).map_source hx)
      (x := x) (by rw [(extChartAt I α).left_inv hx]; exact mem_extChartAt_source x) b
    rwa [(extChartAt I α).left_inv hx, RoughDensity.inChartAt_extChartAt_self] at h1
  have hform : φ.inChartAt α (extChartAt I α x) b = D.toLinearMap.det * φ x b := by
    have h2 := φ.inChartAt_apply_basis_eq_det_mul b ((extChartAt I α).map_source hx)
      (x := x) (by rw [(extChartAt I α).left_inv hx]; exact mem_extChartAt_source x)
    rw [(extChartAt I α).left_inv hx,
      RoughForm.inChartAt_chart_apply φ x (mem_extChartAt_source x)] at h2
    simpa only [tangentCoordChange_self (mem_extChartAt_source x)] using h2
  have hval : (φ.toDensity (Manifold.Orientation.mk l) x) b =
      ((Orientation.signBasis l.modelOrientation b : ℝ) * (l.signAt x x : ℝ)) * φ x b := by
    -- `b` is a basis of `TangentSpace I x = E`, matching `l.signBasis_orientationAt`.
    have hb := φ.toDensity_apply_basis (Manifold.Orientation.mk l) x b
    rwa [Manifold.Orientation.orientationAt_mk, l.signBasis_orientationAt b x,
      Units.val_mul, Int.cast_mul] at hb
  have hsign := l.sign_mul_det α x x hα hxx
  rw [← l.signAt_of_mem hα, ← l.signAt_of_mem hxx] at hsign
  rw [hd, hval, RoughForm.signedInChartAt_apply_of_mem_source _ _ _ _ hx, hform]
  dsimp only
  calc
    |D.toLinearMap.det| *
        ((Orientation.signBasis l.modelOrientation b : ℝ) * (l.signAt x x : ℝ) * φ x b) =
      (Orientation.signBasis l.modelOrientation b : ℝ) *
        (|D.toLinearMap.det| * (l.signAt x x : ℝ)) * φ x b := by ring
    _ = (Orientation.signBasis l.modelOrientation b : ℝ) *
        ((l.signAt α x : ℝ) * D.toLinearMap.det) * φ x b := by rw [← hsign]
    _ = (Orientation.signBasis l.modelOrientation b : ℝ) *
        ((l.signAt α x : ℝ) * (D.toLinearMap.det * φ x b)) := by ring

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
/-- In any preferred chart, evaluating the coordinate expression of `φ.absDensity` on a basis `b`
gives the absolute value of the unsigned chart coefficient of `φ` on the chart target. -/
theorem absDensity_inChartAt_apply [Fact (Module.finrank ℝ E = k)] (φ : RoughForm I M ℝ k)
    (b : Module.Basis (Fin k) ℝ E) (α : M) {y : E} (hy : y ∈ (extChartAt I α).target) :
    (φ.absDensity.inChartAt α y) b = |φ.signedInChartAt b α (fun _ ↦ 1) y| := by
  rw [RoughDensity.inChartAt_apply, RoughForm.absDensity_apply,
    RoughForm.signedInChartAt_apply, dite_eq_left hy, Units.val_one, Int.cast_one, one_mul,
    RoughForm.inChartAt_apply]

end Support

end RoughForm

end TauCeti
