/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Integral curves in coordinates

This file records the correspondence between an integral curve and the solution of the
coordinate equation it becomes when read in one fixed extended chart, in both directions, and the
uniqueness statement that comes with it: two integral curves on an open interval which agree once
agree throughout, as soon as one of them stays in a fixed chart over which the coordinate field is
continuously differentiable. It also identifies the constant integral curves with the zeros of
the field.

## Main results

* `IsMIntegralCurveOn.map_of_mfderiv_eq`: a map differentiable along an integral curve whose
  derivative intertwines the vector fields there sends it to an integral curve of the second field.
* `IsMIntegralCurveAt.map_of_mfderiv_eq`: the corresponding result for local integral curves.
* `IsMIntegralCurveOn.congr`: being an integral curve on a set only depends on the values of the
  curve on that set.
* `isMIntegralCurve_const_iff`: a constant curve is an integral curve exactly at a zero of the
  field.
* `TauCeti.isMIntegralCurve_congr_vectorField`: being an integral curve only depends on the values
  of the vector field along the curve.
* `IsMIntegralCurveAt.of_extChartAt_symm`: a coordinate solution gives a manifold integral curve.
  Conversely, `HasMFDerivAt.hasDerivAt_extChartAt_comp` shows that a curve read in a fixed
  extended chart has the coordinate expression of its velocity as velocity, so an integral curve
  solves the coordinate equation there.
* `IsMIntegralCurveOn.eqOn_of_contDiffOn_extChartAt`: uniqueness of integral curves on an open
  interval, with the field regular in one fixed chart only.

## References

* Mathlib's proof of `exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless`, whose extended-chart
  calculation is adapted by `IsMIntegralCurveAt.of_extChartAt_symm` in the reverse direction.
* Mathlib's `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff`, whose connectedness argument is followed by
  `IsMIntegralCurveOn.eqOn_of_contDiffOn_extChartAt`.
* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The exponential map", and Layer 1, "The group adjoint".
-/

public section

open Bundle Function Manifold Set
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

namespace IsMIntegralCurveOn

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/-- A map differentiable along an integral curve whose derivative intertwines the vector fields
there sends it to an integral curve of the second field. -/
theorem map_of_mfderiv_eq {f : M → M'} {V : (x : M) → TangentSpace I x}
    {W : (x : M') → TangentSpace I' x} {γ : ℝ → M} {s : Set ℝ}
    (hf : ∀ t ∈ s, MDifferentiableAt I I' f (γ t))
    (hVW : ∀ t ∈ s, mfderiv I I' f (γ t) (V (γ t)) = W (f (γ t)))
    (hγ : IsMIntegralCurveOn γ V s) : IsMIntegralCurveOn (f ∘ γ) W s := by
  intro t ht
  have hder :
      (mfderiv I I' f (γ t)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight (V (γ t))) =
        (1 : ℝ →L[ℝ] ℝ).smulRight (W (f (γ t))) := by
    rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
      ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
      ContinuousLinearMap.comp_toSpanSingleton, hVW t ht]
  -- Unfold composition at the base point so the dependent target tangent spaces are definitionally
  -- identical; no rewrite lemma expresses this type-level conversion.
  change HasMFDerivAt[s] (f ∘ γ) t
    ((1 : ℝ →L[ℝ] ℝ).smulRight (W (f (γ t))))
  rw [← hder]
  exact (hf t ht).hasMFDerivAt.comp_hasMFDerivWithinAt t (hγ t ht)

/-- **Being an integral curve on a set is a property of the values on that set.** The values of a
curve outside its parameter set are junk, so a curve agreeing with an integral curve on the set is
again an integral curve there. -/
theorem congr {V : (x : M) → TangentSpace I x} {γ γ' : ℝ → M} {s : Set ℝ}
    (hγ : IsMIntegralCurveOn γ V s) (h : Set.EqOn γ' γ s) : IsMIntegralCurveOn γ' V s := by
  intro t ht
  apply ((hγ t ht).congr_mono h (h ht) Set.Subset.rfl).congr_mfderiv
  -- Normalize the common base point so the dependent tangent spaces and their cast coincide.
  rw [h ht]
  rfl

end IsMIntegralCurveOn

/-- **Constant integral curves are the zeros of the field.** The constant curve at `x` is an
integral curve of `v` exactly when `v x = 0`. -/
@[simp]
theorem isMIntegralCurve_const_iff {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {v : (x : M) → TangentSpace I x} {x : M} :
    IsMIntegralCurve (fun _ ↦ x) v ↔ v x = 0 := by
  refine ⟨fun h ↦ ?_, isMIntegralCurve_const⟩
  -- The derivative of the constant curve is `0`, and evaluating `1 ↦ v x` at `1` gives `v x`.
  have h₀ := (h 0).mfderiv
  rw [mfderiv_const] at h₀
  have h₁ : v x = ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (v x) 1 := by simp
  exact h₁.trans (ContinuousLinearMap.ext_iff.1 h₀ (1 : ℝ)).symm

namespace IsMIntegralCurveAt

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/-- A map eventually differentiable along a local integral curve whose derivative eventually
intertwines the vector fields sends it to a local integral curve of the second field. -/
theorem map_of_mfderiv_eq {f : M → M'} {V : (x : M) → TangentSpace I x}
    {W : (x : M') → TangentSpace I' x} {γ : ℝ → M} {t₀ : ℝ}
    (hf : ∀ᶠ t in 𝓝 t₀, MDifferentiableAt I I' f (γ t))
    (hVW : ∀ᶠ t in 𝓝 t₀, mfderiv I I' f (γ t) (V (γ t)) = W (f (γ t)))
    (hγ : IsMIntegralCurveAt γ V t₀) : IsMIntegralCurveAt (f ∘ γ) W t₀ := by
  rw [isMIntegralCurveAt_iff] at hγ ⊢
  obtain ⟨s, hs, hγs⟩ := hγ
  rw [Filter.eventually_iff_exists_mem] at hf hVW
  obtain ⟨sf, hsf, hf⟩ := hf
  obtain ⟨sVW, hsVW, hVW⟩ := hVW
  refine ⟨s ∩ sf ∩ sVW, Filter.inter_mem (Filter.inter_mem hs hsf) hsVW, ?_⟩
  exact (hγs.mono (Set.inter_subset_left.trans Set.inter_subset_left)).map_of_mfderiv_eq
    (fun t ht ↦ hf t ht.1.2) (fun t ht ↦ hVW t ht.2)

end IsMIntegralCurveAt

namespace TauCeti

/-- **Being an integral curve only depends on the vector field along the curve.** If two vector
fields agree at every point of a curve, it is an integral curve of one exactly when it is an
integral curve of the other. -/
theorem isMIntegralCurve_congr_vectorField {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {γ : ℝ → M} {v w : (x : M) → TangentSpace I x} (hvw : ∀ t, v (γ t) = w (γ t)) :
    IsMIntegralCurve γ v ↔ IsMIntegralCurve γ w :=
  ⟨fun hγ t ↦ hvw t ▸ hγ t, fun hγ t ↦ (hvw t).symm ▸ hγ t⟩

end TauCeti

/-- Convert an ordinary derivative into the model-space derivative expected inside a manifold
derivative. This is the single boundary where the tangent spaces of the self model on `ℝ` and of
`I` are identified with their model vector spaces `ℝ` and `E`. -/
private theorem hasFDerivWithinAt_model_tangent_spaces
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {x : M} {φ : ℝ → E} {t : ℝ} {v : TangentSpace I x}
    (hφ : HasDerivAt φ v t) :
    HasFDerivWithinAt φ
      (ContinuousLinearMap.toSpanSingleton ℝ v :
        TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace I x)
      Set.univ t := by
  change HasFDerivWithinAt φ (ContinuousLinearMap.toSpanSingleton ℝ v) Set.univ t
  exact hφ.hasFDerivAt.hasFDerivWithinAt

/-- A coordinate curve whose values stay in an extended-chart target and whose derivative is the
coordinate expression of a vector field gives a manifold integral curve after applying the inverse
chart. -/
theorem IsMIntegralCurveAt.of_extChartAt_symm
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {x₀ : M} {f : ℝ → E} {t₀ : ℝ} {v : (x : M) → TangentSpace I x}
    (htarget : ∀ᶠ t in nhds t₀, f t ∈ interior (extChartAt I x₀).target)
    (hderiv : ∀ᶠ t in nhds t₀,
      HasDerivAt f
        (tangentCoordChange I ((extChartAt I x₀).symm (f t)) x₀
          ((extChartAt I x₀).symm (f t)) (v ((extChartAt I x₀).symm (f t)))) t) :
    IsMIntegralCurveAt ((extChartAt I x₀).symm ∘ f) v t₀ := by
  obtain ⟨s, hs, haux⟩ := (hderiv.and htarget).exists_mem
  rw [isMIntegralCurveAt_iff]
  refine ⟨s, hs, ?_⟩
  intro t ht
  let xₜ : M := (extChartAt I x₀).symm (f t)
  have h : HasDerivAt f
      (tangentCoordChange I xₜ x₀ xₜ (v xₜ)) t := (haux t ht).1
  have hf3 := mem_of_mem_of_subset (haux t ht).2 interior_subset
  have hft1 := mem_preimage.mp <|
    mem_of_mem_of_subset hf3 (extChartAt I x₀).target_subset_preimage_source
  have hft2 := mem_extChartAt_source (I := I) xₜ
  have hft1' : xₜ ∈ (extChartAt I x₀).source := by simpa only [xₜ] using hft1
  have hcharts :
      xₜ ∈ (extChartAt I xₜ).source ∩ (extChartAt I x₀).source ∩
        (extChartAt I xₜ).source := ⟨⟨hft2, hft1'⟩, hft2⟩
  apply HasMFDerivAt.hasMFDerivWithinAt
  refine ⟨(continuousAt_extChartAt_symm'' hf3).comp h.continuousAt, ?_⟩
  have hcomp : HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘ f)
      (tangentCoordChange I x₀ xₜ xₜ (tangentCoordChange I xₜ x₀ xₜ (v xₜ))) t := by
    apply HasFDerivAt.comp_hasDerivAt _ _ h
    apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ <|
      mem_nhds_iff.mpr ⟨interior (extChartAt I x₀).target,
        subset_trans interior_subset (extChartAt_target_subset_range ..),
        isOpen_interior, (haux t ht).2⟩
    rw [← (extChartAt I x₀).right_inv hf3]
    exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩
  have hd := hcomp.congr_deriv (tangentCoordChange_comp hcharts)
  have hd' := hd.congr_deriv (tangentCoordChange_self hft2)
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    PartialEquiv.refl_symm, modelWithCornersSelf_coe, Function.comp_def, id_eq, range_id]
  -- Restore the named chart preimage before comparing the ordinary and manifold derivatives.
  rw [show (extChartAt I x₀).symm (f t) = xₜ from rfl]
  rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
  exact hasFDerivWithinAt_model_tangent_spaces hd'

/-- **Local step of fixed-chart uniqueness.** Near a time of `Ioo a b` where two integral curves
agree, they agree, provided one of them stays in a fixed extended chart, over an open set on which
the coordinate expression of the field is continuously differentiable: both are then solutions of
the same locally Lipschitz coordinate equation with the same initial value. -/
private theorem IsMIntegralCurveOn.eventuallyEq_of_contDiffOn_extChartAt
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {v : (x : M) → TangentSpace I x} {x₀ : M} {a b t : ℝ} {γ δ : ℝ → M} {u : Set E}
    (hu : IsOpen u)
    (hv : ContDiffOn ℝ 1 (fun z ↦ tangentCoordChange I ((extChartAt I x₀).symm z) x₀
      ((extChartAt I x₀).symm z) (v ((extChartAt I x₀).symm z))) u)
    (hγ : IsMIntegralCurveOn γ v (Ioo a b)) (hδ : IsMIntegralCurveOn δ v (Ioo a b))
    (hγsrc : ∀ t ∈ Ioo a b, γ t ∈ (extChartAt I x₀).source)
    (hγu : ∀ t ∈ Ioo a b, extChartAt I x₀ (γ t) ∈ u)
    (htmem : t ∈ Ioo a b) (hteq : γ t = δ t) : ∀ᶠ r in 𝓝 t, γ r = δ r := by
  let φ := extChartAt I x₀
  let w : E → E := fun z ↦
    tangentCoordChange I (φ.symm z) x₀ (φ.symm z) (v (φ.symm z))
  have hJ : Ioo a b ∈ 𝓝 t := Ioo_mem_nhds htmem.1 htmem.2
  have hγat := hγ.isMIntegralCurveAt hJ
  have hδat := hδ.isMIntegralCurveAt hJ
  have hγst := hγsrc t htmem
  have hδst : δ t ∈ φ.source := hteq ▸ hγst
  have hγut := hγu t htmem
  have hvat : ContDiffAt ℝ 1 w (φ (γ t)) :=
    (hv (φ (γ t)) hγut).contDiffAt (hu.mem_nhds hγut)
  obtain ⟨K, z, hz, hlip⟩ : ∃ K, ∃ z ∈ 𝓝 (φ (γ t)), LipschitzOnWith K w z :=
    hvat.exists_lipschitzOnWith
  have hγz : ∀ᶠ r in 𝓝 t, φ (γ r) ∈ z :=
    ((continuousAt_extChartAt' hγst).comp hγat.continuousAt).eventually hz
  have hδz : ∀ᶠ r in 𝓝 t, φ (δ r) ∈ z :=
    ((continuousAt_extChartAt' hδst).comp hδat.continuousAt).eventually (by
      rw [Function.comp_apply]
      rw [← hteq]
      exact hz)
  have hδsrc : ∀ᶠ r in 𝓝 t, δ r ∈ φ.source :=
    hδat.continuousAt.eventually_mem ((isOpen_extChartAt_source x₀).mem_nhds hδst)
  have hγderiv : ∀ᶠ r in 𝓝 t, HasDerivAt (φ ∘ γ) (w ((φ ∘ γ) r)) r := by
    filter_upwards [hJ] with r hr
    have hd := ((hγ r hr).hasMFDerivAt (Ioo_mem_nhds hr.1 hr.2)).hasDerivAt_extChartAt_comp
      (hγsrc r hr)
    convert hd using 1
    simp only [w, Function.comp_apply]
    rw [φ.left_inv (hγsrc r hr)]
  have hδderiv : ∀ᶠ r in 𝓝 t, HasDerivAt (φ ∘ δ) (w ((φ ∘ δ) r)) r := by
    filter_upwards [hJ, hδsrc] with r hr hrsrc
    have hd := ((hδ r hr).hasMFDerivAt (Ioo_mem_nhds hr.1 hr.2)).hasDerivAt_extChartAt_comp hrsrc
    convert hd using 1
    simp only [w, Function.comp_apply]
    rw [φ.left_inv hrsrc]
  have hcoord : (φ ∘ γ) =ᶠ[𝓝 t] (φ ∘ δ) :=
    ODE_solution_unique_of_eventually (.of_forall fun _ ↦ hlip)
      (hγderiv.and hγz) (hδderiv.and hδz) (congrArg φ hteq)
  filter_upwards [hcoord, hJ, hδsrc] with r hr hrJ hrδsrc
  exact φ.injOn (hγsrc r hrJ) hrδsrc hr

/-- A curve in the model space which stays in the interior of the chart target and solves the
coordinate equation of a vector field on an open set of times gives an integral curve of the
field on the manifold, after applying the inverse extended chart. -/
theorem isMIntegralCurveOn_extChartAt_symm_comp {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (v : (x : M) → TangentSpace I x) (a : M) {f : ℝ → E}
    {s : Set ℝ} (hs : IsOpen s)
    (hmem : ∀ t ∈ s, f t ∈ interior (extChartAt I a).target)
    (hderiv : ∀ t ∈ s, HasDerivAt f (trivializationAt E (TangentSpace I) a
      (⟨(extChartAt I a).symm (f t), v ((extChartAt I a).symm (f t))⟩ :
        TangentBundle I M)).2 t) :
    IsMIntegralCurveOn ((extChartAt I a).symm ∘ f) v s := by
  refine IsMIntegralCurveAt.isMIntegralCurveOn fun t ht ↦ ?_
  apply IsMIntegralCurveAt.of_extChartAt_symm
  · filter_upwards [hs.mem_nhds ht] with r hr
    exact hmem r hr
  · filter_upwards [hs.mem_nhds ht] with r hr
    have hw_eq (z : E) : (trivializationAt E (TangentSpace I) a
        (⟨(extChartAt I a).symm z, v ((extChartAt I a).symm z)⟩ : TangentBundle I M)).2 =
        tangentCoordChange I ((extChartAt I a).symm z) a ((extChartAt I a).symm z)
          (v ((extChartAt I a).symm z)) := by
      -- The fibre coordinate of the preferred trivialization is the second coordinate of the
      -- tangent-bundle chart, whose conversion to `tangentCoordChange` is recorded explicitly.
      change (chartAt (ModelProd H E)
        (⟨a, 0⟩ : TangentBundle I M)
        (⟨(extChartAt I a).symm z, v ((extChartAt I a).symm z)⟩ :
          TangentBundle I M)).2 = _
      exact TangentBundle.coe_chartAt_snd
    simpa only [hw_eq] using hderiv r hr

/-- **Fixed-chart uniqueness of integral curves.** Two integral curves on an open interval which
take the same value at one time of that interval agree on it, as soon as one of them stays in a
fixed extended chart, over an open set on which the coordinate expression of the field is
continuously differentiable. Unlike `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff`, the field has to
be regular only in that one chart, not in the chart at each point of the curve. -/
theorem IsMIntegralCurveOn.eqOn_of_contDiffOn_extChartAt
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [T2Space M]
    {v : (x : M) → TangentSpace I x} {x₀ : M} {a b t₀ : ℝ} {γ δ : ℝ → M} {u : Set E}
    (hu : IsOpen u)
    (hv : ContDiffOn ℝ 1 (fun z ↦ tangentCoordChange I ((extChartAt I x₀).symm z) x₀
      ((extChartAt I x₀).symm z) (v ((extChartAt I x₀).symm z))) u)
    (hγ : IsMIntegralCurveOn γ v (Ioo a b)) (hδ : IsMIntegralCurveOn δ v (Ioo a b))
    (hγsrc : ∀ t ∈ Ioo a b, γ t ∈ (extChartAt I x₀).source)
    (hγu : ∀ t ∈ Ioo a b, extChartAt I x₀ (γ t) ∈ u)
    (ht₀ : t₀ ∈ Ioo a b) (heq : γ t₀ = δ t₀) : EqOn γ δ (Ioo a b) := by
  -- The times of `Ioo a b` where the curves agree form a nonempty subset which is both open and
  -- relatively closed there, so connectedness of the interval makes it everything.
  set q := {t | γ t = δ t} ∩ Ioo a b
  suffices hsub : Ioo a b ⊆ q from fun t ht ↦ mem_ofPred.mp ((subset_def ▸ hsub) t ht).1
  apply isPreconnected_Ioo.subset_of_closure_inter_subset (s := Ioo a b) (u := q) _
    ⟨t₀, ⟨ht₀, ⟨heq, ht₀⟩⟩⟩
  · -- Relative closedness: both curves are continuous at a time of the interval, and one of them
    -- tends to the value of the other along the times where they agree.
    rintro t ⟨htc, htJ⟩
    have hJ : Ioo a b ∈ 𝓝 t := Ioo_mem_nhds htJ.1 htJ.2
    have hγt : Filter.Tendsto γ (𝓝[q] t) (𝓝 (γ t)) :=
      ((hγ.continuousWithinAt htJ).continuousAt hJ).continuousWithinAt
    have hδt : Filter.Tendsto δ (𝓝[q] t) (𝓝 (δ t)) :=
      ((hδ.continuousWithinAt htJ).continuousAt hJ).continuousWithinAt
    have hδγ : δ =ᶠ[𝓝[q] t] γ := by
      filter_upwards [self_mem_nhdsWithin] with r hr using (mem_ofPred.mp hr.1).symm
    exact ⟨tendsto_nhds_unique' (mem_closure_iff_nhdsWithin_neBot.mp htc) hγt (hδt.congr' hδγ),
      htJ⟩
  · -- Openness: near a time where the curves agree, both are solutions of the same locally
    -- Lipschitz coordinate equation with the same value, so they agree there too.
    rw [isOpen_iff_mem_nhds]
    intro t ht
    exact ((eventuallyEq_of_contDiffOn_extChartAt hu hv hγ hδ hγsrc hγu ht.2 ht.1).and
      (Ioo_mem_nhds ht.2.1 ht.2.2)).mono fun _ hr ↦ ⟨hr.1, hr.2⟩
