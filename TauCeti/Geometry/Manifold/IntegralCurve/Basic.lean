/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.ODE.ExistUnique
import TauCeti.Analysis.ODE.Regularity
import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Regularity of integral curves

An integral curve gains one derivative over its vector field. In particular, integral curves of
smooth vector fields on boundaryless smooth manifolds are smooth.

This file also records the correspondence between an integral curve and the solution of the
coordinate equation it becomes when read in one fixed extended chart, in both directions, and the
uniqueness statement that comes with it: two integral curves on an open interval which agree once
agree throughout, as soon as one of them stays in a fixed chart over which the coordinate field is
continuously differentiable.

## Main results

* `IsMIntegralCurveOn.map_of_mfderiv_eq`: a map differentiable along an integral curve whose
  derivative intertwines the vector fields there sends it to an integral curve of the second field.
* `IsMIntegralCurveAt.map_of_mfderiv_eq`: the corresponding result for local integral curves.
* `IsMIntegralCurveOn.congr`: being an integral curve on a set only depends on the values of the
  curve on that set.
* `IsMIntegralCurve.contMDiff_succ`: an integral curve of a `C^n` vector field is `C^(n + 1)`.
* `IsMIntegralCurve.contMDiff`: an integral curve of a smooth vector field is smooth.
* `IsMIntegralCurveAt.of_extChartAt_symm`: a coordinate solution gives a manifold integral curve.
* `IsMIntegralCurveOn.hasDerivAt_extChartAt`: conversely, an integral curve read in a fixed
  extended chart solves the coordinate equation there.
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
  exact (hγs.mono fun _ ht ↦ ht.1.1).map_of_mfderiv_eq
    (fun t ht ↦ hf t ht.1.2) (fun t ht ↦ hVW t ht.2)

end IsMIntegralCurveAt

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

/-- An integral curve, read in any fixed extended chart containing its value, solves the
corresponding coordinate ODE. This is the converse direction of
`IsMIntegralCurveAt.of_extChartAt_symm`. -/
theorem IsMIntegralCurveOn.hasDerivAt_extChartAt
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {v : (x : M) → TangentSpace I x} {γ : ℝ → M} {s : Set ℝ} {x : M} {t : ℝ}
    (hγ : IsMIntegralCurveOn γ v s) (ht : t ∈ s) (hs : s ∈ 𝓝 t)
    (hsrc : γ t ∈ (extChartAt I x).source) :
    HasDerivAt ((extChartAt I x) ∘ γ)
      (tangentCoordChange I (γ t) x (γ t) (v (γ t))) t := by
  replace hsrc := extChartAt_source I x ▸ hsrc
  have hderiv := TauCeti.Manifold.hasDerivAt_comp_curve
    (mdifferentiableAt_extChartAt (I := I) hsrc) ((hγ t ht).hasMFDerivAt hs)
  convert hderiv using 1
  simp only [mvfderiv]
  rw [(hasMFDerivAt_extChartAt (I := I) hsrc).mfderiv,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  rfl

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
  let φ := extChartAt I x₀
  let w : E → E := fun z ↦
    tangentCoordChange I (φ.symm z) x₀ (φ.symm z) (v (φ.symm z))
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
    have hJ : Ioo a b ∈ 𝓝 t := Ioo_mem_nhds ht.2.1 ht.2.2
    have hγat := hγ.isMIntegralCurveAt hJ
    have hδat := hδ.isMIntegralCurveAt hJ
    have hγst := hγsrc t ht.2
    have hδst : δ t ∈ φ.source := ht.1 ▸ hγst
    have hγut := hγu t ht.2
    have hvat : ContDiffAt ℝ 1 w (φ (γ t)) :=
      (hv (φ (γ t)) hγut).contDiffAt (hu.mem_nhds hγut)
    obtain ⟨K, z, hz, hlip⟩ : ∃ K, ∃ z ∈ 𝓝 (φ (γ t)), LipschitzOnWith K w z :=
      hvat.exists_lipschitzOnWith
    have hγz : ∀ᶠ r in 𝓝 t, φ (γ r) ∈ z :=
      ((continuousAt_extChartAt' hγst).comp hγat.continuousAt).eventually hz
    have hδz : ∀ᶠ r in 𝓝 t, φ (δ r) ∈ z :=
      ((continuousAt_extChartAt' hδst).comp hδat.continuousAt).eventually (by
        rw [Function.comp_apply]
        rw [← ht.1]
        exact hz)
    have hδsrc : ∀ᶠ r in 𝓝 t, δ r ∈ φ.source :=
      hδat.continuousAt.eventually_mem ((isOpen_extChartAt_source x₀).mem_nhds hδst)
    have hγderiv : ∀ᶠ r in 𝓝 t, HasDerivAt (φ ∘ γ) (w ((φ ∘ γ) r)) r := by
      filter_upwards [hJ] with r hr
      have hd := hγ.hasDerivAt_extChartAt hr (Ioo_mem_nhds hr.1 hr.2) (hγsrc r hr)
      convert hd using 1
      simp only [w, Function.comp_apply]
      rw [φ.left_inv (hγsrc r hr)]
    have hδderiv : ∀ᶠ r in 𝓝 t, HasDerivAt (φ ∘ δ) (w ((φ ∘ δ) r)) r := by
      filter_upwards [hJ, hδsrc] with r hr hrsrc
      have hd := hδ.hasDerivAt_extChartAt hr (Ioo_mem_nhds hr.1 hr.2) hrsrc
      convert hd using 1
      simp only [w, Function.comp_apply]
      rw [φ.left_inv hrsrc]
    have hcoord : (φ ∘ γ) =ᶠ[𝓝 t] (φ ∘ δ) :=
      ODE_solution_unique_of_eventually (.of_forall fun _ ↦ hlip)
        (hγderiv.and hγz) (hδderiv.and hδz) (congrArg φ ht.1)
    have hlocal : γ =ᶠ[𝓝 t] δ := by
      filter_upwards [hcoord, hJ, hδsrc] with r hr hrJ hrδsrc
      exact φ.injOn (hγsrc r hrJ) hrδsrc hr
    exact (hlocal.and hJ).mono fun _ hr ↦ ⟨hr.1, hr.2⟩

/-- A local integral curve of a `C^1` vector field on a boundaryless manifold is `C^2` at its
initial parameter. -/
theorem IsMIntegralCurveAt.contMDiffAt_two
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [BoundarylessManifold I M] [IsManifold I 2 M]
    {γ : ℝ → M} {v : (x : M) → TangentSpace I x} {t₀ : ℝ}
    (hγ : IsMIntegralCurveAt γ v t₀)
    (hv : ContMDiffAt I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)) (γ t₀)) :
    ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t₀ := by
  rw [contMDiffAt_iff_target]
  refine ⟨hγ.continuousAt, ?_⟩
  let c : ℝ → E := (extChartAt I (γ t₀)) ∘ γ
  let v' : E → E := fun x =>
    tangentCoordChange I ((extChartAt I (γ t₀)).symm x) (γ t₀)
      ((extChartAt I (γ t₀)).symm x) (v ((extChartAt I (γ t₀)).symm x))
  have hv' : ContDiffAt ℝ 1 v' (extChartAt I (γ t₀) (γ t₀)) := by
    have hv₀ := hv
    rw [contMDiffAt_iff] at hv₀
    exact (hv₀.2.contDiffAt
      (range_mem_nhds_isInteriorPoint BoundarylessManifold.isInteriorPoint)).snd
  obtain ⟨u, hxu, hvu⟩ := hv'.contDiffOn le_rfl (by simp)
  have hcsrc : ∀ᶠ t in 𝓝 t₀, γ t ∈ (extChartAt I (γ t₀)).source :=
    hγ.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) _)
  have hderiv : ∀ᶠ t in 𝓝 t₀, HasDerivAt c (v' (c t)) t :=
    hγ.eventually_hasDerivAt.and hcsrc |>.mono fun t ht => by
      apply ht.1.congr_deriv
      simp only [v', c, Function.comp_apply]
      rw [PartialEquiv.left_inv _ ht.2]
  have hcu : ∀ᶠ t in 𝓝 t₀, c t ∈ u :=
    ((continuousAt_extChartAt (γ t₀)).comp hγ.continuousAt).eventually hxu
  have hall : {t | HasDerivAt c (v' (c t)) t ∧ c t ∈ u} ∈ 𝓝 t₀ :=
    hderiv.and hcu
  obtain ⟨s, hsP, hsopen, hst₀⟩ := mem_nhds_iff.mp hall
  have hc : ContDiffAt ℝ 2 c t₀ :=
    (TauCeti.contDiffOn_succ_of_hasDerivAt_comp hsopen hvu (fun t ht => (hsP ht).2)
      (fun t ht => (hsP ht).1)).contDiffAt (hsopen.mem_nhds hst₀)
  have hc' : ContDiffAt ℝ 2 ((extChartAt I (γ t₀)) ∘ γ) t₀ := by
    simpa only [c] using hc
  exact hc'.contMDiffAt

namespace IsMIntegralCurve

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [BoundarylessManifold I M]

/-- An integral curve of a `C^n` vector field on a boundaryless smooth manifold is `C^(n + 1)`. -/
theorem contMDiff_succ (n : ℕ) [IsManifold I (n + 1 : ℕ) M]
    {γ : ℝ → M} {v : (x : M) → TangentSpace I x}
    (hγ : IsMIntegralCurve γ v)
    (hv : let _ : IsManifold I 1 M := IsManifold.of_le (n := (n + 1 : ℕ)) (by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n));
      CMDiff n (fun x => (⟨x, v x⟩ : TangentBundle I M))) :
    ContMDiff 𝓘(ℝ, ℝ) I (n + 1 : ℕ) γ := by
  let _ : IsManifold I 1 M := IsManifold.of_le (n := (n + 1 : ℕ)) (by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  -- The hypothesis stages this same low-order manifold instance in a dependent `let`; unfold that
  -- binder so its `TangentBundle` agrees with the explicitly installed instance above.
  change CMDiff n (fun x => (⟨x, v x⟩ : TangentBundle I M)) at hv
  intro t₀
  rw [contMDiffAt_iff_target]
  refine ⟨hγ.continuous.continuousAt, ?_⟩
  let c : ℝ → E := (extChartAt I (γ t₀)) ∘ γ
  let v' : E → E := fun x =>
    tangentCoordChange I ((extChartAt I (γ t₀)).symm x) (γ t₀)
      ((extChartAt I (γ t₀)).symm x) (v ((extChartAt I (γ t₀)).symm x))
  have hv' : ContDiffAt ℝ n v' (extChartAt I (γ t₀) (γ t₀)) := by
    have hv₀ := hv.contMDiffAt (x := γ t₀)
    rw [contMDiffAt_iff] at hv₀
    exact (hv₀.2.contDiffAt
      (range_mem_nhds_isInteriorPoint BoundarylessManifold.isInteriorPoint)).snd
  obtain ⟨u, hxu, hvu⟩ := hv'.contDiffOn le_rfl (by simp)
  have hcsrc : ∀ᶠ t in 𝓝 t₀, γ t ∈ (extChartAt I (γ t₀)).source :=
    hγ.continuous.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) _)
  have hderiv : ∀ᶠ t in 𝓝 t₀, HasDerivAt c (v' (c t)) t :=
    (hγ.isMIntegralCurveAt t₀).eventually_hasDerivAt.and hcsrc |>.mono fun t ht => by
      apply ht.1.congr_deriv
      simp only [v', c, Function.comp_apply]
      rw [PartialEquiv.left_inv _ ht.2]
  have hcu : ∀ᶠ t in 𝓝 t₀, c t ∈ u :=
    ((continuousAt_extChartAt (γ t₀)).comp hγ.continuous.continuousAt).eventually hxu
  have hall : {t | HasDerivAt c (v' (c t)) t ∧ c t ∈ u} ∈ 𝓝 t₀ :=
    hderiv.and hcu
  obtain ⟨s, hsP, hsopen, hst₀⟩ := mem_nhds_iff.mp hall
  have hc : ContDiffAt ℝ (n + 1 : ℕ) c t₀ :=
    (TauCeti.contDiffOn_succ_of_hasDerivAt_comp hsopen hvu (fun t ht => (hsP ht).2)
      (fun t ht => (hsP ht).1)).contDiffAt (hsopen.mem_nhds hst₀)
  have hc' : ContDiffAt ℝ (n + 1 : ℕ) ((extChartAt I (γ t₀)) ∘ γ) t₀ := by
    simpa only [c] using hc
  exact hc'.contMDiffAt

/-- An integral curve of an infinitely smooth vector field on a boundaryless smooth manifold is
infinitely smooth. -/
theorem contMDiff [IsManifold I ∞ M] {γ : ℝ → M} {v : (x : M) → TangentSpace I x}
    (hγ : IsMIntegralCurve γ v)
    (hv : CMDiff ∞ (fun x => (⟨x, v x⟩ : TangentBundle I M))) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := by
  rw [contMDiff_infty]
  intro n
  let _ : IsManifold I (n + 1 : ℕ) M := IsManifold.of_le (n := ∞)
    (by exact_mod_cast le_top)
  exact (hγ.contMDiff_succ n (hv.of_le (by exact_mod_cast le_top))).of_le
    (by exact_mod_cast Nat.le_succ n)

end IsMIntegralCurve
