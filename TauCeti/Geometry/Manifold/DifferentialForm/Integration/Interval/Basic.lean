/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Chart.Interior
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
public import TauCeti.Geometry.Manifold.Orientation.Interval
public import TauCeti.MeasureTheory.Measure.Haar.EuclideanSpace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Canonical oriented interval integration

Pullback along the actual inclusion of `[a,b]` gives a top form on Mathlib's interval manifold.
The left/right coordinate derivatives and chart signs compensate, and the normalized Euclidean
line measure is real Lebesgue measure. The canonical integral therefore equals `∫ t in a..b`.
-/

public section

noncomputable section

open Set MeasureTheory Fact.Manifold
open scoped Manifold

namespace TauCeti

variable {a b : ℝ} [hab : Fact (a < b)]

/-- The actual pullback coefficient of a real one-form in an interval chart is its real
coefficient multiplied by that chart's inclusion derivative. -/
theorem inChartAt_mpullback_subtypeVal_Icc
    (ω : RoughForm 𝓘(ℝ) ℝ ℝ 1) (α : Icc a b) {z : EuclideanSpace ℝ (Fin 1)}
    (hz : z ∈ (extChartAt (𝓡∂ 1) α).target) :
    (mpullback (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc a b → ℝ) ω).inChartAt α z
      (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis =
      (if (α : ℝ) < b then (1 : ℝ) else -1) *
        ω ((extChartAt (𝓡∂ 1) α).symm z : ℝ) (fun _ ↦ 1) := by
  have hf := (contMDiff_subtypeVal_Icc (x := a) (y := b) (n := 1)
    ((extChartAt (𝓡∂ 1) α).symm z)).mdifferentiableAt one_ne_zero
  rw [RoughForm.inChartAt_mpullback_modelSpace ω _ α hz hf]
  have hd := (hasFDerivWithinAt_subtypeVal_extChartAt_Icc_symm α hz).fderivWithin
    ((𝓡∂ 1).uniqueDiffOn z (extChartAt_target_subset_range α hz))
  simp only [Function.comp_def]
  rw [hd, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  let c : ℝ := if (α : ℝ) < b then 1 else -1
  have he : (fun i : Fin 1 ↦
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) ((extChartAt (𝓡∂ 1) α).symm z : ℝ)).symm
        ((c • EuclideanSpace.proj 0) ((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis i))) =
      fun _ ↦ c • (1 : TangentSpace 𝓘(ℝ) ((extChartAt (𝓡∂ 1) α).symm z : ℝ)) := by
    funext i
    rw [Subsingleton.elim i 0]
    simp only [smul_apply, smul_eq_mul,
      OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      EuclideanSpace.coe_proj, PiLp.single_apply, ite_eq_left, mul_one]
    have hmap := (NormedSpace.fromTangentSpace (𝕜 := ℝ)
      ((extChartAt (𝓡∂ 1) α).symm z : ℝ)).symm.map_smul c (1 : ℝ)
    simp only [smul_eq_mul, mul_one] at hmap
    exact hmap.trans (congrArg (fun v ↦ c • v)
      (NormedSpace.fromTangentSpace_symm_apply _ (1 : ℝ)))
  -- Expose the signed projection and the coefficient c so the transported tuple he rewrites it.
  change ω _ (fun i ↦
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) ((extChartAt (𝓡∂ 1) α).symm z : ℝ)).symm
      ((c • EuclideanSpace.proj 0) ((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis i))) =
    c * ω _ (fun _ ↦ 1)
  rw [he]
  simpa only [Fin.prod_univ_one, smul_eq_mul] using
    (ω ((extChartAt (𝓡∂ 1) α).symm z : ℝ)).map_smul_univ (fun _ ↦ c) (fun _ ↦ 1)

private theorem integrable_interval_pullback_coefficient
    (ω : RoughForm 𝓘(ℝ) ℝ ℝ 1)
    (hf : IntervalIntegrable (fun t ↦ ω t (fun _ ↦ 1)) volume a b) (α : Icc a b) :
    Integrable ((mpullback (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc a b → ℝ) ω).signedInChartAt
      (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis α (fun _ ↦ 1))
      (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.addHaar := by
  let φ := mpullback (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc a b → ℝ) ω
  let f : ℝ → ℝ := fun t ↦ ω t (fun _ ↦ 1)
  let π := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0
  let g : ℝ → ℝ := fun t ↦ if (α : ℝ) < b then f (t + a) else f (b - t)
  have hg : IntervalIntegrable g volume 0 (b - a) := by
    by_cases hα : (α : ℝ) < b
    · simpa only [g, ite_eq_left hα, sub_self] using hf.comp_add_right a
    · simpa only [g, ite_eq_right hα, sub_self] using (hf.comp_sub_left b).symm
  have hI : IntegrableOn g (Ico 0 (b - a)) :=
    (intervalIntegrable_iff_integrableOn_Ico_of_le (sub_nonneg.mpr hab.out.le)).mp hg
  have hπ := (TauCeti.volume_preserving_euclideanSpace_proj (ι := Fin 1) 0).restrict_preimage_emb
    (TauCeti.measurableEmbedding_euclideanSpace_proj (ι := Fin 1) 0) (Ico 0 (b - a))
  have hc : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 1) ↦
      (if (α : ℝ) < b then (1 : ℝ) else -1) * g (π z))
      (extChartAt (𝓡∂ 1) α).target := by
    rw [extChartAt_Icc_target]
    exact (hπ.integrable_comp_of_integrable hI).const_mul _
  apply (integrableOn_iff_integrable_of_support_subset
    (φ.support_signedInChartAt_subset_target _ α (fun _ ↦ 1))).mp
  rw [(EuclideanSpace.basisFun (Fin 1) ℝ).addHaar_eq_volume]
  apply hc.congr_fun _ (measurableSet_extChartAt_target α)
  intro z hz
  rw [RoughForm.signedInChartAt_apply, dite_eq_left hz]
  simp only [Units.val_one, Int.cast_one, one_mul]
  rw [inChartAt_mpullback_subtypeVal_Icc ω α hz]
  -- Expand only the local coefficient abbreviations; keep the chart inverse for its equation.
  change (if (α : ℝ) < b then (1 : ℝ) else -1) * g (π z) =
    (if (α : ℝ) < b then (1 : ℝ) else -1) * f ((extChartAt (𝓡∂ 1) α).symm z : ℝ)
  rw [subtypeVal_extChartAt_Icc_symm α hz]
  by_cases hα : (α : ℝ) < b <;> simp only [g, hα, ↓reduceIte]
  <;> rfl

/-- Actual pullback of an interval-integrable real one-form is intrinsically integrable,
and its canonical increasing-orientation integral is the ordinary interval integral. -/
theorem integralTopForm_mpullback_subtypeVal_Icc
    (ω : RoughForm 𝓘(ℝ) ℝ ℝ 1)
    (hf : IntervalIntegrable (fun t ↦ ω t (fun _ ↦ 1)) volume a b) :
    IntegrableTopForm (mpullback (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc a b → ℝ) ω) ∧
      integralTopForm (Manifold.Orientation.interval a b)
        (mpullback (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc a b → ℝ) ω) =
        ∫ t in a..b, ω t (fun _ ↦ 1) := by
  let φ := mpullback (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc a b → ℝ) ω
  let B := (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis
  let l := Manifold.OrientationLift.interval a b
  let α : Icc a b := ⊥
  let f : ℝ → ℝ := fun t ↦ ω t (fun _ ↦ 1)
  have hi : IntegrableTopForm φ := by
    rw [integrableTopForm_iff]
    refine ⟨isCompact_univ.of_isClosed_subset
      (_root_.isClosed_tsupport
        (α := (EuclideanSpace ℝ (Fin 1)) [⋀^Fin 1]→L[ℝ] ℝ) φ) (subset_univ _), ⟨B⟩, ?_⟩
    intro b' β
    exact (φ.integrable_signedInChartAt_basis_iff B b' β (fun _ ↦ 1)).mpr
      (integrable_interval_pullback_coefficient ω hf β)
  refine ⟨hi, ?_⟩
  rw [Manifold.Orientation.interval_eq_mk,
    integralTopForm_eq_chartIntegral_of_interior_subset l φ hi α
      interior_Icc_subset_extChartAt_bot_source, l.chartIntegral_eq_integral φ B α]
  have hs : (fun x : (extChartAt (𝓡∂ 1) α).source ↦ l.signAt α x) = fun _ ↦ (1 : ℤˣ) := by
    funext x
    rw [Manifold.OrientationLift.signAt_of_mem _ (by
      simpa only [extChartAt_source] using x.property), Manifold.OrientationLift.interval_sign]
    simp only [α, Icc.coe_bot, hab.out, ↓reduceIte]
  rw [hs]
  have hb : _root_.Orientation.signBasis l.modelOrientation B = 1 := by
    rw [Manifold.OrientationLift.interval_modelOrientation]
    exact _root_.Orientation.signBasis_orientation _
  rw [hb]
  simp only [Units.val_one, Int.cast_one, one_mul]
  have hrestrict : (∫ z, φ.signedInChartAt B α (fun _ ↦ 1) z ∂B.addHaar) =
      ∫ z in (extChartAt (𝓡∂ 1) α).target,
        φ.signedInChartAt B α (fun _ ↦ 1) z ∂B.addHaar :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by
      rw [RoughForm.signedInChartAt_apply, dite_eq_right hz]).symm
  rw [hrestrict]
  have he : EqOn (φ.signedInChartAt B α (fun _ ↦ 1))
      (fun z : EuclideanSpace ℝ (Fin 1) ↦ f (z 0 + a)) (extChartAt (𝓡∂ 1) α).target := by
    intro z hz
    rw [RoughForm.signedInChartAt_apply, dite_eq_left hz]
    simp only [Units.val_one, Int.cast_one, one_mul]
    rw [inChartAt_mpullback_subtypeVal_Icc ω α hz]
    -- Identify the bottom-chart coefficient with the local real coefficient f before rewriting.
    change (if (α : ℝ) < b then (1 : ℝ) else -1) *
      f ((extChartAt (𝓡∂ 1) α).symm z : ℝ) = f (z 0 + a)
    rw [subtypeVal_extChartAt_Icc_symm α hz]
    simp only [α, Icc.coe_bot, hab.out, ↓reduceIte, one_mul]
  rw [setIntegral_congr_fun (measurableSet_extChartAt_target α) he,
    (EuclideanSpace.basisFun (Fin 1) ℝ).addHaar_eq_volume, extChartAt_Icc_target]
  -- Present the chart target and coordinate function through the same projection for transport.
  change (∫ z in (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0) ⁻¹' Ico 0 (b - a),
    f ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0) z + a)) = _
  rw [(TauCeti.volume_preserving_euclideanSpace_proj (ι := Fin 1) 0).setIntegral_preimage_emb
    (TauCeti.measurableEmbedding_euclideanSpace_proj (ι := Fin 1) 0) (fun t ↦ f (t + a))
    (Ico 0 (b - a)), integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (sub_nonneg.mpr hab.out.le),
    intervalIntegral.integral_comp_add_right]
  simp only [zero_add, sub_add_cancel]
  rfl

/-- Integration of the actual manifold pullback along a model-valued curve that is C1 on
the closed interval is its raw velocity integral. Endpoint derivatives are read within the
interval; they agree with ordinary derivatives at every interior point. -/
theorem integralTopForm_mpullback_curve_Icc {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (ω : RoughForm 𝓘(ℝ, X) X ℝ 1) (γ : ℝ → X)
    (hγ : ContDiffOn ℝ 1 γ (Icc a b))
    (hf : IntervalIntegrable (fun t ↦ ω (γ t)
      (fun _ ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) (γ t)).symm (deriv γ t))) volume a b) :
    IntegrableTopForm (mpullback (𝓡∂ 1) 𝓘(ℝ, X) (fun t : Icc a b ↦ γ t) ω) ∧
      integralTopForm (Manifold.Orientation.interval a b)
        (mpullback (𝓡∂ 1) 𝓘(ℝ, X) (fun t : Icc a b ↦ γ t) ω) =
        ∫ t in a..b, ω (γ t)
          (fun _ ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) (γ t)).symm (deriv γ t)) := by
  let η := mpullbackWithin 𝓘(ℝ) 𝓘(ℝ, X) γ (Icc a b) ω
  have he : EqOn (fun t ↦ η t (fun _ ↦ 1)) (fun t ↦ ω (γ t)
      (fun _ ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) (γ t)).symm (deriv γ t)))
      (uIoo a b) := by
    intro t ht
    rw [uIoo_of_le hab.out.le] at ht
    have hd := (hγ.contDiffAt (Icc_mem_nhds ht.1 ht.2)).contMDiffAt.mdifferentiableAt
      one_ne_zero
    -- Unfold the local pulled-back form η so the within-pullback equation applies.
    change mpullbackWithin 𝓘(ℝ) 𝓘(ℝ, X) γ (Icc a b) ω t _ = _
    rw [mpullbackWithin_eq_mpullback
      ((uniqueDiffOn_Icc hab.out t ⟨ht.1.le, ht.2.le⟩).uniqueMDiffWithinAt) hd ω,
      mpullback_apply, mfderiv_eq_fderiv]
    apply congrArg (ω (γ t))
    funext i
    -- Expose the model derivative conjugation and write the input unit in ℝ explicitly:
    -- the interval module's tangent-unit instance otherwise survives inside fderiv.
    change (NormedSpace.fromTangentSpace (𝕜 := ℝ) (γ t)).symm
        (fderiv ℝ γ t (NormedSpace.fromTangentSpace (𝕜 := ℝ) t (1 : ℝ))) = _
    rw [NormedSpace.fromTangentSpace_apply (𝕜 := ℝ) t (1 : ℝ),
      fderiv_apply_one_eq_deriv]
  have hi : IntervalIntegrable (fun t ↦ η t (fun _ ↦ 1)) volume a b :=
    hf.congr_uIoo (fun t ht ↦ (he ht).symm)
  have h := integralTopForm_mpullback_subtypeVal_Icc η hi
  have hc : mpullback (𝓡∂ 1) 𝓘(ℝ, X) (fun t : Icc a b ↦ γ t) ω =
      mpullback (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc a b → ℝ) η := by
    funext x
    have hmaps : MapsTo (Subtype.val : Icc a b → ℝ) univ (Icc a b) := fun t _ ↦ t.property
    have hx := mpullbackWithin_comp_at
      (((contMDiff_subtypeVal_Icc (x := a) (y := b) (n := 1)).mdifferentiable
        one_ne_zero x).mdifferentiableWithinAt (s := univ))
      ((hγ.contMDiffOn.mdifferentiableOn one_ne_zero) x x.property)
      hmaps
      (uniqueMDiffWithinAt_univ (𝓡∂ 1)) ω
    simpa only [mpullbackWithin_univ, Function.comp_def, η] using hx
  rw [← hc] at h
  exact ⟨h.1, h.2.trans (intervalIntegral.integral_congr_uIoo he)⟩

end TauCeti
