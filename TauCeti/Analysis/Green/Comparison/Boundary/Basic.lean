/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.DifferentialForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
public import TauCeti.MeasureTheory.Measure.Haar.EuclideanSpace
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Circulation in oriented boundary charts

A parametrization of an actual one-dimensional manifold reads pullback of the planar
circulation form as the raw circulation integrand. The boundary orientation supplies the
outward-first sign when this is applied to Stokes' theorem.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Manifold

namespace TauCeti.Green

private abbrev lineParam : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm.toContinuousLinearMap

private theorem lineParam_apply (t : ℝ) :
    lineParam t = (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t) := rfl

private theorem lineParam_one :
    lineParam 1 = (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis 0 := by
  ext i
  rw [Subsingleton.elim i 0]
  simp [lineParam, EuclideanSpace.basisFun_apply]

variable {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 1)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 1 N]

/-- In an actual one-dimensional chart, pullback of the planar circulation form is the
raw circulation along its parametrization, with the usual real derivative. -/
theorem inChartAt_mpullback_manifoldOneForm_eq_circulationFun
    (P Q : ℂ → ℝ) (f : N → ℂ)
    (hf : MDifferentiable 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) f)
    (α : N) {t : ℝ}
    (ht : (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t) ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).target) :
    (mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) f
        (manifoldOneForm P Q)).inChartAt α
          ((EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t))
          (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis =
      circulationFun P Q
        (fun s ↦ f ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).symm
          ((EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ s)))) t := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α
  let g : EuclideanSpace ℝ (Fin 1) → ℂ := f ∘ e.symm
  have ht' : lineParam t ∈ e.target := ht
  have hd : DifferentiableAt ℝ g (lineParam t) := by
    have h := (hf (e.symm (lineParam t))).comp_mdifferentiableWithinAt (lineParam t)
      (mdifferentiableWithinAt_extChartAt_symm ht')
    simpa only [_root_.ModelWithCorners.range_eq_univ, mdifferentiableWithinAt_univ,
      mdifferentiableAt_iff_differentiableAt] using h
  have hγ := hd.hasFDerivAt.comp_hasDerivAt t lineParam.hasFDerivAt.hasDerivAt
  -- Name the canonical inverse projection so the derivative chain rule matches the parameter map.
  change (mpullback _ _ f (manifoldOneForm P Q)).inChartAt α (lineParam t)
    (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis = circulationFun P Q (g ∘ lineParam) t
  rw [RoughForm.inChartAt_mpullback_modelSpace _ f α ht' (hf _),
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    manifoldOneForm_apply, circulationFun_eq_oneForm, hγ.deriv,
    _root_.ModelWithCorners.range_eq_univ, fderivWithin_univ, lineParam_one]
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
  rfl

/-- A compact chart-supported localization of the actual pulled-back circulation form has
its parametrized circulation integral. The representing orientation supplies the model and
chart signs, and integrability of the parametrized coefficient is a conclusion. -/
theorem integralTopForm_weighted_mpullback_chart
    (l : Manifold.OrientationLift 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) N (Fin 1))
    (P Q : ℂ → ℝ) (f : N → ℂ)
    (hf : MDifferentiable 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) f)
    (ρ : N → ℝ) (α : N) (c : ℤˣ) {γ : ℝ → ℂ}
    (hγ : ∀ t, γ t = f ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).symm
      ((EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t))))
    (hi : IntegrableTopForm (fun x ↦ ρ x •
      mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q) x))
    (hs : (_root_.tsupport (α := (EuclideanSpace ℝ (Fin 1)) [⋀^Fin _]→L[ℝ] ℝ) (fun x ↦ ρ x •
      mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q) x)) ⊆
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).source)
    (hσ : ∀ x ∈ _root_.tsupport (α := (EuclideanSpace ℝ (Fin 1)) [⋀^Fin _]→L[ℝ] ℝ) (fun x ↦ ρ x •
      mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q) x),
        l.signAt α x = c) :
    IntegrableOn (fun t ↦ ρ ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).symm
      ((EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t))) * circulationFun P Q γ t)
      {t | (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t) ∈
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).target} ∧
    integralTopForm (Manifold.Orientation.mk l) (fun x ↦ ρ x •
      mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q) x) =
      (Orientation.signBasis l.modelOrientation (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis : ℝ) *
        (c : ℝ) * ∫ t in {t | (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t) ∈
          (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).target},
          ρ ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).symm
            ((EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t))) * circulationFun P Q γ t := by
  let ψ : RoughForm 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) N ℝ 1 := fun x ↦ ρ x •
    mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q) x
  let b := (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α
  let A : Set ℝ := {t | lineParam t ∈ e.target}
  let g : ℝ → ℝ := fun t ↦ ρ (e.symm (lineParam t)) * circulationFun P Q γ t
  let F := A.indicator g
  have hA : MeasurableSet A := (measurableSet_extChartAt_target α).preimage lineParam.measurable
  have hγ' : (fun t ↦ f (e.symm (lineParam t))) = γ := (funext hγ).symm
  have hS : ψ.signedInChartAt b α (fun _ ↦ 1) =
      F ∘ EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0 := by
    funext z
    have he : lineParam (z 0) = z :=
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm_apply_apply z
    -- Expose function composition and indicator evaluation at the unique real coordinate.
    change ψ.signedInChartAt b α (fun _ ↦ 1) z = A.indicator g (z 0)
    by_cases hz : z ∈ e.target
    · have ht : z 0 ∈ A := by simpa only [A, he, mem_ofPred_eq] using hz
      rw [indicator_of_mem ht]
      rw [RoughForm.signedInChartAt_apply, dite_eq_left hz]
      simp only [Units.val_one, Int.cast_one, one_mul]
      rw [RoughForm.inChartAt_fun_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      have htarget : lineParam (z 0) ∈ e.target := he.symm ▸ hz
      have hr := inChartAt_mpullback_manifoldOneForm_eq_circulationFun P Q f hf α htarget
      -- Use the named basis and inverse projection before rewriting the parameter inverse law.
      change (mpullback _ _ f (manifoldOneForm P Q)).inChartAt α (lineParam (z 0)) b =
        circulationFun P Q (fun t ↦ f (e.symm (lineParam t))) (z 0) at hr
      rw [he, hγ'] at hr
      simpa only [g, EuclideanSpace.coe_proj, he] using congrArg (fun r ↦ ρ (e.symm z) * r) hr
    · have ht : z 0 ∉ A := by simpa only [A, he, mem_ofPred_eq] using hz
      rw [RoughForm.signedInChartAt_apply, dite_eq_right hz,
        indicator_of_notMem ht]
  have hiS : Integrable (ψ.signedInChartAt b α (fun _ ↦ 1)) := by
    have h := ((integrableTopForm_iff ψ).mp hi).2.2 b α
    rwa [(EuclideanSpace.basisFun (Fin 1) ℝ).addHaar_eq_volume] at h
  have hiF : Integrable F :=
    ((TauCeti.volume_preserving_euclideanSpace_proj (ι := Fin 1) 0).integrable_comp_emb
      (TauCeti.measurableEmbedding_euclideanSpace_proj (ι := Fin 1) 0)).mp (by rwa [← hS])
  have heq : (∫ z, ψ.signedInChartAt b α (fun _ ↦ 1) z ∂b.addHaar) = ∫ t in A, g t := by
    rw [(EuclideanSpace.basisFun (Fin 1) ℝ).addHaar_eq_volume, hS]
    have ht :=
      (TauCeti.volume_preserving_euclideanSpace_proj (ι := Fin 1) 0).setIntegral_preimage_emb
      (TauCeti.measurableEmbedding_euclideanSpace_proj (ι := Fin 1) 0) F univ
    simp only [preimage_univ, setIntegral_univ] at ht
    -- The measure-preserving projection theorem is stated using explicit function composition.
    change (∫ z, F (EuclideanSpace.proj 0 z)) = _
    rw [ht]
    exact integral_indicator hA
  refine ⟨(integrable_indicator_iff hA).mp hiF, ?_⟩
  rw [integralTopForm_eq_chartIntegral l ψ hi α hs,
    l.chartIntegral_eq_const_mul_unsigned ψ b α c hσ, heq]
  rfl

/-- If a chart-supported circulation form has its coordinate support in `[a,b]` and that
interval stays in the chart target, its canonical integral is signed ordinary circulation
on `a..b`. This connects the boundary-chart description to interval and curve integration. -/
theorem integralTopForm_mpullback_chart_eq_intervalIntegral
    (l : Manifold.OrientationLift 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) N (Fin 1))
    (P Q : ℂ → ℝ) (f : N → ℂ)
    (hf : MDifferentiable 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) f)
    (α : N) (c : ℤˣ) {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ∀ t, γ t = f ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).symm
      ((EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t))))
    (hi : IntegrableTopForm
      (mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)))
    (hs : (_root_.tsupport (α := (EuclideanSpace ℝ (Fin 1)) [⋀^Fin _]→L[ℝ] ℝ)
    (mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) f
      (manifoldOneForm P Q))) ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).source)
    (hσ : ∀ x ∈ (_root_.tsupport (α := (EuclideanSpace ℝ (Fin 1)) [⋀^Fin _]→L[ℝ] ℝ)
    (mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) f
      (manifoldOneForm P Q))), l.signAt α x = c)
    (hb : ∀ x ∈ (_root_.tsupport (α := (EuclideanSpace ℝ (Fin 1)) [⋀^Fin _]→L[ℝ] ℝ)
    (mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) f
      (manifoldOneForm P Q))),
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α x) 0 ∈ Icc a b)
    (ht : ∀ t ∈ Icc a b, (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t) ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).target) :
    IntervalIntegrable (circulationFun P Q γ) volume a b ∧
      integralTopForm (Manifold.Orientation.mk l)
        (mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)) =
        (Orientation.signBasis l.modelOrientation (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis : ℝ) *
          (c : ℝ) * ∫ t in a..b, circulationFun P Q γ t := by
  let φ := mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α
  let A : Set ℝ := {t | lineParam t ∈ e.target}
  have hA : MeasurableSet A := (measurableSet_extChartAt_target α).preimage lineParam.measurable
  have hsub : Icc a b ⊆ A := ht
  have hr := integralTopForm_weighted_mpullback_chart l P Q f hf (fun _ ↦ 1) α c hγ
    (by simpa only [one_smul] using hi) (by simpa only [one_smul] using hs)
    (by simpa only [one_smul] using hσ)
  have hcirci : IntegrableOn (circulationFun P Q γ) A := by
    simpa only [one_mul, A, e, lineParam_apply] using hr.1
  have hγ' : (fun t ↦ f (e.symm (lineParam t))) = γ := (funext hγ).symm
  have hzero : ∀ t ∈ A \ Icc a b, circulationFun P Q γ t = 0 := by
    intro t ht'
    have htarget : lineParam t ∈ e.target := ht'.1
    have hn : e.symm (lineParam t) ∉
    (_root_.tsupport (α := (EuclideanSpace ℝ (Fin 1)) [⋀^Fin _]→L[ℝ] ℝ) φ) := by
      intro hx
      have hb' := hb _ hx
      rw [e.right_inv htarget] at hb'
      exact ht'.2 hb'
    have he := inChartAt_mpullback_manifoldOneForm_eq_circulationFun P Q f hf α htarget
    -- Expose the localized coefficient in the canonical one-coordinate parametrization.
    change φ.inChartAt α (lineParam t) (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis =
      circulationFun P Q (fun t ↦ f (e.symm (lineParam t))) t at he
    rw [hγ'] at he
    have hz : φ (e.symm (lineParam t)) = 0 :=
      _root_.image_eq_zero_of_notMem_tsupport
        (α := (EuclideanSpace ℝ (Fin 1)) [⋀^Fin _]→L[ℝ] ℝ) hn
    rw [← he, RoughForm.inChartAt_apply, hz]
    simp only [ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  have heq : (∫ t in A, circulationFun P Q γ t) = ∫ t in a..b, circulationFun P Q γ t := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hA hsub hzero,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    (hcirci.mono_set hsub), ?_⟩
  have hr' : integralTopForm (Manifold.Orientation.mk l) φ =
      (Orientation.signBasis l.modelOrientation (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis : ℝ) *
        (c : ℝ) * ∫ t in A, circulationFun P Q γ t := by
    simpa only [one_smul, one_mul, φ, A, e, lineParam_apply] using hr.2
  rw [heq] at hr'
  exact hr'

/-- An actual path parametrizing a bounded boundary chart computes the same canonical
form integral through Mathlib's existing curve integral. Agreement on the unit interval
suffices, since derivatives of the two parametrizations agree on its interior. -/
theorem integralTopForm_mpullback_chart_eq_curveIntegral
    (l : Manifold.OrientationLift 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) N (Fin 1))
    (P Q : ℂ → ℝ) (f : N → ℂ)
    (hf : MDifferentiable 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) f)
    (α : N) (c : ℤˣ) {p q : ℂ} (γ : Path p q)
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t = f ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).symm
      ((EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t))))
    (hi : IntegrableTopForm
      (mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)))
    (hs : (_root_.tsupport (α := (EuclideanSpace ℝ (Fin 1)) [⋀^Fin _]→L[ℝ] ℝ)
    (mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) f
      (manifoldOneForm P Q))) ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).source)
    (hσ : ∀ x ∈ (_root_.tsupport (α := (EuclideanSpace ℝ (Fin 1)) [⋀^Fin _]→L[ℝ] ℝ)
    (mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) f
      (manifoldOneForm P Q))), l.signAt α x = c)
    (hb : ∀ x ∈ (_root_.tsupport (α := (EuclideanSpace ℝ (Fin 1)) [⋀^Fin _]→L[ℝ] ℝ)
    (mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) f
      (manifoldOneForm P Q))),
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α x) 0 ∈ Icc (0 : ℝ) 1)
    (ht : ∀ t ∈ Icc (0 : ℝ) 1, (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t) ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).target) :
    IntervalIntegrable (circulationFun P Q γ.extend) volume 0 1 ∧
      integralTopForm (Manifold.Orientation.mk l)
        (mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)) =
        (Orientation.signBasis l.modelOrientation (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis : ℝ) *
          (c : ℝ) * curveIntegral (oneForm P Q) γ := by
  let Γ : ℝ → ℂ := fun t ↦ f ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).symm
    ((EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t)))
  have hr := integralTopForm_mpullback_chart_eq_intervalIntegral l P Q f hf α c
    (γ := Γ) (a := 0) (b := 1) zero_le_one (fun _ ↦ rfl) hi hs hσ hb ht
  have he : EqOn (circulationFun P Q Γ) (circulationFun P Q γ.extend) (uIoo 0 1) := by
    intro t ht'
    rw [uIoo_of_le zero_le_one] at ht'
    have heq : Γ =ᶠ[nhds t] γ.extend := by
      filter_upwards [isOpen_Ioo.mem_nhds ht'] with u hu
      exact (hγ u (Ioo_subset_Icc_self hu)).symm
    rw [circulationFun_eq_oneForm, circulationFun_eq_oneForm, heq.eq_of_nhds, heq.deriv_eq]
  refine ⟨hr.1.congr_uIoo he, ?_⟩
  rw [curveIntegral_oneForm_eq]
  exact hr.2.trans (congrArg (fun r ↦
    (Orientation.signBasis l.modelOrientation (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis : ℝ) *
      (c : ℝ) * r) (intervalIntegral.integral_congr_uIoo he))

end TauCeti.Green
