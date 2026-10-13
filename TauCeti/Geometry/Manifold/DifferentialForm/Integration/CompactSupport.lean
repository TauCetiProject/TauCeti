/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Chart
public import TauCeti.Geometry.Manifold.DifferentialForm.Support
public import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Integrability of chart-supported signed top forms

The signed coordinate coefficient of a form supported compactly within one chart has support
in the compact coordinate image of its manifold support. Continuity on the chart target gives
actual Haar integrability; extending by zero outside the target causes no boundary assumption.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Manifold

namespace TauCeti.RoughForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {k : ℕ}

/-- The signed chart coefficient is supported within the coordinate image of the form support. -/
theorem support_signedInChartAt_subset (φ : RoughForm I M ℝ k)
    (b : Module.Basis (Fin k) ℝ E) (α : M)
    (σ : {x : M // x ∈ (extChartAt I α).source} → ℤˣ) :
    Function.support (φ.signedInChartAt b α σ) ⊆ (extChartAt I α) '' φ.tsupport := by
  classical
  intro y hy
  have hnonzero := Function.mem_support.mp hy
  by_cases ht : y ∈ (extChartAt I α).target
  · have hf : φ ((extChartAt I α).symm y) ≠ 0 := by
      intro hf
      apply hnonzero
      have hz : φ.inChartAt α y b = 0 := by
        rw [inChartAt_apply, hf]
        rfl
      rw [signedInChartAt_apply, dite_eq_left ht, hz, mul_zero]
    exact ⟨(extChartAt I α).symm y, mem_tsupport_of_ne_zero hf,
      (extChartAt I α).right_inv ht⟩
  · exact False.elim (hnonzero (by rw [signedInChartAt_apply, dite_eq_right ht]))

/-- Source-continuous chart signs preserve continuity of the coefficient on the chart target. -/
theorem continuousOn_signedInChartAt (φ : RoughForm I M ℝ k)
    (b : Module.Basis (Fin k) ℝ E) (α : M)
    (σ : {x : M // x ∈ (extChartAt I α).source} → ℤˣ) (hσ : Continuous σ)
    (hφ : ContinuousOn (φ.inChartAt α) (extChartAt I α).target) :
    ContinuousOn (φ.signedInChartAt b α σ) (extChartAt I α).target := by
  let τ : (extChartAt I α).target → (extChartAt I α).source :=
    fun y ↦ ⟨(extChartAt I α).symm y, (extChartAt I α).map_target y.property⟩
  have hτ : Continuous τ :=
    (continuousOn_extChartAt_symm (I := I) α).domRestrict.subtype_mk _
  have hcast : Continuous (fun u : ℤˣ ↦ (u : ℝ)) := continuous_of_discreteTopology
  have hcoeff : ContinuousOn (fun y ↦ φ.inChartAt α y b) (extChartAt I α).target :=
    (continuous_eval_const (b : Fin k → E)).comp_continuousOn hφ
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (extChartAt I α).target.domRestrict (φ.signedInChartAt b α σ) =
      fun y : (extChartAt I α).target ↦
        (σ (τ y) : ℝ) * φ.inChartAt α y b := by
    funext y
    exact (signedInChartAt_apply φ b α σ y).trans (dite_eq_left y.property)
  rw [he]
  exact (hcast.comp (hσ.comp hτ)).mul hcoeff.domRestrict

variable [MeasurableSpace E] [BorelSpace E]

/-- A compactly supported chart coefficient is genuinely integrable against normalized Haar
measure, using only continuity in coordinates and continuity of the source-indexed sign. -/
theorem integrable_signedInChartAt (φ : RoughForm I M ℝ k)
    (b : Module.Basis (Fin k) ℝ E) (α : M)
    (σ : {x : M // x ∈ (extChartAt I α).source} → ℤˣ) (hσ : Continuous σ)
    (hφ : ContinuousOn (φ.inChartAt α) (extChartAt I α).target)
    (hc : IsCompact φ.tsupport) (hs : φ.tsupport ⊆ (extChartAt I α).source)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    Integrable (φ.signedInChartAt b α σ) μ := by
  have hK : IsCompact ((extChartAt I α) '' φ.tsupport) :=
    hc.image_of_continuousOn ((continuousOn_extChartAt α).mono hs)
  have htarget : (extChartAt I α) '' φ.tsupport ⊆ (extChartAt I α).target :=
    (image_mono hs).trans (extChartAt I α).image_source_eq_target.subset
  exact (integrableOn_iff_integrable_of_support_subset
    (φ.support_signedInChartAt_subset b α σ)).mp
      ((φ.continuousOn_signedInChartAt b α σ hσ hφ).mono htarget |>.integrableOn_compact hK)

variable [FiniteDimensional ℝ E]

/-- Chart-supported compact top forms have the same actual signed coefficient integral in
any two charts containing their support. Only the model is equipped with a measurable structure. -/
theorem integral_signedInChartAt_eq_of_tsupport_subset [IsManifold I 1 M]
    (φ : RoughForm I M ℝ k) (b : Module.Basis (Fin k) ℝ E) (α β : M)
    (σα : {x : M // x ∈ (extChartAt I α).source} → ℤˣ)
    (σβ : {x : M // x ∈ (extChartAt I β).source} → ℤˣ)
    (hc : IsCompact φ.tsupport)
    (hsub : φ.tsupport ⊆ (extChartAt I α).source ∩ (extChartAt I β).source)
    (hσ : ∀ x (hx : x ∈ φ.tsupport),
      (σα ⟨x, (hsub hx).1⟩ : ℝ) *
        (fderivWithin ℝ (extChartAt I β ∘ (extChartAt I α).symm) (range I)
          (extChartAt I α x)).toLinearMap.det =
      |(fderivWithin ℝ (extChartAt I β ∘ (extChartAt I α).symm) (range I)
          (extChartAt I α x)).toLinearMap.det| * (σβ ⟨x, (hsub hx).2⟩ : ℝ))
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    (∫ y, φ.signedInChartAt b α σα y ∂μ) = ∫ y, φ.signedInChartAt b β σβ y ∂μ := by
  have hm : MeasurableSet ((extChartAt I α) '' φ.tsupport) :=
    (hc.image_of_continuousOn
      ((continuousOn_extChartAt α).mono (hsub.trans inter_subset_left))).measurableSet
  have hα : (∫ y in (extChartAt I α) '' φ.tsupport, φ.signedInChartAt b α σα y ∂μ) =
      ∫ y, φ.signedInChartAt b α σα y ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by
      by_contra hn
      exact hy (φ.support_signedInChartAt_subset b α σα (Function.mem_support.mpr hn))
  have hβ : (∫ y in (extChartAt I β) '' φ.tsupport, φ.signedInChartAt b β σβ y ∂μ) =
      ∫ y, φ.signedInChartAt b β σβ y ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by
      by_contra hn
      exact hy (φ.support_signedInChartAt_subset b β σβ (Function.mem_support.mpr hn))
  exact hα.symm.trans ((φ.signedInChartAt_changeChart b α β σα σβ hsub hm hσ μ).1.trans hβ)

/-- Genuine integrability of an arbitrary rough compact chart-supported form transports
between charts containing its support. This does not assume continuity of the form. -/
theorem integrable_signedInChartAt_iff_of_tsupport_subset [IsManifold I 1 M]
    (φ : RoughForm I M ℝ k) (b : Module.Basis (Fin k) ℝ E) (α β : M)
    (σα : {x : M // x ∈ (extChartAt I α).source} → ℤˣ)
    (σβ : {x : M // x ∈ (extChartAt I β).source} → ℤˣ)
    (hc : IsCompact φ.tsupport)
    (hsub : φ.tsupport ⊆ (extChartAt I α).source ∩ (extChartAt I β).source)
    (hσ : ∀ x (hx : x ∈ φ.tsupport),
      (σα ⟨x, (hsub hx).1⟩ : ℝ) *
        (fderivWithin ℝ (extChartAt I β ∘ (extChartAt I α).symm) (range I)
          (extChartAt I α x)).toLinearMap.det =
      |(fderivWithin ℝ (extChartAt I β ∘ (extChartAt I α).symm) (range I)
          (extChartAt I α x)).toLinearMap.det| * (σβ ⟨x, (hsub hx).2⟩ : ℝ))
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    Integrable (φ.signedInChartAt b α σα) μ ↔ Integrable (φ.signedInChartAt b β σβ) μ := by
  have hm : MeasurableSet ((extChartAt I α) '' φ.tsupport) :=
    (hc.image_of_continuousOn
      ((continuousOn_extChartAt α).mono (hsub.trans inter_subset_left))).measurableSet
  have ht := (φ.signedInChartAt_changeChart b α β σα σβ hsub hm hσ μ).2
  rw [integrableOn_iff_integrable_of_support_subset (φ.support_signedInChartAt_subset b α σα),
    integrableOn_iff_integrable_of_support_subset (φ.support_signedInChartAt_subset b β σβ)] at ht
  exact ht

end TauCeti.RoughForm

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace E] [BorelSpace E] {k : ℕ} {n : WithTop ℕ∞}

/-- A regular form with compact support in one chart has a genuinely integrable signed
coefficient. `C⁰` regularity already suffices. -/
theorem IsSmoothForm.integrable_signedInChartAt {φ : RoughForm I M ℝ k}
    (hφ : IsSmoothForm I n φ) (b : Module.Basis (Fin k) ℝ E) (α : M)
    (σ : {x : M // x ∈ (extChartAt I α).source} → ℤˣ) (hσ : Continuous σ)
    (hc : IsCompact φ.tsupport) (hs : φ.tsupport ⊆ (extChartAt I α).source)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    Integrable (φ.signedInChartAt b α σ) μ :=
  φ.integrable_signedInChartAt b α σ hσ (hφ.continuousOn_inChartAt α) hc hs μ

end TauCeti
