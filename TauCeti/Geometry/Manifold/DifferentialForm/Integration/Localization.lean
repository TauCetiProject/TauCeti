/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.CompactSupport
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Operations
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Integrability under scalar localization

A continuous scalar preserves integrability of a compactly supported chart coefficient even
when the underlying form is merely rough. This permits refinement of chart partitions without
imposing continuity on every integrable form.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Manifold

namespace TauCeti.RoughForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [MeasurableSpace E] [BorelSpace E] {k : ℕ}

/-- Continuous scalar localization preserves integrability of a rough form's coefficient in a
chart containing its compact support. No regularity of the form itself is required. -/
theorem integrable_signedInChartAt_fun_smul (φ : RoughForm I M ℝ k)
    (b : Module.Basis (Fin k) ℝ E) (α : M)
    (σ : {x : M // x ∈ (extChartAt I α).source} → ℤˣ)
    (hc : IsCompact φ.tsupport) (hs : φ.tsupport ⊆ (extChartAt I α).source)
    (f : C(M, ℝ)) (μ : Measure E)
    (hi : Integrable (φ.signedInChartAt b α σ) μ) :
    Integrable (signedInChartAt (I := I) (fun x ↦ f x • φ x) b α σ) μ := by
  have hK : IsCompact ((extChartAt I α) '' φ.tsupport) :=
    hc.image_of_continuousOn ((continuousOn_extChartAt α).mono hs)
  have htarget : (extChartAt I α) '' φ.tsupport ⊆ (extChartAt I α).target :=
    (image_mono hs).trans (extChartAt I α).image_source_eq_target.subset
  have hf : ContinuousOn (fun y ↦ f ((extChartAt I α).symm y))
      ((extChartAt I α) '' φ.tsupport) :=
    f.continuous.comp_continuousOn ((continuousOn_extChartAt_symm α).mono htarget)
  have hprod := hi.integrableOn.continuousOn_mul hf hK
  have hsupport : Function.support
      (signedInChartAt (I := I) (fun x ↦ f x • φ x) b α σ) ⊆
      (extChartAt I α) '' φ.tsupport :=
    (support_signedInChartAt_subset _ b α σ).trans
      (image_mono (tsupport_fun_smul_subset_right f φ))
  apply (integrableOn_iff_integrable_of_support_subset hsupport).mp
  convert hprod using 1
  ext y
  exact signedInChartAt_fun_smul f φ b α σ y

end TauCeti.RoughForm
