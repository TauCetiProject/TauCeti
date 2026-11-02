/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.CompactSupport
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Pullback

/-!
# Integrability of compactly supported continuous top forms

A finite open chart cover with compact coordinate bounds controls each local coefficient.
Unsigned Jacobian transport then gives integrability on every preferred chart, using only
the model's Borel measurable structure. No Hausdorff or orientation assumption on the
manifold is needed; a model basis records the actual top degree.

The resulting chart formula characterizes the oriented integral of such forms; on a
finite-dimensional normed space with a constant orientation it is the Haar integral of the
coefficient in a positively oriented basis.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {k : ℕ} {n : WithTop ℕ∞} {φ : RoughForm I M ℝ k}

omit [MeasurableSpace E] [BorelSpace E] in
/-- A compactly supported C0 top form satisfies the canonical integrability predicate.
The explicit basis records the degree; the model's Borel structure is used only internally. -/
theorem IsSmoothForm.integrableTopForm (hφ : IsSmoothForm I n φ)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ))
    (b : Module.Basis (Fin k) ℝ E) : IntegrableTopForm φ := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let : LocallyCompactSpace H := I.locallyCompactSpace
  obtain ⟨m, β, u, B, hu, hcover⟩ := exists_finite_precompact_chart_cover (I := I) hc
  apply φ.integrableTopForm_of_open_cover hc b β u (fun i ↦ (hu i).1)
    (fun i ↦ by simpa only [extChartAt_source] using (hu i).2.1) hcover
  intro i
  exact (((φ.continuousOn_signedInChartAt b (β i) (fun _ ↦ 1) continuous_const
    (hφ.continuousOn_inChartAt (β i))).mono (hu i).2.2.2.1).integrableOn_compact
      (hu i).2.2.1 (μ := b.addHaar)).mono_set (hu i).2.2.2.2

/-- Every positive signed preferred-chart coefficient of a compactly supported C0 form is
integrable, including when the manifold is nonorientable or non-Hausdorff. -/
theorem IsSmoothForm.integrable_signedInChartAt_one (hφ : IsSmoothForm I n φ)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ)) (b : Module.Basis (Fin k) ℝ E)
    (α : M) :
    Integrable (φ.signedInChartAt b α (fun _ ↦ 1)) b.addHaar :=
  ((integrableTopForm_iff φ).mp (hφ.integrableTopForm hc b)).2.2 b α

/-- The characteristic equation for compactly supported C0 top forms in a preferred chart.
The coefficient uses the actual ordinary manifold pullback; its possible boundary difference
from the within-range chart expression is Haar-null. -/
theorem integralTopForm_of_tsupport_subset_chart
    (l : Manifold.OrientationLift I M (Fin k)) (hφ : IsSmoothForm I 0 φ)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ)) (α : M) (hs :
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) ⊆ (chartAt H α).source)
    (b : Module.Basis (Fin k) ℝ E) (hb : b.orientation = l.modelOrientation) :
    integralTopForm (Manifold.Orientation.mk l) φ =
      ∫ y in (extChartAt I α).target,
        (l.signAt α ((extChartAt I α).symm y) : ℝ) *
          mpullback 𝓘(ℝ, E) I (extChartAt I α).symm φ y b ∂b.addHaar := by
  rw [integralTopForm_eq_chartIntegral l φ (hφ.integrableTopForm hc b) α
    (by simpa only [extChartAt_source] using hs),
    l.chartIntegral_eq_integral_mpullback φ b α, ← hb,
    _root_.Orientation.signBasis_orientation]
  simp

/-- On a finite-dimensional normed space with a constant orientation, the oriented integral of
a compactly supported C0 top form is the integral of its coefficient in any positively oriented
basis against that basis's Haar measure. -/
theorem integralTopForm_model_eq_integral (o : _root_.Orientation ℝ E (Fin k))
    (hk : Fintype.card (Fin k) = Module.finrank ℝ E) {φ : RoughForm 𝓘(ℝ, E) E ℝ k}
    (hφ : IsSmoothForm 𝓘(ℝ, E) 0 φ)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ))
    (b : Module.Basis (Fin k) ℝ E) (hb : b.orientation = o) :
    integralTopForm (Manifold.Orientation.model (I := 𝓘(ℝ, E)) o hk) φ =
      ∫ x, φ x b ∂b.addHaar := by
  rw [Manifold.Orientation.model_eq_mk,
    integralTopForm_of_tsupport_subset_chart _ hφ hc 0 (by simp) b
      (hb.trans (Manifold.OrientationLift.model_modelOrientation o hk).symm)]
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_target, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, Measure.restrict_univ]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only [id_eq, mpullback_id]
  rw [Manifold.OrientationLift.signAt_of_mem _ (by simp), Manifold.OrientationLift.model_sign]
  simp

omit [MeasurableSpace E] [BorelSpace E] in
/-- The oriented integral is additive for compactly supported C0 top forms. -/
theorem integralTopForm_add (o : Manifold.Orientation I M (Fin k))
    {ψ : RoughForm I M ℝ k} (hφ : IsSmoothForm I 0 φ) (hψ : IsSmoothForm I 0 ψ)
    (hcφ : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ)) (hcψ : IsCompact
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) ψ)) :
    integralTopForm o (φ + ψ) = integralTopForm o φ + integralTopForm o ψ := by
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using o.card_eq.symm)
  exact integralTopForm_add_of_integrable o
    (hφ.integrableTopForm hcφ b) (hψ.integrableTopForm hcψ b)

end TauCeti
