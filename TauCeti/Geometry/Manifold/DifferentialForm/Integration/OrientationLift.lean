/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.CompactSupport
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Operations
public import TauCeti.Geometry.Manifold.Orientation.Lift

/-!
# Chart integrals against actual orientation lifts

An orientation lift determines an actual signed chart functional, expressed using an arbitrary
model basis and its normalized Haar measure. The relative basis sign makes the functional
independent of the basis, including in dimension zero. Actual lift compatibility then gives
agreement between charts containing the compact support of the form.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Manifold

namespace TauCeti.Manifold.OrientationLift

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {k : ℕ}

/-- The chart integral against a lift, with actual source-indexed chart signs and normalized
Haar measure. Its basis choice is removed by `chartIntegral_eq_integral`. -/
def chartIntegral (l : OrientationLift I M (Fin k)) (φ : TauCeti.RoughForm I M ℝ k)
    (α : M) : ℝ :=
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
  (_root_.Orientation.signBasis l.modelOrientation b : ℝ) *
    ∫ y, φ.signedInChartAt b α (fun x ↦ l.signAt α x) y ∂b.addHaar

omit [IsManifold I 1 M] in
/-- Any model basis gives the actual chart integral, with its relative orientation sign. -/
theorem chartIntegral_eq_integral (l : OrientationLift I M (Fin k))
    (φ : TauCeti.RoughForm I M ℝ k) (b : Module.Basis (Fin k) ℝ E) (α : M) :
    l.chartIntegral φ α = (_root_.Orientation.signBasis l.modelOrientation b : ℝ) *
      ∫ y, φ.signedInChartAt b α (fun x ↦ l.signAt α x) y ∂b.addHaar := by
  rw [chartIntegral]
  exact φ.integral_signedInChartAt_basis_eq l.modelOrientation _ b α (fun x ↦ l.signAt α x)

/-- A continuous compact chart-supported form has an integrable actual coefficient for the lift. -/
theorem integrable_signedInChartAt (l : OrientationLift I M (Fin k))
    {φ : TauCeti.RoughForm I M ℝ k} {n : WithTop ℕ∞} (hφ : TauCeti.IsSmoothForm I n φ)
    (b : Module.Basis (Fin k) ℝ E) (α : M) (hc : IsCompact
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ))
    (hs : (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) ⊆ (extChartAt I α).source) :
    Integrable (φ.signedInChartAt b α (fun x ↦ l.signAt α x)) b.addHaar :=
  hφ.integrable_signedInChartAt b α (fun x ↦ l.signAt α x) (by
    apply continuousOn_iff_continuous_domRestrict.mp
    simpa only [extChartAt_source] using l.continuousOn_signAt α)
    hc hs b.addHaar

/-- The actual lift chart integrals agree when both charts contain the form support.
The signed Jacobian relation is derived from the lift, rather than supplied as an extra premise. -/
theorem chartIntegral_eq_of_tsupport_subset (l : OrientationLift I M (Fin k))
    (φ : TauCeti.RoughForm I M ℝ k) (α β : M)
    (hα : (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) ⊆ (extChartAt I α).source)
    (hβ : (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) ⊆ (extChartAt I β).source) :
    l.chartIntegral φ α = l.chartIntegral φ β := by
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
  rw [chartIntegral_eq_integral l φ b α, chartIntegral_eq_integral l φ b β]
  congr 1
  apply φ.integral_signedInChartAt_eq_of_tsupport_subset b α β (fun x ↦ l.signAt α x)
    (fun x ↦ l.signAt β x)
    (fun x hx ↦ ⟨hα hx, hβ hx⟩)
  intro x hx
  have hα' : x ∈ (chartAt H α).source := by simpa only [extChartAt_source] using hx.1
  have hβ' : x ∈ (chartAt H β).source := by simpa only [extChartAt_source] using hx.2
  simpa only [signAt_of_mem _ hα', signAt_of_mem _ hβ'] using
    l.sign_mul_det α β x hα' hβ'

/-- Genuine coefficient integrability of arbitrary rough forms is preserved between
charts containing the support, using the actual lift compatibility. -/
theorem integrable_signedInChartAt_iff_of_tsupport_subset (l : OrientationLift I M (Fin k))
    (φ : TauCeti.RoughForm I M ℝ k) (b : Module.Basis (Fin k) ℝ E) (α β : M)
    (hα : (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) ⊆ (extChartAt I α).source)
    (hβ : (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) ⊆ (extChartAt I β).source) :
    Integrable (φ.signedInChartAt b α (fun x ↦ l.signAt α x)) b.addHaar ↔
      Integrable (φ.signedInChartAt b β (fun x ↦ l.signAt β x)) b.addHaar := by
  apply φ.integrable_signedInChartAt_iff_of_tsupport_subset b α β (fun x ↦ l.signAt α x)
    (fun x ↦ l.signAt β x)
    (fun x hx ↦ ⟨hα hx, hβ hx⟩)
  intro x hx
  have hα' : x ∈ (chartAt H α).source := by simpa only [extChartAt_source] using hx.1
  have hβ' : x ∈ (chartAt H β).source := by simpa only [extChartAt_source] using hx.2
  simpa only [signAt_of_mem _ hα', signAt_of_mem _ hβ'] using
    l.sign_mul_det α β x hα' hβ'

omit [IsManifold I 1 M] in
/-- Reversing the actual manifold orientation reverses the lift's chart integral. -/
theorem chartIntegral_neg (l : OrientationLift I M (Fin k))
    (φ : TauCeti.RoughForm I M ℝ k) (α : M) :
    (-l).chartIntegral φ α = -l.chartIntegral φ α := by
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
  rw [chartIntegral_eq_integral (-l) φ b α, chartIntegral_eq_integral l φ b α]
  simp only [neg_signAt, neg_modelOrientation, _root_.Orientation.signBasis_neg]
  simp

omit [IsManifold I 1 M] in
/-- Simultaneous reversal of the model orientation and source signs preserves the actual
chart integral, so the functional depends only on the manifold orientation. -/
theorem chartIntegral_flip (l : OrientationLift I M (Fin k))
    (φ : TauCeti.RoughForm I M ℝ k) (α : M) : l.flip.chartIntegral φ α = l.chartIntegral φ α := by
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
  rw [chartIntegral_eq_integral l.flip φ b α, chartIntegral_eq_integral l φ b α]
  have hs : (fun x : (extChartAt I α).source ↦ l.flip.signAt α x) =
      fun x : (extChartAt I α).source ↦ -l.signAt α x := by
    funext x
    exact l.flip_signAt_of_mem (by simpa only [extChartAt_source] using x.property)
  rw [flip_modelOrientation, hs]
  exact φ.integral_signedInChartAt_diagonal_flip l.modelOrientation b α (fun x ↦ l.signAt α x)

omit [IsManifold I 1 M] in
/-- A lift sign constant on the support factors out of its genuine normalized chart integral. -/
theorem chartIntegral_eq_const_mul_unsigned
    (l : OrientationLift I M (Fin k)) (ψ : TauCeti.RoughForm I M ℝ k)
    (b : Module.Basis (Fin k) ℝ E) (α : M) (c : ℤˣ)
    (hσ : ∀ x ∈ (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) ψ), l.signAt α x = c) :
    l.chartIntegral ψ α = (_root_.Orientation.signBasis l.modelOrientation b : ℝ) *
      (c : ℝ) * ∫ y, ψ.signedInChartAt b α (fun _ ↦ 1) y ∂b.addHaar := by
  rw [l.chartIntegral_eq_integral ψ b α,
    ψ.signedInChartAt_eq_const_mul_unsigned b α (fun x ↦ l.signAt α x) c (fun x hx ↦ hσ x hx),
    MeasureTheory.integral_const_mul, mul_assoc]

end TauCeti.Manifold.OrientationLift
