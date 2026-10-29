/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Bochner.Alternating
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Chart.Basic

/-!
# Basis independence of signed chart integrals

The source-indexed chart sign and the relative basis sign serve different purposes. The former
corrects a chart's orientation; the latter lets integration use an arbitrary basis, including
negative model orientations in dimension zero. The actual signed chart integral is independent
of that arbitrary basis, with the corresponding normalized Haar measure.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Manifold

namespace TauCeti.RoughForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {k : ℕ}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private def signedChartExpression (φ : RoughForm I M ℝ k) (α : M)
    (σ : {x : M // x ∈ (extChartAt I α).source} → ℤˣ) (y : E) : E [⋀^Fin k]→L[ℝ] ℝ := by
  classical
  exact if hy : y ∈ (extChartAt I α).target then
    (σ ⟨(extChartAt I α).symm y, (extChartAt I α).map_target hy⟩ : ℝ) • φ.inChartAt α y
  else 0

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem signedChartExpression_apply (φ : RoughForm I M ℝ k) (α : M)
    (σ : {x : M // x ∈ (extChartAt I α).source} → ℤˣ)
    (b : Module.Basis (Fin k) ℝ E) (y : E) :
    signedChartExpression φ α σ y b = φ.signedInChartAt b α σ y := by
  classical
  rw [signedInChartAt_apply]
  dsimp only [signedChartExpression]
  split_ifs <;> simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply]

/-- The actual signed chart integral does not depend on the chosen basis, even if neither
basis is positively oriented for the model orientation. -/
theorem integral_signedInChartAt_basis_eq (φ : RoughForm I M ℝ k)
    (o : Orientation ℝ E (Fin k)) (b b' : Module.Basis (Fin k) ℝ E) (α : M)
    (σ : {x : M // x ∈ (extChartAt I α).source} → ℤˣ) :
    (Orientation.signBasis o b : ℝ) * (∫ y, φ.signedInChartAt b α σ y ∂b.addHaar) =
      (Orientation.signBasis o b' : ℝ) * (∫ y, φ.signedInChartAt b' α σ y ∂b'.addHaar) := by
  simpa only [signedChartExpression_apply] using
    b.integral_signed_apply_eq o b' (signedChartExpression φ α σ)

/-- Genuine signed coefficient integrability is independent of the model basis and its
normalized Haar measure, without a regularity assumption on the form or chart sign. -/
theorem integrable_signedInChartAt_basis_iff (φ : RoughForm I M ℝ k)
    (b b' : Module.Basis (Fin k) ℝ E) (α : M)
    (σ : {x : M // x ∈ (extChartAt I α).source} → ℤˣ) :
    Integrable (φ.signedInChartAt b' α σ) b'.addHaar ↔
      Integrable (φ.signedInChartAt b α σ) b.addHaar := by
  simpa only [signedChartExpression_apply] using
    b.integrable_apply_basis_iff b' (signedChartExpression φ α σ)

end TauCeti.RoughForm
