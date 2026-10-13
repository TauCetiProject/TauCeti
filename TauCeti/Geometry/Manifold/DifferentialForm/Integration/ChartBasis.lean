/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Basis
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Chart

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

/-- The actual signed chart integral does not depend on the chosen basis, even if neither
basis is positively oriented for the model orientation. -/
theorem integral_signedInChartAt_basis_eq (φ : RoughForm I M ℝ k)
    (o : Orientation ℝ E (Fin k)) (b b' : Module.Basis (Fin k) ℝ E) (α : M)
    (σ : {x : M // x ∈ (extChartAt I α).source} → ℤˣ) :
    (Orientation.signBasis o b : ℝ) * (∫ y, φ.signedInChartAt b α σ y ∂b.addHaar) =
      (Orientation.signBasis o b' : ℝ) * (∫ y, φ.signedInChartAt b' α σ y ∂b'.addHaar) := by
  classical
  let ψ : E → E [⋀^Fin k]→L[ℝ] ℝ := fun y ↦
    if hy : y ∈ (extChartAt I α).target then
      (σ ⟨(extChartAt I α).symm y, (extChartAt I α).map_target hy⟩ : ℝ) • φ.inChartAt α y
    else 0
  have he (d : Module.Basis (Fin k) ℝ E) (y : E) :
      ψ y d = φ.signedInChartAt d α σ y := by
    rw [signedInChartAt_apply]
    dsimp only [ψ]
    split_ifs <;> simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul,
      ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  simpa only [he] using b.integral_signed_apply_eq o b' ψ

end TauCeti.RoughForm
