/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.OrientationLift

/-!
# Linearity of actual signed chart integrals

Signed chart coefficients commute with finite sums and constant scalar multiplication.
The actual orientation-lift chart integral is additive when its coefficients are integrable,
and homogeneous even for the total integral of an arbitrary rough form. All integrability
hypotheses refer to the actual signed coefficients in an explicitly supplied model basis.
-/

public section

noncomputable section

open MeasureTheory
open scoped Manifold

namespace TauCeti.RoughForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {k : ℕ}

/-- The zero form has zero signed coefficient, including outside the chart target. -/
@[simp]
theorem signedInChartAt_zero (b : Module.Basis (Fin k) ℝ E) (α : M)
    (σ : {x : M // x ∈ (extChartAt I α).source} → ℤˣ) (y : E) :
    (0 : RoughForm I M ℝ k).signedInChartAt b α σ y = 0 := by
  classical
  simp [signedInChartAt_apply]

/-- Constant scalar multiplication commutes with the actual signed chart coefficient. -/
theorem signedInChartAt_smul (c : ℝ) (φ : RoughForm I M ℝ k)
    (b : Module.Basis (Fin k) ℝ E) (α : M)
    (σ : {x : M // x ∈ (extChartAt I α).source} → ℤˣ) (y : E) :
    (c • φ).signedInChartAt b α σ y = c * φ.signedInChartAt b α σ y := by
  have heq : c • φ = (fun x ↦ c • φ x) := funext fun _ ↦ rfl
  rw [heq]
  exact signedInChartAt_fun_smul (fun _ ↦ c) φ b α σ y

/-- The signed coefficient of a finite sum of actual forms is the finite sum of coefficients. -/
theorem signedInChartAt_sum {ι : Type*} (φ : ι → RoughForm I M ℝ k) (s : Finset ι)
    (b : Module.Basis (Fin k) ℝ E) (α : M)
    (σ : {x : M // x ∈ (extChartAt I α).source} → ℤˣ) (y : E) :
    (∑ i ∈ s, φ i).signedInChartAt b α σ y = ∑ i ∈ s, (φ i).signedInChartAt b α σ y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [Finset.sum_insert hi, signedInChartAt_add, ih, Finset.sum_insert hi]

variable [MeasurableSpace E]

/-- Integrability of the actual signed coefficients is preserved by finite sums, for any measure. -/
theorem integrable_signedInChartAt_sum {ι : Type*} (φ : ι → RoughForm I M ℝ k) (s : Finset ι)
    (b : Module.Basis (Fin k) ℝ E) (α : M)
    (σ : {x : M // x ∈ (extChartAt I α).source} → ℤˣ) (μ : Measure E)
    (h : ∀ i ∈ s, Integrable ((φ i).signedInChartAt b α σ) μ) :
    Integrable ((∑ i ∈ s, φ i).signedInChartAt b α σ) μ := by
  have heq : (∑ i ∈ s, φ i).signedInChartAt b α σ =
      fun y ↦ ∑ i ∈ s, (φ i).signedInChartAt b α σ y :=
    funext (signedInChartAt_sum φ s b α σ)
  rw [heq]
  exact integrable_finsetSum s h

end TauCeti.RoughForm

namespace TauCeti.Manifold.OrientationLift

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {k : ℕ}

/-- The actual orientation-lift chart integral of zero is zero. -/
@[simp]
theorem chartIntegral_zero (l : OrientationLift I M (Fin k)) (α : M) :
    l.chartIntegral (0 : TauCeti.RoughForm I M ℝ k) α = 0 := by
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
  rw [chartIntegral_eq_integral l _ b α]
  simp_rw [TauCeti.RoughForm.signedInChartAt_zero]
  simp

/-- The actual chart integral is additive under integrability of its two signed coefficients. -/
theorem chartIntegral_add (l : OrientationLift I M (Fin k)) (b : Module.Basis (Fin k) ℝ E)
    (φ ψ : TauCeti.RoughForm I M ℝ k) (α : M)
    (hφ : Integrable (φ.signedInChartAt b α (fun x ↦ l.signAt α x)) b.addHaar)
    (hψ : Integrable (ψ.signedInChartAt b α (fun x ↦ l.signAt α x)) b.addHaar) :
    l.chartIntegral (φ + ψ) α = l.chartIntegral φ α + l.chartIntegral ψ α := by
  rw [chartIntegral_eq_integral l (φ + ψ) b α, chartIntegral_eq_integral l φ b α,
    chartIntegral_eq_integral l ψ b α]
  simp_rw [TauCeti.RoughForm.signedInChartAt_add]
  rw [integral_add hφ hψ, mul_add]

/-- Constant scalar multiplication commutes with the actual total chart integral, with no
integrability or regularity hypothesis. -/
theorem chartIntegral_smul (l : OrientationLift I M (Fin k)) (c : ℝ)
    (φ : TauCeti.RoughForm I M ℝ k) (α : M) :
    l.chartIntegral (c • φ) α = c * l.chartIntegral φ α := by
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
  rw [chartIntegral_eq_integral l (c • φ) b α, chartIntegral_eq_integral l φ b α]
  simp_rw [TauCeti.RoughForm.signedInChartAt_smul]
  rw [integral_const_mul]
  ring

/-- The actual lift chart integral of a finite sum is the sum of chart integrals when the
actual signed coefficients in the supplied basis are integrable. -/
theorem chartIntegral_sum {ι : Type*} (l : OrientationLift I M (Fin k))
    (b : Module.Basis (Fin k) ℝ E) (φ : ι → TauCeti.RoughForm I M ℝ k) (s : Finset ι) (α : M)
    (h : ∀ i ∈ s, Integrable ((φ i).signedInChartAt b α (fun x ↦ l.signAt α x)) b.addHaar) :
    l.chartIntegral (∑ i ∈ s, φ i) α = ∑ i ∈ s, l.chartIntegral (φ i) α := by
  rw [chartIntegral_eq_integral l _ b α]
  simp_rw [TauCeti.RoughForm.signedInChartAt_sum]
  rw [integral_finsetSum s h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ (chartIntegral_eq_integral l (φ i) b α).symm

end TauCeti.Manifold.OrientationLift
