/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Chart.Basis

/-!
# Operations on signed chart coefficients

Signed coefficients respect addition and scalar localization of actual rough differential forms.
Reversing the chart signs reverses the coefficient, whereas simultaneously reversing the model
orientation and chart signs preserves the relative-basis coefficient integral.
-/

public section

noncomputable section

open MeasureTheory
open scoped Manifold

namespace TauCeti.RoughForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {k : ℕ}

/-- Signed coefficients commute with addition of actual forms. -/
theorem signedInChartAt_add (φ ψ : RoughForm I M ℝ k) (b : Module.Basis (Fin k) ℝ E)
    (α : M) (σ : {x : M // x ∈ (extChartAt I α).source} → ℤˣ) (y : E) :
    (φ + ψ).signedInChartAt b α σ y =
      φ.signedInChartAt b α σ y + ψ.signedInChartAt b α σ y := by
  classical
  simp only [signedInChartAt_apply]
  split_ifs <;> simp [inChartAt_add, mul_add]

/-- Scalar localization of a form commutes with the source-indexed signed coefficient. -/
theorem signedInChartAt_fun_smul (f : M → ℝ) (φ : RoughForm I M ℝ k)
    (b : Module.Basis (Fin k) ℝ E) (α : M)
    (σ : {x : M // x ∈ (extChartAt I α).source} → ℤˣ) (y : E) :
    signedInChartAt (I := I) (fun x ↦ f x • φ x) b α σ y =
      f ((extChartAt I α).symm y) * φ.signedInChartAt b α σ y := by
  classical
  simp only [signedInChartAt_apply]
  split_ifs
  · rw [inChartAt_fun_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    ring
  · simp

/-- Restriction of a form by an indicator restricts its signed coefficient to the corresponding
coordinate piece. This uses only the form values, so it also applies to discontinuous pieces. -/
theorem signedInChartAt_indicator (s : Set M) (φ : RoughForm I M ℝ k)
    (b : Module.Basis (Fin k) ℝ E) (α : M)
    (σ : {x : M // x ∈ (extChartAt I α).source} → ℤˣ) (y : E) :
    signedInChartAt (I := I) (fun x ↦ s.indicator (fun _ ↦ (1 : ℝ)) x • φ x) b α σ y =
      ((extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' s).indicator
        (φ.signedInChartAt b α σ) y := by
  classical
  rw [signedInChartAt_fun_smul]
  by_cases hy : y ∈ (extChartAt I α).target
  · by_cases hs : (extChartAt I α).symm y ∈ s
    · have hys : y ∈ (extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' s := ⟨hy, hs⟩
      rw [Set.indicator_of_mem hs, Set.indicator_of_mem hys, one_mul]
    · have hys : y ∉ (extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' s := fun h ↦ hs h.2
      rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hys, zero_mul]
  · have hz : φ.signedInChartAt b α σ y = 0 := by
      rw [signedInChartAt_apply, dite_eq_right hy]
    have hys : y ∉ (extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' s := fun h ↦ hy h.1
    rw [hz, mul_zero, Set.indicator_of_notMem hys]

/-- Reversing every chart sign reverses the actual coefficient. -/
theorem signedInChartAt_neg_sign (φ : RoughForm I M ℝ k) (b : Module.Basis (Fin k) ℝ E)
    (α : M) (σ : {x : M // x ∈ (extChartAt I α).source} → ℤˣ) (y : E) :
    φ.signedInChartAt b α (fun x ↦ -σ x) y = -φ.signedInChartAt b α σ y := by
  classical
  simp only [signedInChartAt_apply]
  split_ifs <;> simp

variable [MeasurableSpace E] [BorelSpace E]

/-- The actual relative-basis coefficient integral descends through simultaneous reversal of
model orientation and chart signs, including in dimension zero. -/
theorem integral_signedInChartAt_diagonal_flip (φ : RoughForm I M ℝ k)
    (o : Orientation ℝ E (Fin k)) (b : Module.Basis (Fin k) ℝ E) (α : M)
    (σ : {x : M // x ∈ (extChartAt I α).source} → ℤˣ) :
    (Orientation.signBasis (-o) b : ℝ) *
        (∫ y, φ.signedInChartAt b α (fun x ↦ -σ x) y ∂b.addHaar) =
      (Orientation.signBasis o b : ℝ) * (∫ y, φ.signedInChartAt b α σ y ∂b.addHaar) := by
  simp_rw [signedInChartAt_neg_sign]
  rw [integral_neg, Orientation.signBasis_neg]
  simp

end TauCeti.RoughForm
