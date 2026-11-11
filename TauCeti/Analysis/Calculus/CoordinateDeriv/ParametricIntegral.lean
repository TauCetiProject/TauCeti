/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.Calculus.CoordinateDeriv

/-!
# Differentiation under the integral sign in coordinates

For an integral `p ↦ ∫ F(p, θ) dθ` over `ℝⁿ` depending on a position and a frequency
`p ∈ ℝⁿ × ℝⁿ`, `TauCeti.differentiableAt_integral_and_fderiv_apply_eq_sum` differentiates under
the integral sign when the derivatives of the integrand on the coordinate vectors are known
functions `A j` and `B j`, continuous in `θ` and dominated near the base point by one integrable
function. The derivative of the integral on the coordinate vectors is then the integral of `A j`
and `B j`. The coefficient of the left symbol of an amplitude (`TauCeti.Amplitude.leftSymbol`) is
differentiated in this form.
-/

public section

open MeasureTheory

namespace TauCeti

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Differentiation under the integral sign** for `p ↦ ∫ F(p, θ) dθ` on `ℝⁿ × ℝⁿ`, when the
derivatives of the integrand on the coordinate vectors are `A j` and `B j`, continuous in `θ` and
dominated near `p₀` by one integrable function. -/
theorem differentiableAt_integral_and_fderiv_apply_eq_sum
    {F : CoordinateSpace n × CoordinateSpace n → CoordinateSpace n → E}
    {A B : Fin n → CoordinateSpace n × CoordinateSpace n → CoordinateSpace n → E}
    (hF : ∀ θ p, DifferentiableAt ℝ (F · θ) p)
    (hF' : ∀ θ p v, fderiv ℝ (F · θ) p v = ∑ j, v.1 j • A j p θ + ∑ j, v.2 j • B j p θ)
    (hFi : ∀ p, Integrable (F p)) (hAc : ∀ j p, Continuous (A j p))
    (hBc : ∀ j p, Continuous (B j p)) {g : CoordinateSpace n → ℝ} (hg : Integrable g)
    (p₀ : CoordinateSpace n × CoordinateSpace n)
    (hbound : ∀ θ, ∀ p ∈ Metric.ball p₀ 1, ∑ j, ‖A j p θ‖ + ∑ j, ‖B j p θ‖ ≤ g θ) :
    DifferentiableAt ℝ (fun p ↦ ∫ θ, F p θ) p₀ ∧ ∀ v, fderiv ℝ (fun p ↦ ∫ θ, F p θ) p₀ v =
      ∑ j, v.1 j • (∫ θ, A j p₀ θ) + ∑ j, v.2 j • ∫ θ, B j p₀ θ := by
  have hcont : Continuous fun θ ↦ fderiv ℝ (F · θ) p₀ := by
    refine continuous_clm_apply.2 fun v ↦ ?_
    simp only [hF']
    exact (continuous_finsetSum _ fun j _ ↦ (hAc j p₀).const_smul _).add
      (continuous_finsetSum _ fun j _ ↦ (hBc j p₀).const_smul _)
  have hnorm : ∀ θ, ∀ p ∈ Metric.ball p₀ 1, ‖fderiv ℝ (F · θ) p‖ ≤ g θ := fun θ p hp ↦
    ((fderiv ℝ (F · θ) p).opNorm_le_of_apply_eq_sum _ _ (hF' θ p)).trans (hbound θ p hp)
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds p₀ one_pos)
    (.of_forall fun p ↦ (hFi p).aestronglyMeasurable) (hFi p₀) hcont.aestronglyMeasurable
    (.of_forall fun θ p hp ↦ hnorm θ p hp) hg
    (.of_forall fun θ p _ ↦ (hF θ p).hasFDerivAt)
  refine ⟨h.differentiableAt, fun v ↦ ?_⟩
  have hmem := Metric.mem_ball_self (x := p₀) one_pos
  have hAi : ∀ j, Integrable (A j p₀) := fun j ↦ hg.mono' (hAc j p₀).aestronglyMeasurable
    (.of_forall fun θ ↦ ((Finset.single_le_sum (fun i _ ↦ norm_nonneg (A i p₀ θ))
      (Finset.mem_univ j)).trans (le_add_of_nonneg_right (by positivity))).trans
        (hbound θ p₀ hmem))
  have hBi : ∀ j, Integrable (B j p₀) := fun j ↦ hg.mono' (hBc j p₀).aestronglyMeasurable
    (.of_forall fun θ ↦ ((Finset.single_le_sum (fun i _ ↦ norm_nonneg (B i p₀ θ))
      (Finset.mem_univ j)).trans (le_add_of_nonneg_left (by positivity))).trans
        (hbound θ p₀ hmem))
  rw [h.fderiv, ContinuousLinearMap.integral_apply (hg.mono' hcont.aestronglyMeasurable
    (.of_forall fun θ ↦ hnorm θ p₀ hmem))]
  have hA' : ∀ j, Integrable fun θ ↦ v.1 j • A j p₀ θ := fun j ↦ (hAi j).smul _
  have hB' : ∀ j, Integrable fun θ ↦ v.2 j • B j p₀ θ := fun j ↦ (hBi j).smul _
  simp only [hF']
  rw [integral_add (integrable_finsetSum _ fun j _ ↦ hA' j)
    (integrable_finsetSum _ fun j _ ↦ hB' j), integral_finsetSum _ fun j _ ↦ hA' j,
    integral_finsetSum _ fun j _ ↦ hB' j]
  simp only [integral_smul]

end TauCeti
