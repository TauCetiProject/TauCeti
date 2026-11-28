/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Operator.Orbit
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integration of operator fields with integrable orbits

For Banach spaces, an operator field whose every orbit is Bochner integrable
defines a bounded operator by integrating each orbit. This construction uses
the bounded orbit map into L¹ and the native L¹ integral. It does not require
strong measurability of the field in the operator-norm topology.

An integrable scalar majorant bounds its operator norm. If the field itself is
Bochner integrable in operator norm, the orbitwise integral agrees with that
Bochner integral.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*,
  Volume I, §1.1, for orbitwise measurable operator fields.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {S 𝕜 X Y : Type*} [MeasurableSpace S] {μ : Measure S} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
  [NormedSpace ℝ Y] [IsScalarTower ℝ 𝕜 Y]

/-- Integrate an operator field orbitwise. Integrability of each orbit suffices for
the resulting linear operator to be bounded, even on an arbitrary measure space. -/
noncomputable def orbitIntegralCLM (A : S → X →L[𝕜] Y)
    (hA : ∀ x, Integrable (fun s ↦ A s x) μ) : X →L[𝕜] Y :=
  (L1.integralCLM' 𝕜).comp
    (orbitLpCLM A (fun x ↦ memLp_one_iff_integrable.2 (hA x)))

/-- Evaluation of the orbitwise integral is the integral of the orbit. -/
@[simp]
theorem orbitIntegralCLM_apply (A : S → X →L[𝕜] Y)
    (hA : ∀ x, Integrable (fun s ↦ A s x) μ) (x : X) :
    orbitIntegralCLM A hA x = ∫ s, A s x ∂μ := by
  rw [orbitIntegralCLM, ContinuousLinearMap.comp_apply, ← L1.integral_eq',
    L1.integral_eq_integral]
  exact integral_congr_ae (coeFn_orbitLpCLM A _ x)

/-- The orbit formula uniquely determines the orbitwise integral operator. -/
theorem eq_orbitIntegralCLM_iff (A : S → X →L[𝕜] Y)
    (hA : ∀ x, Integrable (fun s ↦ A s x) μ) (T : X →L[𝕜] Y) :
    T = orbitIntegralCLM A hA ↔ ∀ x, T x = ∫ s, A s x ∂μ := by
  simp only [← orbitIntegralCLM_apply A hA, ContinuousLinearMap.ext_iff]

/-- Changing an operator field on orbitwise null sets preserves its integral.
The exceptional null set may depend on the vector. -/
theorem orbitIntegralCLM_congr (A B : S → X →L[𝕜] Y)
    (hA : ∀ x, Integrable (fun s ↦ A s x) μ)
    (hB : ∀ x, Integrable (fun s ↦ B s x) μ)
    (h : ∀ x, (fun s ↦ A s x) =ᵐ[μ] fun s ↦ B s x) :
    orbitIntegralCLM A hA = orbitIntegralCLM B hB := by
  ext x
  simp only [orbitIntegralCLM_apply]
  exact integral_congr_ae (h x)

/-- An integrable nonnegative majorant bounds the norm of the orbitwise integral. -/
theorem norm_orbitIntegralCLM_le (A : S → X →L[𝕜] Y)
    (hA : ∀ x, Integrable (fun s ↦ A s x) μ) {g : S → ℝ}
    (hg : Integrable g μ) (hg_nonneg : ∀ᵐ s ∂μ, 0 ≤ g s)
    (hbound : ∀ x, ∀ᵐ s ∂μ, ‖A s x‖ ≤ g s * ‖x‖) :
    ‖orbitIntegralCLM A hA‖ ≤ ∫ s, g s ∂μ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg_of_ae hg_nonneg)
  intro x
  rw [orbitIntegralCLM_apply, ← integral_mul_const]
  exact norm_integral_le_of_norm_le (hg.mul_const ‖x‖) (hbound x)

/-- For a Bochner integrable operator field, orbitwise integration agrees with the
Bochner integral in the operator-norm topology. -/
theorem orbitIntegralCLM_eq_integral (A : S → X →L[𝕜] Y) (hA : Integrable A μ) :
    orbitIntegralCLM A (fun x ↦ hA.apply_continuousLinearMap x) = ∫ s, A s ∂μ := by
  ext x
  rw [orbitIntegralCLM_apply]
  exact (ContinuousLinearMap.integral_apply hA x).symm

end TauCeti
