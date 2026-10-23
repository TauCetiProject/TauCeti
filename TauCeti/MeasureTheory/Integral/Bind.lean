/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Bochner integration against mixtures

The Bochner integral against `Measure.bind` is the iterated integral against its components.
Integrability is characterized by almost-everywhere component integrability and integrability
of the component absolute moments. The second-moment version supports covariance calculations
for probability mixtures.

These results use Mathlib's integration theory for kernel composition, with the mixing measure
viewed as a constant kernel. No finiteness assumptions on the measures are needed.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter

namespace MeasureTheory.Measure

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] {μ : Measure α} {K : α → Measure β} {f : β → E}

/-- Integrability against a mixture is equivalent to component integrability almost everywhere
and integrability of the component absolute moments. -/
theorem integrable_bind_iff (hK : Measurable K)
    (hf : AEStronglyMeasurable f (μ.bind K)) :
    Integrable f (μ.bind K) ↔
      (∀ᵐ a ∂μ, Integrable f (K a)) ∧ Integrable (fun a ↦ ∫ x, ‖f x‖ ∂K a) μ := by
  exact ProbabilityTheory.integrable_comp_iff
    (κ := Kernel.const Unit μ) (η := ⟨K, hK⟩) (a := ()) hf

/-- The integral against an almost-everywhere measurable mixture equals the iterated component
integral. -/
theorem integral_bind [NormedSpace ℝ E] (hK : AEMeasurable K μ)
    (hf : Integrable f (μ.bind K)) :
    ∫ x, f x ∂μ.bind K = ∫ a, ∫ x, f x ∂K a ∂μ := by
  let κ : Kernel α β := ⟨hK.mk K, hK.measurable_mk⟩
  have hKκ : K =ᵐ[μ] κ := hK.ae_eq_mk
  have hfκ : Integrable f (μ.bind κ) := by
    rwa [← bind_congr_right hKκ]
  calc
    ∫ x, f x ∂μ.bind K = ∫ x, f x ∂μ.bind κ := by rw [bind_congr_right hKκ]
    _ = ∫ a, ∫ x, f x ∂κ a ∂μ := by
      exact Kernel.integral_comp (κ := Kernel.const Unit μ) (η := κ) (a := ()) hfκ
    _ = ∫ a, ∫ x, f x ∂K a ∂μ := by
      apply integral_congr_ae
      filter_upwards [hKκ] with a ha
      rw [ha]

/-- Component expectations of an integrable observable are integrable under the mixing law. -/
theorem integrable_integral_bind [NormedSpace ℝ E] (hK : Measurable K)
    (hf : Integrable f (μ.bind K)) :
    Integrable (fun a ↦ ∫ x, f x ∂K a) μ := by
  exact hf.integral_comp (κ := Kernel.const Unit μ) (η := ⟨K, hK⟩) (a := ())

/-- A mixture has a finite second moment exactly when its components do almost everywhere
and their second moments are integrable under the mixing law. -/
theorem memLp_two_bind_iff (hK : Measurable K)
    (hf : AEStronglyMeasurable f (μ.bind K)) :
    MemLp f 2 (μ.bind K) ↔
      (∀ᵐ a ∂μ, MemLp f 2 (K a)) ∧
        Integrable (fun a ↦ ∫ x, ‖f x‖ ^ 2 ∂K a) μ := by
  refine (memLp_two_iff_integrable_sq_norm hf).trans ?_
  have hs : AEStronglyMeasurable (fun x ↦ ‖f x‖ ^ 2) (μ.bind K) := hf.norm.pow 2
  refine (integrable_bind_iff hK hs).trans ?_
  have hfae := hf.comp (κ := Kernel.const Unit μ) (η := ⟨K, hK⟩) (a := ())
  simp only [Real.norm_of_nonneg (sq_nonneg _)]
  exact and_congr (eventually_congr (hfae.mono fun a ha ↦
    (memLp_two_iff_integrable_sq_norm ha).symm)) Iff.rfl

end MeasureTheory.Measure
