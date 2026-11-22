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

The Bochner integral against `Measure.bind` of an observable integrable under the mixture is the
iterated integral against its components. The `L¹` seminorm of the component integrals is at most
that of the observable under the mixture. Integrability is characterized by almost-everywhere
component integrability and integrability of the component absolute moments. The second-moment
version supports covariance calculations for mixtures. The real mass of a measurable set is the
integral of its component real masses when those component masses are finite almost everywhere.

These results use Mathlib's integration theory for kernel composition, with the mixing measure
viewed as a constant kernel. The component family need only be almost everywhere measurable: it
agrees almost everywhere with a measurable modification, which is a kernel and has the same
mixture. No finiteness assumptions on the measures are needed.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter

namespace MeasureTheory.Measure

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] {μ : Measure α} {K : α → Measure β} {f : β → E}

/-- Integrability against a mixture is equivalent to component integrability almost everywhere
and integrability of the component absolute moments. -/
theorem integrable_bind_iff (hK : AEMeasurable K μ)
    (hf : AEStronglyMeasurable f (μ.bind K)) :
    Integrable f (μ.bind K) ↔
      (∀ᵐ a ∂μ, Integrable f (K a)) ∧ Integrable (fun a ↦ ∫ x, ‖f x‖ ∂K a) μ := by
  -- Replace `K` by a measurable modification, which is a kernel.
  let κ : Kernel α β := ⟨hK.mk K, hK.measurable_mk⟩
  have hKκ : K =ᵐ[μ] κ := hK.ae_eq_mk
  rw [bind_congr_right hKκ] at hf ⊢
  rw [Measure.integrable_comp_iff hf]
  refine and_congr (eventually_congr ?_) (integrable_congr ?_) <;>
    filter_upwards [hKκ] with a ha <;> rw [ha]

/-- The integral of an observable that is integrable against an almost-everywhere measurable mixture
equals the iterated component integral. -/
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

/-- The real mass of a measurable set under a mixture is the integral of its component
real masses. Only finiteness on the set is required of each component. -/
theorem bind_apply_real (hK : AEMeasurable K μ) {s : Set β} (hs : MeasurableSet s)
    (hKs : ∀ᵐ a ∂μ, K a s ≠ ⊤) :
    (μ.bind K).real s = ∫ a, (K a).real s ∂μ := by
  rw [measureReal_def, bind_apply hs hK]
  exact (integral_toReal ((Measure.measurable_coe hs).comp_aemeasurable hK)
    (hKs.mono fun _ h ↦ lt_top_iff_ne_top.mpr h)).symm

/-- If an observable is almost everywhere strongly measurable with respect to the mixture, then
its component Bochner integrals are almost everywhere strongly measurable with respect to the
mixing measure. -/
theorem aestronglyMeasurable_integral_bind [NormedSpace ℝ E] (hK : AEMeasurable K μ)
    (hf : AEStronglyMeasurable f (μ.bind K)) :
    AEStronglyMeasurable (fun a ↦ ∫ x, f x ∂K a) μ := by
  -- Replace `K` by a measurable modification, which is a kernel.
  let κ : Kernel α β := ⟨hK.mk K, hK.measurable_mk⟩
  have hKκ : K =ᵐ[μ] κ := hK.ae_eq_mk
  -- The mixture is the composition of `κ` with the constant kernel at `μ`, so Mathlib's
  -- `AEStronglyMeasurable.integral_kernel_comp` applies.
  rw [bind_congr_right hKκ, Measure.comp_eq_comp_const_apply] at hf
  have hκ := hf.integral_kernel_comp
  rw [Kernel.const_apply] at hκ
  refine hκ.congr ?_
  filter_upwards [hKκ] with a ha
  simp only [κ, Kernel.coe_mk, ha]

/-- The `L¹` seminorm of the component Bochner integrals of an observable against the mixing
measure is at most the `L¹` seminorm of the observable against the mixture. No measurability of
the observable and no bound on the component masses is needed: the `L¹` seminorm of a function
that is not almost everywhere strongly measurable is `∞`. -/
theorem eLpNorm_one_integral_bind_le [NormedSpace ℝ E] (hK : AEMeasurable K μ) :
    eLpNorm (fun a ↦ ∫ x, f x ∂K a) 1 μ ≤ eLpNorm f 1 (μ.bind K) := by
  by_cases hf : AEStronglyMeasurable f (μ.bind K)
  · rw [eLpNorm_one_eq_lintegral_eNorm (aestronglyMeasurable_integral_bind hK hf),
      eLpNorm_one_eq_lintegral_eNorm hf, lintegral_bind hK hf.eNorm]
    exact lintegral_mono fun a ↦ eNorm_integral_le_lintegral_eNorm _
  · rw [eLpNorm_of_not_aestronglyMeasurable hf]
    exact le_top

/-- If an observable is integrable against the mixture, then its component Bochner integrals are
integrable against the mixing measure. -/
theorem integrable_integral_bind [NormedSpace ℝ E] (hK : AEMeasurable K μ)
    (hf : Integrable f (μ.bind K)) :
    Integrable (fun a ↦ ∫ x, f x ∂K a) μ :=
  memLp_one_iff_integrable.mp <| memLp_iff.mpr <|
    (eLpNorm_one_integral_bind_le hK).trans_lt (memLp_one_iff_integrable.mpr hf).eLpNorm_lt_top

/-- A mixture has a finite second moment exactly when its components do almost everywhere
and their second moments are integrable under the mixing law. -/
theorem memLp_two_bind_iff (hK : AEMeasurable K μ)
    (hf : AEStronglyMeasurable f (μ.bind K)) :
    MemLp f 2 (μ.bind K) ↔
      (∀ᵐ a ∂μ, MemLp f 2 (K a)) ∧
        Integrable (fun a ↦ ∫ x, ‖f x‖ ^ 2 ∂K a) μ := by
  refine (memLp_two_iff_integrable_sq_norm hf).trans ?_
  have hs : AEStronglyMeasurable (fun x ↦ ‖f x‖ ^ 2) (μ.bind K) := hf.norm.pow 2
  refine (integrable_bind_iff hK hs).trans ?_
  -- Almost every component sees `f` as almost everywhere equal to its strongly measurable `mk`.
  have hfae : ∀ᵐ a ∂μ, AEStronglyMeasurable f (K a) := by
    filter_upwards [ae_ae_of_ae_bind hK hf.ae_eq_mk] with a ha
    exact ⟨hf.mk f, hf.stronglyMeasurable_mk, ha⟩
  simp only [Real.norm_of_nonneg (sq_nonneg _)]
  exact and_congr (eventually_congr (hfae.mono fun a ha ↦
    (memLp_two_iff_integrable_sq_norm ha).symm)) Iff.rfl

end MeasureTheory.Measure
