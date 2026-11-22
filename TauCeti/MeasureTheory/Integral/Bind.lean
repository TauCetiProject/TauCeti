/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import TauCeti.MeasureTheory.Integral.Bochner.Holder

/-!
# Bochner integration against mixtures

The Bochner integral against `Measure.bind` of an observable integrable under the mixture is the
iterated integral against its components. The `L¹` seminorm of the component integrals is at most
that of the observable under the mixture. More generally, if almost every component has mass at
most a constant `c`, then for `1 ≤ p` the `Lᵖ` seminorm of the component integrals is at most
`c ^ (1 - 1 / p)` times that of the observable under the mixture, so an observable in `Lᵖ` of the
mixture has its component integrals in `Lᵖ` of the mixing measure. An observable that is almost
everywhere strongly measurable, or in `Lᵖ`, with respect to the mixture is so with respect to
almost every component. For an observable that is almost everywhere strongly measurable with
respect to the mixture, integrability is characterized by almost-everywhere component
integrability and integrability of the component absolute moments, and square-integrability by
almost-everywhere component square-integrability and integrability of the component second
moments; the latter supports covariance calculations for mixtures. The real mass of a measurable
set is the integral of its component real masses when those component masses are finite almost
everywhere.

These results use Mathlib's integration theory for kernel composition, with the mixing measure
viewed as a constant kernel. The component family need only be almost everywhere measurable: it
agrees almost everywhere with a measurable modification, which is a kernel and has the same
mixture. Apart from the component mass bound in the `Lᵖ` estimate, no finiteness assumptions on
the measures are needed.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] {μ : Measure α} {K : α → Measure β} {f : β → E}

/-- An observable that is almost everywhere strongly measurable with respect to the mixture is
integrable against it exactly when it is integrable against almost every component and its
component absolute moments are integrable against the mixing measure. -/
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

/-- An observable that is almost everywhere strongly measurable with respect to the mixture is
almost everywhere strongly measurable with respect to almost every component. -/
theorem ae_aestronglyMeasurable_bind (hK : AEMeasurable K μ)
    (hf : AEStronglyMeasurable f (μ.bind K)) : ∀ᵐ a ∂μ, AEStronglyMeasurable f (K a) := by
  filter_upwards [ae_ae_of_ae_bind hK hf.ae_eq_mk] with a ha
  exact ⟨hf.mk f, hf.stronglyMeasurable_mk, ha⟩

/-- An observable that is almost everywhere strongly measurable with respect to the mixture is
square-integrable against it exactly when it is square-integrable against almost every component
and its component second moments are integrable against the mixing measure. -/
theorem memLp_two_bind_iff (hK : AEMeasurable K μ)
    (hf : AEStronglyMeasurable f (μ.bind K)) :
    MemLp f 2 (μ.bind K) ↔
      (∀ᵐ a ∂μ, MemLp f 2 (K a)) ∧
        Integrable (fun a ↦ ∫ x, ‖f x‖ ^ 2 ∂K a) μ := by
  refine (memLp_two_iff_integrable_sq_norm hf).trans ?_
  have hs : AEStronglyMeasurable (fun x ↦ ‖f x‖ ^ 2) (μ.bind K) := hf.norm.pow 2
  refine (integrable_bind_iff hK hs).trans ?_
  simp only [Real.norm_of_nonneg (sq_nonneg _)]
  exact and_congr (eventually_congr ((ae_aestronglyMeasurable_bind hK hf).mono fun a ha ↦
    (memLp_two_iff_integrable_sq_norm ha).symm)) Iff.rfl

/-- If an observable is in `Lᵖ` of the mixture, then it is in `Lᵖ` of almost every component. -/
theorem ae_memLp_bind {p : ℝ≥0∞} (hK : AEMeasurable K μ) (hf : MemLp f p (μ.bind K)) :
    ∀ᵐ a ∂μ, MemLp f p (K a) := by
  have hfae := ae_aestronglyMeasurable_bind hK hf.aestronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp0
  · exact hfae.mono fun a ha ↦ memLp_zero_iff_aestronglyMeasurable.mpr ha
  rcases eq_or_ne p ∞ with rfl | hp_top
  · -- An essential bound of `f` under the mixture bounds `f` under almost every component.
    filter_upwards [hfae, ae_ae_of_ae_bind hK (ae_le_eLpNormEssSup (f := f))] with a ha hb
    rw [memLp_iff, eLpNorm_exponent_top ha]
    exact (eLpNormEssSup_le_of_ae_eNorm_bound hb).trans_lt
      (eLpNorm_exponent_top hf.aestronglyMeasurable ▸ hf.eLpNorm_lt_top)
  · -- The `p`-th power of `‖f‖` is integrable under the mixture, so under almost every component.
    have hint := ((integrable_bind_iff hK (hf.aestronglyMeasurable.norm.aemeasurable.pow_const
      p.toReal).aestronglyMeasurable).mp (hf.integrable_norm_rpow hp0 hp_top)).1
    filter_upwards [hfae, hint] with a ha hia
    exact (integrable_norm_rpow_iff ha hp0 hp_top).mp hia

/-- `eLpNorm_integral_bind_le` for an observable that is almost everywhere strongly measurable
with respect to the mixture. -/
private theorem eLpNorm_integral_bind_le_of_aestronglyMeasurable [NormedSpace ℝ E] {p : ℝ≥0∞}
    (hp : 1 ≤ p) {c : ℝ≥0} (hK : AEMeasurable K μ) (hmass : ∀ᵐ a ∂μ, K a Set.univ ≤ c)
    (hf : AEStronglyMeasurable f (μ.bind K)) :
    eLpNorm (fun a ↦ ∫ x, f x ∂K a) p μ ≤
      (c : ℝ≥0∞) ^ (1 - p.toReal⁻¹) * eLpNorm f p (μ.bind K) := by
  have hmean := aestronglyMeasurable_integral_bind hK hf
  rcases eq_or_ne p ∞ with rfl | hp_top
  · -- An essential bound of `f` under the mixture bounds almost every component integral, up to
    -- the mass of the component.
    simp only [eLpNorm_exponent_top hmean, eLpNorm_exponent_top hf, ENNReal.toReal_top, inv_zero,
      sub_zero, ENNReal.rpow_one]
    refine eLpNormEssSup_le_of_ae_eNorm_bound ?_
    filter_upwards [hmass, ae_ae_of_ae_bind hK (ae_le_eLpNormEssSup (f := f))] with a hca ha
    calc ‖∫ x, f x ∂K a‖ₑ ≤ ∫⁻ x, ‖f x‖ₑ ∂K a := eNorm_integral_le_lintegral_eNorm _
      _ ≤ ∫⁻ _, eLpNormEssSup f (μ.bind K) ∂K a := lintegral_mono_ae ha
      _ = eLpNormEssSup f (μ.bind K) * K a Set.univ := lintegral_const _
      _ ≤ c * eLpNormEssSup f (μ.bind K) := by
          rw [mul_comm]
          exact mul_le_mul' hca le_rfl
  have hr : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp_top hp
  have hr0 : p.toReal ≠ 0 := (zero_lt_one.trans_le hr).ne'
  have hcr : (c : ℝ≥0∞) ^ (p.toReal - 1) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.2 hr) ENNReal.coe_ne_top
  -- Jensen's inequality under each component, integrated against the mixing measure.
  have hJ : ∫⁻ a, ‖∫ x, f x ∂K a‖ₑ ^ p.toReal ∂μ ≤
      (c : ℝ≥0∞) ^ (p.toReal - 1) * ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ.bind K := by
    rw [lintegral_bind hK (hf.eNorm.pow_const _), ← lintegral_const_mul' _ _ hcr]
    refine lintegral_mono_ae ?_
    filter_upwards [hmass] with a hca
    exact (TauCeti.enorm_integral_rpow_le_measure_univ_rpow_mul _ hr).trans
      (mul_le_mul' (ENNReal.rpow_le_rpow hca (sub_nonneg.2 hr)) le_rfl)
  -- Taking `p`-th roots turns the integrated bound into the bound on the seminorms.
  have hC : ENNReal.ofReal ((c : ℝ) ^ (1 - p.toReal⁻¹)) = (c : ℝ≥0∞) ^ (1 - p.toReal⁻¹) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg c.coe_nonneg (sub_nonneg.2 (inv_le_one_of_one_le₀ hr)),
      ENNReal.ofReal_coe_nnreal]
  rw [← hC]
  refine TauCeti.eLpNorm_le_eLpNorm_of_lintegral_rpow_le (by positivity) hp_top hmean ?_
  rwa [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), hC, ← ENNReal.rpow_mul,
    sub_mul, inv_mul_cancel₀ hr0, one_mul]

/-- If almost every component has mass at most `c`, then for `1 ≤ p` the `Lᵖ` seminorm of the
component Bochner integrals of an observable is at most `c ^ (1 - 1 / p)` times its `Lᵖ` seminorm
under the mixture. For `p = ∞` the factor is `c`. No measurability of the observable is needed:
the `Lᵖ` seminorm of a function that is not almost everywhere strongly measurable is `∞`. -/
theorem eLpNorm_integral_bind_le [NormedSpace ℝ E] {p : ℝ≥0∞} (hp : 1 ≤ p) {c : ℝ≥0}
    (hK : AEMeasurable K μ) (hmass : ∀ᵐ a ∂μ, K a Set.univ ≤ c) :
    eLpNorm (fun a ↦ ∫ x, f x ∂K a) p μ ≤
      (c : ℝ≥0∞) ^ (1 - p.toReal⁻¹) * eLpNorm f p (μ.bind K) := by
  by_cases hf : AEStronglyMeasurable f (μ.bind K)
  · exact eLpNorm_integral_bind_le_of_aestronglyMeasurable hp hK hmass hf
  rw [eLpNorm_of_not_aestronglyMeasurable hf]
  rcases eq_or_ne ((c : ℝ≥0∞) ^ (1 - p.toReal⁻¹)) 0 with h0 | h0
  · -- Then `c = 0`, so almost every component and component integral vanishes.
    have hc0 : (c : ℝ≥0∞) = 0 := by
      rcases ENNReal.rpow_eq_zero_iff.mp h0 with h | h
      · exact h.1
      · exact absurd h.1 ENNReal.coe_ne_top
    have hzero : (fun a ↦ ∫ x, f x ∂K a) =ᵐ[μ] 0 := by
      filter_upwards [hmass] with a ha
      have hKa : K a = 0 := Measure.measure_univ_eq_zero.mp (nonpos_iff_eq_zero.mp (hc0 ▸ ha))
      rw [hKa, integral_zero_measure, Pi.zero_apply]
    rw [eLpNorm_congr_ae hzero, eLpNorm_zero]
    exact zero_le
  · rw [ENNReal.mul_top h0]
    exact le_top

/-- If almost every component has mass at most `c`, then for `1 ≤ p` the component Bochner
integrals of an observable in `Lᵖ` of the mixture, with values in a real normed space, are in `Lᵖ`
of the mixing measure. -/
theorem memLp_integral_bind [NormedSpace ℝ E] {p : ℝ≥0∞} (hp : 1 ≤ p) {c : ℝ≥0}
    (hK : AEMeasurable K μ) (hmass : ∀ᵐ a ∂μ, K a Set.univ ≤ c) (hf : MemLp f p (μ.bind K)) :
    MemLp (fun a ↦ ∫ x, f x ∂K a) p μ := by
  have hexp : 0 ≤ 1 - p.toReal⁻¹ := by
    rcases eq_or_ne p ∞ with rfl | hp_top
    · simp
    · exact sub_nonneg.2 (inv_le_one_of_one_le₀ (by simpa using ENNReal.toReal_mono hp_top hp))
  exact memLp_iff.mpr <| (eLpNorm_integral_bind_le hp hK hmass).trans_lt
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hexp ENNReal.coe_ne_top) hf.eLpNorm_lt_top)

end MeasureTheory.Measure
