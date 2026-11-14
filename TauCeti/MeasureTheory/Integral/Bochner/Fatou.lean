/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Fatou's lemma for real integrals

An almost everywhere limit along a countably generated filter of eventually nonnegative,
integrable functions whose integrals are frequently at most `D` is integrable, with integral
at most `D`. No dominating function is needed, so integrability of the limit is a conclusion.

## Main results

* `TauCeti.ae_nonneg_of_tendsto`: almost everywhere nonnegativity passes to the limit.
* `TauCeti.lintegral_ofReal_le_of_tendsto_of_integral_le`: the lower-integral bound.
* `TauCeti.integrable_of_tendsto_of_integral_le`: integrability of the limit.
* `TauCeti.integral_le_of_tendsto_of_integral_le`: the real-integral bound.
-/

public section

open Filter MeasureTheory
open scoped Topology

namespace TauCeti

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι}
  [l.IsCountablyGenerated] {F : ι → α → ℝ} {G : α → ℝ} {D : ℝ}

/-- An almost everywhere limit along a countably generated filter of frequently almost
everywhere nonnegative functions is almost everywhere nonnegative. -/
theorem ae_nonneg_of_tendsto (hF₀ : ∃ᶠ i in l, 0 ≤ᵐ[μ] F i)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ F i x) l (𝓝 (G x))) : 0 ≤ᵐ[μ] G := by
  obtain ⟨u, hu, h₀⟩ := exists_seq_forall_of_frequently hF₀
  filter_upwards [hlim, ae_all_iff.2 h₀] with x hx hx₀ using ge_of_tendsto' (hx.comp hu) hx₀

/-- Fatou's lemma for lower integrals: an almost everywhere limit of eventually nonnegative,
integrable real functions whose integrals are frequently at most `D` has lower integral at most
`ENNReal.ofReal D`. -/
theorem lintegral_ofReal_le_of_tendsto_of_integral_le (hF : ∀ᶠ i in l, Integrable (F i) μ)
    (hF₀ : ∀ᶠ i in l, 0 ≤ᵐ[μ] F i)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ F i x) l (𝓝 (G x)))
    (hD : ∃ᶠ i in l, ∫ x, F i x ∂μ ≤ D) :
    ∫⁻ x, ENNReal.ofReal (G x) ∂μ ≤ ENNReal.ofReal D := by
  obtain ⟨u, hu, h⟩ := exists_seq_forall_of_frequently (hD.and_eventually (hF.and hF₀))
  calc ∫⁻ x, ENNReal.ofReal (G x) ∂μ
      = ∫⁻ x, liminf (fun n ↦ ENNReal.ofReal (F (u n) x)) atTop ∂μ :=
        lintegral_congr_ae <| hlim.mono fun x hx ↦
          ((ENNReal.continuous_ofReal.tendsto _).comp (hx.comp hu)).liminf_eq.symm
    _ ≤ liminf (fun n ↦ ∫⁻ x, ENNReal.ofReal (F (u n) x) ∂μ) atTop :=
        lintegral_liminf_le' fun n ↦ (h n).2.1.aemeasurable.ennreal_ofReal
    _ ≤ ENNReal.ofReal D := liminf_le_of_frequently_le' <| .of_forall fun n ↦ by
        rw [← ofReal_integral_eq_lintegral_ofReal (h n).2.1 (h n).2.2]
        exact ENNReal.ofReal_le_ofReal (h n).1

/-- **Fatou's lemma for real integrals**, integrability: an almost everywhere limit along a
countably generated filter of eventually nonnegative, integrable functions whose integrals are
frequently at most `D` is integrable. -/
theorem integrable_of_tendsto_of_integral_le (hF : ∀ᶠ i in l, Integrable (F i) μ)
    (hF₀ : ∀ᶠ i in l, 0 ≤ᵐ[μ] F i)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ F i x) l (𝓝 (G x)))
    (hD : ∃ᶠ i in l, ∫ x, F i x ∂μ ≤ D) : Integrable G μ := by
  have : l.NeBot := (frequently_true_iff_neBot l).1 (hD.mono fun _ _ ↦ trivial)
  obtain ⟨u, hu, hFu⟩ := exists_seq_forall_of_frequently hF.frequently
  exact ⟨aestronglyMeasurable_of_tendsto_ae atTop (fun n ↦ (hFu n).aestronglyMeasurable)
      (hlim.mono fun x hx ↦ hx.comp hu),
    (hasFiniteIntegral_iff_ofReal (ae_nonneg_of_tendsto hF₀.frequently hlim)).2 <|
      (lintegral_ofReal_le_of_tendsto_of_integral_le hF hF₀ hlim hD).trans_lt
        ENNReal.ofReal_lt_top⟩

/-- **Fatou's lemma for real integrals**, integral bound: an almost everywhere limit along a
countably generated filter of eventually nonnegative, integrable functions whose integrals are
frequently at most `D` has integral at most `D`. -/
theorem integral_le_of_tendsto_of_integral_le (hF : ∀ᶠ i in l, Integrable (F i) μ)
    (hF₀ : ∀ᶠ i in l, 0 ≤ᵐ[μ] F i)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ F i x) l (𝓝 (G x)))
    (hD : ∃ᶠ i in l, ∫ x, F i x ∂μ ≤ D) : ∫ x, G x ∂μ ≤ D := by
  have : l.NeBot := (frequently_true_iff_neBot l).1 (hD.mono fun _ _ ↦ trivial)
  obtain ⟨i, hiD, hi₀⟩ := (hD.and_eventually hF₀).exists
  rw [integral_eq_lintegral_of_nonneg_ae (ae_nonneg_of_tendsto hF₀.frequently hlim)
    (integrable_of_tendsto_of_integral_le hF hF₀ hlim hD).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal ((integral_nonneg_of_ae hi₀).trans hiD)
    (lintegral_ofReal_le_of_tendsto_of_integral_le hF hF₀ hlim hD)

end TauCeti
