/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.UnifTight

/-!
# Uniform tightness under almost everywhere domination

* `MeasureTheory.UnifTight.ae_mono`: uniform tightness passes to families which are dominated
  almost everywhere in norm by a uniformly tight family.
* `MeasureTheory.tendsto_eLpNorm_comp_sub_comp_of_tendsto`: for a finite exponent, composing
  with a continuous map `P` satisfying `‖P x‖ ≤ ‖x‖` preserves `Lᵖ` convergence. The map need not
  be uniformly continuous or Lipschitz; by Vitali's convergence theorem, continuity together with
  the norm bound suffices.
-/

public section

namespace MeasureTheory

open scoped ENNReal

/-- Uniform tightness passes to families dominated almost everywhere in norm by a uniformly
tight family. -/
protected theorem UnifTight.ae_mono {α β ι : Type*} {m : MeasurableSpace α}
    [NormedAddCommGroup β] {μ : Measure α} {p : ℝ≥0∞} {f g : ι → α → β}
    (hg : UnifTight g p μ) (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ)
    (hfg : ∀ i, (‖f i ·‖ₑ) ≤ᵐ[μ] (‖g i ·‖ₑ)) : UnifTight f p μ := by
  intro ε hε
  obtain ⟨s, hs, hfinite, hbound⟩ := hg.exists_measurableSet_indicator hε.ne'
  refine ⟨s, hfinite.ne, fun n ↦ (eLpNorm_mono_enorm_ae
    ((hf_meas n).indicator hs.compl) ?_).trans (hbound n)⟩
  filter_upwards [hfg n] with x hx
  by_cases hxs : x ∈ sᶜ
  · simpa only [Set.indicator_of_mem hxs] using hx
  · simp only [Set.indicator_of_notMem hxs, enorm_zero, le_refl]

open Filter Topology in
/-- **Continuous maps of norm at most the identity preserve `Lᵖ` convergence.** Let
`1 ≤ p < ∞` and let `P` be continuous with `‖P x‖ ≤ ‖x‖`. If `f n → g` in `Lᵖ`, then
`P ∘ f n → P ∘ g` in `Lᵖ`. -/
theorem tendsto_eLpNorm_comp_sub_comp_of_tendsto {α β : Type*} {m : MeasurableSpace α}
    [NormedAddCommGroup β] {μ : Measure α} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) {P : β → β}
    (hP : Continuous P) (hPb : ∀ x, ‖P x‖ ≤ ‖x‖) {f : ℕ → α → β} {g : α → β}
    (hf : ∀ n, MemLp (f n) p μ) (hg : MemLp g p μ)
    (hfg : Tendsto (fun n ↦ eLpNorm (f n - g) p μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (P ∘ f n - P ∘ g) p μ) atTop (𝓝 0) := by
  have hmeas (n : ℕ) : AEStronglyMeasurable (P ∘ f n) μ :=
    hP.comp_aestronglyMeasurable (hf n).aestronglyMeasurable
  have hPg : MemLp (P ∘ g) p μ :=
    hg.mono (hP.comp_aestronglyMeasurable hg.aestronglyMeasurable)
      (Eventually.of_forall fun x ↦ hPb (g x))
  have hbound (n : ℕ) : ∀ᵐ x ∂μ, ‖(P ∘ f n) x‖ₑ ≤ ‖f n x‖ₑ :=
    Eventually.of_forall fun x ↦ enorm_le_iff_norm_le.2 (hPb (f n x))
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨hmeasure, hui, hut⟩ :=
    (tendstoInMeasure_iff_tendsto_Lp hp hp' (fun n ↦ hf (ns n)) hg).2 (hfg.comp hns)
  obtain ⟨ms, -, hae⟩ := hmeasure.exists_seq_tendsto_ae
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ (P ∘ f (ns (ms n))) x) atTop (𝓝 ((P ∘ g) x)) := by
    filter_upwards [hae] with x hx
    exact (hP.tendsto (g x)).comp hx
  exact ⟨ms, tendsto_Lp_of_tendsto_ae hp hp' (fun n ↦ hmeas (ns (ms n))) hPg
    ((hui.comp ms).ae_mono (fun n ↦ hmeas (ns (ms n))) fun n ↦ hbound (ns (ms n)))
    ((hut.comp ms).ae_mono (fun n ↦ hmeas (ns (ms n))) fun n ↦ hbound (ns (ms n))) hlim⟩

end MeasureTheory
