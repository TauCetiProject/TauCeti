/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.MeasureTheory.Function.Lp.Translation

/-!
# Approximate identities acting on bounded functions

Translation is not continuous on `L^∞`, and an approximate identity `K_c = c⁻ⁿ K (c⁻¹ ·)` does not
converge to the identity in the `L^∞` norm. It does converge after integration against a fixed
integrable weight. This file proves the two statements of this kind needed to multiply limits of
bounded functions, for instance the low-frequency truncations of two bounded functions.

* **Weighted continuity of translation.** If `w` is integrable and `f` is essentially bounded, then
  `∫ |w(x)| ‖f(x + h) - f(x)‖ dx → 0` as `h → 0`
  (`MeasureTheory.tendsto_lintegral_eNorm_mul_eNorm_comp_add_sub`). Writing
  `w(x) (f(x + h) - f(x)) = (w(x) - w(x + h)) f(x + h) + ((w f)(x + h) - (w f)(x))` reduces this to
  the continuity of translation in `L¹` for the integrable functions `w` and `w f`.
* **Weighted convergence of an approximate identity.** If moreover `K` is integrable with
  `∫ K = 1`, then the averages `∫ K(s) f(x - c s) ds`, which are the convolutions of `f` with the
  dilates `K_c`, satisfy `∫ |w(x)| ‖∫ K(s) f(x - c s) ds - f(x)‖ dx → 0` as `c → 0`
  (`MeasureTheory.tendsto_lintegral_eNorm_mul_eNorm_integral_smul_comp_sub_smul_sub`). The kernel
  need not be nonnegative or compactly supported. Since `∫ K = 1`, the difference is
  `∫ K(s) (f(x - c s) - f(x)) ds`; Tonelli's theorem bounds the weighted integral by
  `∫ |K(s)| Φ(-c s) ds`, where `Φ(h)` is the quantity of the first statement, and dominated
  convergence finishes the proof.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Section 1.2 (approximate identities).
-/

public section

open Filter Topology Set
open scoped ENNReal

namespace MeasureTheory

variable {E F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

section Translation

variable [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddRightInvariant] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

/-- **Weighted continuity of translation for bounded functions.** If `w` is integrable and `f` is
essentially bounded, then `∫ |w(x)| ‖f(x + h) - f(x)‖ dx → 0` as `h → 0`. -/
theorem tendsto_lintegral_eNorm_mul_eNorm_comp_add_sub {w : E → ℂ} (hw : Integrable w μ)
    {f : E → F} (hf : AEStronglyMeasurable f μ) {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    Tendsto (fun h : E ↦ ∫⁻ x, ‖w x‖ₑ * ‖f (x + h) - f x‖ₑ ∂μ) (𝓝 0) (𝓝 0) := by
  have hwf : Integrable (w • f) μ := hw.smul_bdd C hf hC
  have h₁ := MemLp.tendsto_eLpNorm_comp_add_sub (memLp_one_iff_integrable.2 hw) le_rfl
    ENNReal.one_ne_top
  have h₂ := MemLp.tendsto_eLpNorm_comp_add_sub (memLp_one_iff_integrable.2 hwf) le_rfl
    ENNReal.one_ne_top
  have hlim : Tendsto (fun h : E ↦ ENNReal.ofReal C * eLpNorm (fun x ↦ w (x + h) - w x) 1 μ +
      eLpNorm (fun x ↦ (w • f) (x + h) - (w • f) x) 1 μ) (𝓝 0) (𝓝 0) := by
    simpa using (ENNReal.Tendsto.const_mul h₁ (Or.inr ENNReal.ofReal_ne_top)).add h₂
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ bot_le)
    fun h ↦ ?_
  -- `w(x) (f(x + h) - f(x)) = (w(x) - w(x + h)) f(x + h) + ((w f)(x + h) - (w f)(x))`.
  have hCh : ∀ᵐ x ∂μ, ‖f (x + h)‖ ≤ C :=
    (measurePreserving_add_right μ h).quasiMeasurePreserving.ae hC
  have hpt : ∀ᵐ x ∂μ, ‖w x‖ₑ * ‖f (x + h) - f x‖ₑ ≤
      ENNReal.ofReal C * ‖w (x + h) - w x‖ₑ + ‖(w • f) (x + h) - (w • f) x‖ₑ := by
    filter_upwards [hCh] with x hx
    have hsplit : w x • (f (x + h) - f x) =
        (w x - w (x + h)) • f (x + h) + ((w • f) (x + h) - (w • f) x) := by
      simp only [Pi.smul_apply', smul_sub, sub_smul]
      abel
    calc ‖w x‖ₑ * ‖f (x + h) - f x‖ₑ = ‖w x • (f (x + h) - f x)‖ₑ := (eNorm_smul _ _).symm
      _ ≤ ‖(w x - w (x + h)) • f (x + h)‖ₑ + ‖(w • f) (x + h) - (w • f) x‖ₑ := by
          rw [hsplit]
          exact eNorm_add_le _ _
      _ ≤ ENNReal.ofReal C * ‖w (x + h) - w x‖ₑ + ‖(w • f) (x + h) - (w • f) x‖ₑ := by
          gcongr
          rw [eNorm_smul, eNorm_sub_rev, mul_comm]
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal hx
  have hW : AEStronglyMeasurable (fun x ↦ w (x + h) - w x) μ :=
    (hw.aestronglyMeasurable.comp_measurePreserving (measurePreserving_add_right μ h)).sub
      hw.aestronglyMeasurable
  have hWF : AEStronglyMeasurable (fun x ↦ (w • f) (x + h) - (w • f) x) μ :=
    (hwf.aestronglyMeasurable.comp_measurePreserving (measurePreserving_add_right μ h)).sub
      hwf.aestronglyMeasurable
  have hmeas : AEMeasurable (fun x ↦ ‖w (x + h) - w x‖ₑ) μ := hW.eNorm
  calc ∫⁻ x, ‖w x‖ₑ * ‖f (x + h) - f x‖ₑ ∂μ
      ≤ ∫⁻ x, (ENNReal.ofReal C * ‖w (x + h) - w x‖ₑ +
          ‖(w • f) (x + h) - (w • f) x‖ₑ) ∂μ := lintegral_mono_ae hpt
    _ = ENNReal.ofReal C * eLpNorm (fun x ↦ w (x + h) - w x) 1 μ +
          eLpNorm (fun x ↦ (w • f) (x + h) - (w • f) x) 1 μ := by
        rw [lintegral_add_left' (hmeas.const_mul _), lintegral_const_mul'' _ hmeas,
          eLpNorm_one_eq_lintegral_eNorm hW, eLpNorm_one_eq_lintegral_eNorm hWF]

end Translation

section ApproximateIdentity

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Weighted convergence of an approximate identity on bounded functions.** Let `K` be
integrable with `∫ K = 1`, let `w` be integrable and let `f` be essentially bounded. Then the
averages `∫ K(s) f(x - c s) ds` of `f` against the dilates of `K` satisfy

`∫ |w(x)| ‖∫ K(s) f(x - c s) ds - f(x)‖ dx → 0` as `c → 0`, `c ≠ 0`. -/
theorem tendsto_lintegral_eNorm_mul_eNorm_integral_smul_comp_sub_smul_sub [CompleteSpace F]
    {K : E → ℂ} (hK : Integrable K μ) (hK1 : ∫ s, K s ∂μ = 1) {w : E → ℂ} (hw : Integrable w μ)
    {f : E → F} (hf : AEStronglyMeasurable f μ) {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    Tendsto (fun c : ℝ ↦ ∫⁻ x, ‖w x‖ₑ * ‖(∫ s, K s • f (x - c • s) ∂μ) - f x‖ₑ ∂μ)
      (𝓝[≠] 0) (𝓝 0) := by
  -- Replace `f` by a strongly measurable modification bounded everywhere, and `w` by a strongly
  -- measurable modification.
  set g := hf.mk f
  set f₀ : E → F := {x | ‖g x‖ ≤ C}.indicator g
  have hf₀m : StronglyMeasurable f₀ :=
    hf.stronglyMeasurable_mk.indicator (measurableSet_le hf.stronglyMeasurable_mk.norm.measurable
      measurable_const)
  have hff₀ : f =ᵐ[μ] f₀ := by
    filter_upwards [hf.ae_eq_mk, hC] with x hx hxC
    rw [hx]
    exact (indicator_of_mem (show x ∈ {x | ‖g x‖ ≤ C} by simpa [g, ← hx] using hxC) g).symm
  have hf₀C : ∀ x, ‖f₀ x‖ ≤ max C 0 := fun x ↦ by
    by_cases hx : ‖g x‖ ≤ C
    · rw [show f₀ x = g x from indicator_of_mem hx g]
      exact hx.trans (le_max_left _ _)
    · rw [show f₀ x = 0 from indicator_of_notMem hx g, norm_zero]
      exact le_max_right _ _
  set w₀ := hw.aestronglyMeasurable.mk w
  have hw₀m : StronglyMeasurable w₀ := hw.aestronglyMeasurable.stronglyMeasurable_mk
  have hww₀ : w =ᵐ[μ] w₀ := hw.aestronglyMeasurable.ae_eq_mk
  have hw₀ : Integrable w₀ μ := hw.congr hww₀
  set C' := max C 0
  -- `Φ h = ∫ |w₀(x)| ‖f₀(x + h) - f₀(x)‖ dx` tends to zero, and is bounded by `2 C' ∫ |w₀|`.
  set Φ : E → ℝ≥0∞ := fun h ↦ ∫⁻ x, ‖w₀ x‖ₑ * ‖f₀ (x + h) - f₀ x‖ₑ ∂μ
  have hΦ : Tendsto Φ (𝓝 0) (𝓝 0) := tendsto_lintegral_eNorm_mul_eNorm_comp_add_sub hw₀
    hf₀m.aestronglyMeasurable (Eventually.of_forall hf₀C)
  have hΦm : Measurable Φ := by
    refine Measurable.lintegral_prod_right' (f := fun p : E × E ↦ ‖w₀ p.2‖ₑ *
      ‖f₀ (p.2 + p.1) - f₀ p.2‖ₑ) ?_
    exact (hw₀m.comp_measurable measurable_snd).eNorm.mul
      ((hf₀m.comp_measurable (measurable_snd.add measurable_fst)).sub
        (hf₀m.comp_measurable measurable_snd)).eNorm
  set B : ℝ≥0∞ := ENNReal.ofReal (2 * C') * ∫⁻ x, ‖w₀ x‖ₑ ∂μ
  have hB : B ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hw₀.2.ne
  have hΦB : ∀ h, Φ h ≤ B := fun h ↦ by
    refine (lintegral_mono fun x ↦ ?_).trans_eq (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)
    rw [mul_comm (ENNReal.ofReal _)]
    gcongr
    refine (eNorm_sub_le).trans ?_
    have hC' : 0 ≤ C' := le_max_right C 0
    rw [two_mul, ENNReal.ofReal_add hC' hC']
    gcongr <;> rw [← ofReal_norm] <;> exact ENNReal.ofReal_le_ofReal (hf₀C _)
  -- Dominated convergence for `∫ |K(s)| Φ(-c s) ds`.
  have hDCT : Tendsto (fun c : ℝ ↦ ∫⁻ s, ‖K s‖ₑ * Φ (-(c • s)) ∂μ) (𝓝[≠] 0) (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence' (μ := μ) (l := 𝓝[≠] (0 : ℝ))
      (F := fun c s ↦ ‖K s‖ₑ * Φ (-(c • s))) (f := fun _ ↦ 0) (fun s ↦ ‖K s‖ₑ * B)
      (Eventually.of_forall fun c ↦ hK.aestronglyMeasurable.eNorm.mul
        (hΦm.comp (measurable_const_smul c).neg).aemeasurable)
      (Eventually.of_forall fun c ↦ Eventually.of_forall fun s ↦ by gcongr; exact hΦB _)
      (by rw [lintegral_mul_const' _ _ hB]; exact ENNReal.mul_ne_top hK.2.ne hB)
      (Eventually.of_forall fun s ↦ ?_)
    · simpa using h
    have hs : Tendsto (fun c : ℝ ↦ -(c • s)) (𝓝[≠] 0) (𝓝 0) := by
      have : Tendsto (fun c : ℝ ↦ -(c • s)) (𝓝 0) (𝓝 (-((0 : ℝ) • s))) :=
        ((continuous_id.smul continuous_const).neg).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    simpa using ENNReal.Tendsto.const_mul (hΦ.comp hs) (Or.inr eNorm_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hDCT
    (Eventually.of_forall fun _ ↦ bot_le) ?_
  filter_upwards [self_mem_nhdsWithin] with c (hc : c ≠ 0)
  -- For fixed `x`, the average of `f` equals that of `f₀`, since `s ↦ x - c s` preserves null sets.
  have hqmp : ∀ x, QuasiMeasurePreserving (fun s : E ↦ x - c • s) μ μ := fun x ↦ by
    have h := (measurePreserving_add_left μ x).quasiMeasurePreserving.comp
      (Measure.quasiMeasurePreserving_smul μ (neg_ne_zero.2 hc))
    convert h using 2 with s
    simp [sub_eq_add_neg, neg_smul]
  have havg : ∀ x, ∫ s, K s • f (x - c • s) ∂μ = ∫ s, K s • f₀ (x - c • s) ∂μ := fun x ↦
    integral_congr_ae <| by
      filter_upwards [(hqmp x).ae_eq_comp hff₀] with s hs
      simp only [Function.comp_apply] at hs
      rw [hs]
  -- Since `∫ K = 1`, the difference is `∫ K(s) (f₀(x - c s) - f₀(x)) ds`.
  have hdiff : ∀ x, (∫ s, K s • f₀ (x - c • s) ∂μ) - f₀ x =
      ∫ s, K s • (f₀ (x - c • s) - f₀ x) ∂μ := fun x ↦ by
    have hint : Integrable (fun s ↦ K s • f₀ (x - c • s)) μ :=
      hK.smul_bdd C' ((hf₀m.comp_measurable
        (measurable_const.sub (measurable_const_smul c))).aestronglyMeasurable)
        (Eventually.of_forall fun s ↦ hf₀C _)
    simp_rw [smul_sub]
    rw [integral_sub hint (hK.smul_const _), integral_smul_const, hK1, one_smul]
  have hmeas2 : AEMeasurable (Function.uncurry fun x s ↦
      ‖w₀ x‖ₑ * (‖K s‖ₑ * ‖f₀ (x - c • s) - f₀ x‖ₑ)) (μ.prod μ) :=
    (hw₀m.comp_measurable measurable_fst).eNorm.aemeasurable.mul
      ((hK.aestronglyMeasurable.eNorm.comp_snd).mul
        ((hf₀m.comp_measurable (measurable_fst.sub (measurable_snd.const_smul c))).sub
          (hf₀m.comp_measurable measurable_fst)).eNorm.aemeasurable)
  calc ∫⁻ x, ‖w x‖ₑ * ‖(∫ s, K s • f (x - c • s) ∂μ) - f x‖ₑ ∂μ
      = ∫⁻ x, ‖w₀ x‖ₑ * ‖∫ s, K s • (f₀ (x - c • s) - f₀ x) ∂μ‖ₑ ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hww₀, hff₀] with x hx hxf
        rw [hx, havg, hxf, hdiff]
    _ ≤ ∫⁻ x, ‖w₀ x‖ₑ * ∫⁻ s, ‖K s‖ₑ * ‖f₀ (x - c • s) - f₀ x‖ₑ ∂μ ∂μ := by
        refine lintegral_mono fun x ↦ ?_
        gcongr
        exact (eNorm_integral_le_lintegral_eNorm _).trans_eq (by simp_rw [eNorm_smul])
    _ = ∫⁻ x, ∫⁻ s, ‖w₀ x‖ₑ * (‖K s‖ₑ * ‖f₀ (x - c • s) - f₀ x‖ₑ) ∂μ ∂μ := by
        refine lintegral_congr fun x ↦ (lintegral_const_mul'' _ ?_).symm
        exact hK.aestronglyMeasurable.eNorm.mul
          ((hf₀m.comp_measurable (measurable_const.sub (measurable_const_smul c))).sub
            stronglyMeasurable_const).eNorm.aemeasurable
    _ = ∫⁻ s, ∫⁻ x, ‖w₀ x‖ₑ * (‖K s‖ₑ * ‖f₀ (x - c • s) - f₀ x‖ₑ) ∂μ ∂μ :=
        lintegral_lintegral_swap hmeas2
    _ = ∫⁻ s, ‖K s‖ₑ * Φ (-(c • s)) ∂μ := by
        refine lintegral_congr fun s ↦ ?_
        rw [← lintegral_const_mul' _ _ eNorm_ne_top]
        refine lintegral_congr fun x ↦ ?_
        rw [← sub_eq_add_neg]
        ring

end ApproximateIdentity

end MeasureTheory
