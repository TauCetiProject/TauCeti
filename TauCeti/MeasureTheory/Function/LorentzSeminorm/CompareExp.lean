/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.LorentzSeminorm.Basic

/-!
# Weak `Lᵖ`, secondary-exponent monotonicity, and indicator Lorentz gauges

This file establishes the distribution-function formulas for weak `Lᵖ` (`L^{p,∞}`), the sharp
embedding `L^{p,q₀} ⊆ L^{p,q₁}` for `0 < p < ∞` and `0 < q₀ ≤ q₁ ≤ ∞`, the exact Lorentz gauge of
indicator functions `c 1_A`, the degeneracy `L^{∞,q} = {0}` for `0 < q < ∞`, and the finiteness of
`∫₀ᵗ (‖f‖ₑ)*` for every `f ∈ L^{p,q}` with `1 < p ≤ ∞` and `q ≠ 0` (which places `L^{p,q}` inside
`L¹ + L^∞`).

## Main declarations

* `TauCeti.eLorentzNorm_top_eq_iSup_decreasingRearrangement`,
  `TauCeti.eLorentzNorm_top_eq_iSup_measure_lt`,
  `TauCeti.eLorentzNorm_top_eq_iSup_ofReal_measure_lt`, `TauCeti.eLorentzNorm_top_le_iff`:
  weak-`Lᵖ` formulas (`q = ∞`, `0 < p < ∞`) in terms of `(‖f‖ₑ)*` and `c μ{‖f‖ₑ > c} ^ (1 / p)`.
* `TauCeti.eLorentzNorm_le_of_le_exponent`, `TauCeti.MemLorentz.mono_exponent`: sharp secondary-
  exponent monotonicity `‖f‖_{L^{p,q₁}} ≤ (q₀ / p) ^ (1 / q₀ - 1 / q₁) ‖f‖_{L^{p,q₀}}`, yielding
  Chebyshev's inequality `TauCeti.eLorentzNorm_top_le_eLpNorm` at `q₀ = p`, `q₁ = ∞`.
* `TauCeti.eLorentzNorm_indicator_const`, `TauCeti.eLorentzNorm_indicator_const_top`: exact Lorentz
  gauge of `A.indicator (fun _ ↦ c)`.
* `TauCeti.memLorentz_top_left_iff`: `L^{∞,q} = {0}` up to null sets when `0 < q < ∞`.
* `TauCeti.setLIntegral_decreasingRearrangement_le_eLorentzNorm_top`,
  `TauCeti.MemLorentz.setLIntegral_decreasingRearrangement_lt_top`: bounding `∫₀ᵗ (‖f‖ₑ)*` by the
  weak-`Lᵖ` gauge for `1 < p ≤ ∞`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §1.3 (Proposition 1.3.1).
* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., GTM 249, Springer, 2014, §1.4
  (Propositions 1.4.5 and 1.4.10).
-/

public noncomputable section

open Filter MeasureTheory Measure Set Topology
open scoped ENNReal NNReal

namespace TauCeti

/-- Log-convexity between `q₀` and `∞` on an arbitrary measure space: for `0 < q₀ ≤ q₁ < ∞` and
`Φ : ℝ → ℝ≥0∞` a.e. strongly measurable,
`‖Φ‖_{q₁} ≤ ‖Φ‖_∞ ^ (1 - q₀ / q₁) * ‖Φ‖_{q₀} ^ (q₀ / q₁)`. -/
private theorem eLpNorm_le_eLpNorm_top_rpow_mul_rpow {ν : Measure ℝ} {Φ : ℝ → ℝ≥0∞}
    (hΦ : AEStronglyMeasurable Φ ν) {q₀ q₁ : ℝ≥0∞} (hq₀ : q₀ ≠ 0) (hq₁top : q₁ ≠ ∞)
    (hq : q₀ ≤ q₁) :
    eLpNorm Φ q₁ ν ≤
      eLpNorm Φ ∞ ν ^ (1 - q₀.toReal / q₁.toReal) *
        eLpNorm Φ q₀ ν ^ (q₀.toReal / q₁.toReal) := by
  have hq₀top : q₀ ≠ ∞ := (lt_of_le_of_lt hq hq₁top.lt_top).ne
  set r₀ := q₀.toReal
  set r₁ := q₁.toReal
  have hr₀ : 0 < r₀ := ENNReal.toReal_pos hq₀ hq₀top
  have hr₀₁ : r₀ ≤ r₁ := ENNReal.toReal_mono hq₁top hq
  have hr₁ : 0 < r₁ := hr₀.trans_le hr₀₁
  have hsub : 0 ≤ r₁ - r₀ := sub_nonneg.2 hr₀₁
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (hq₀.bot_lt.trans_le hq).ne' hq₁top hΦ,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hq₀ hq₀top hΦ, eLpNorm_exponent_top hΦ]
  simp only [eNorm_eq_self]
  have hint : ∫⁻ s, Φ s ^ r₁ ∂ν ≤
      eLpNormEssSup Φ ν ^ (r₁ - r₀) * ∫⁻ s, Φ s ^ r₀ ∂ν := by
    rw [← lintegral_const_mul'' _ (hΦ.aemeasurable.pow_const r₀)]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_le_eLpNormEssSup (f := Φ) (μ := ν)] with s hs
    simp only [eNorm_eq_self] at hs
    calc Φ s ^ r₁ = Φ s ^ (r₁ - r₀) * Φ s ^ r₀ := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ hsub hr₀.le, sub_add_cancel]
      _ ≤ eLpNormEssSup Φ ν ^ (r₁ - r₀) * Φ s ^ r₀ := by gcongr
  calc (∫⁻ s, Φ s ^ r₁ ∂ν) ^ (1 / r₁)
      ≤ (eLpNormEssSup Φ ν ^ (r₁ - r₀) * ∫⁻ s, Φ s ^ r₀ ∂ν) ^ (1 / r₁) :=
        ENNReal.rpow_le_rpow hint (by positivity)
    _ = eLpNormEssSup Φ ν ^ (1 - r₀ / r₁) *
          ((∫⁻ s, Φ s ^ r₀ ∂ν) ^ (1 / r₀)) ^ (r₀ / r₁) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        congr 2 <;> field_simp

/-- `∫_{0 < s ≤ t} s ^ (-r) ds = t ^ (1 - r) / (1 - r)` for `r < 1` and `t > 0`. -/
private theorem setLIntegral_Ioc_rpow_neg {r t : ℝ} (hr : r < 1) (ht : 0 < t) :
    ∫⁻ s in Ioc 0 t, ENNReal.ofReal (s ^ (-r)) =
      ENNReal.ofReal (t ^ (1 - r) / (1 - r)) := by
  have h1sub : 0 < 1 - r := sub_pos.2 hr
  rw [div_eq_inv_mul, ← setLIntegral_Ioc_rpow_multHaar h1sub ht]
  symm
  rw [← lintegral_indicator measurableSet_Ioc, lintegral_multHaar_eq_setLIntegral]
  have hcongr : EqOn
      (fun s ↦ ENNReal.ofReal s⁻¹ *
        (Ioc 0 t).indicator (fun s ↦ ENNReal.ofReal (s ^ (1 - r))) s)
      ((Ioc 0 t).indicator fun s ↦ ENNReal.ofReal (s ^ (-r))) (Ioi 0) := by
    intro s (hs : 0 < s)
    dsimp only
    by_cases hst : s ≤ t
    · rw [indicator_of_mem (mem_Ioc.2 ⟨hs, hst⟩), indicator_of_mem (mem_Ioc.2 ⟨hs, hst⟩),
        ← ENNReal.ofReal_mul (inv_nonneg.2 hs.le), ← Real.rpow_neg_one s, ← Real.rpow_add hs]
      ring_nf
    · have hnot : s ∉ Ioc 0 t := fun h ↦ hst (mem_Ioc.1 h).2
      simp [indicator_of_notMem hnot]
  rw [setLIntegral_congr_fun measurableSet_Ioi hcongr,
    setLIntegral_indicator measurableSet_Ioc, inter_eq_left.2 Ioc_subset_Ioi_self]

section ENorm

variable {α ε : Type*} {mα : MeasurableSpace α} {μ : Measure α}
  [TopologicalSpace ε] [ENorm ε] {f : α → ε} {p : ℝ≥0∞}

/-- **Weak-`Lᵖ` rearrangement formula.** For `0 < p < ∞` and an a.e. strongly measurable `f`,
`‖f‖_{L^{p,∞}(μ)} = ⨆ t > 0, t ^ (1 / p) (‖f‖ₑ)* t`. -/
theorem eLorentzNorm_top_eq_iSup_decreasingRearrangement (hf : AEStronglyMeasurable f μ)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    eLorentzNorm f p ∞ μ =
      ⨆ (t : ℝ) (_ : 0 < t),
        ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t := by
  set αr := p.toReal⁻¹
  have hα : 0 < αr := inv_pos.2 (ENNReal.toReal_pos hp0 hptop)
  set Φ : ℝ → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (t ^ αr) * μ.decreasingRearrangement (‖f ·‖ₑ) t
  rw [eLorentzNorm_eq_eLpNorm_multHaar hp0 hf,
    eLpNorm_exponent_top
      (measurable_ofReal_rpow_mul_decreasingRearrangement μ αr _).aestronglyMeasurable,
    eLpNormEssSup_eq_essSup_eNorm]
  simp only [eNorm_eq_self]
  refine le_antisymm (essSup_le_of_ae_le _ ?_) (iSup₂_le fun t₀ ht₀ ↦ ?_)
  · filter_upwards [ae_pos_multHaar] with t ht
    exact le_iSup₂_of_le t ht le_rfl
  · by_contra! hlt
    set M := essSup Φ multHaar
    have ht₀_pos : 0 < t₀ ^ αr := Real.rpow_pos_of_pos ht₀ αr
    set c := ENNReal.ofReal (t₀ ^ (-αr)) * M
    have hM_eq : essSup Φ multHaar = ENNReal.ofReal (t₀ ^ αr) * c := by
      dsimp [c, M]
      rw [← mul_assoc, ← ENNReal.ofReal_mul ht₀_pos.le, ← Real.rpow_add ht₀,
        add_neg_cancel, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
    have hc_lt : c < μ.decreasingRearrangement (‖f ·‖ₑ) t₀ := by
      by_contra! hle
      exact hlt.not_ge ((mul_le_mul_of_nonneg_left hle bot_le).trans_eq hM_eq.symm)
    rw [μ.lt_decreasingRearrangement_iff] at hc_lt
    -- Choose `t₁ > t₀` with `ofReal t₁ < μ {c < ‖f‖ₑ}`, so `M < Φ` on `[t₀, t₁)`.
    obtain ⟨t₁, ht₀₁, ht₁_lt⟩ : ∃ t₁, t₀ < t₁ ∧ ENNReal.ofReal t₁ < μ {y | c < ‖f y‖ₑ} := by
      rcases eq_or_ne (μ {y | c < ‖f y‖ₑ}) ∞ with htop | htop
      · exact ⟨t₀ + 1, by linarith, htop ▸ ENNReal.ofReal_lt_top⟩
      · have hlt_real := (ENNReal.ofReal_lt_iff_lt_toReal ht₀.le htop).1 hc_lt
        refine ⟨(t₀ + (μ {y | c < ‖f y‖ₑ}).toReal) / 2, by linarith, ?_⟩
        exact (ENNReal.ofReal_lt_iff_lt_toReal (by linarith) htop).2 (by linarith)
    have hpos_Ico : 0 < multHaar (Ico t₀ t₁) := by
      rw [multHaar_Ico ht₀ ht₀₁.le, ENNReal.ofReal_pos, sub_pos]
      exact Real.log_lt_log ht₀ ht₀₁
    refine hpos_Ico.ne' (measure_mono_null (fun s hs ↦ ?_) (ae_iff.1 (ENNReal.ae_le_essSup Φ)))
    rw [mem_ofPred_eq, not_le, hM_eq, mul_comm]
    have hcs : c < μ.decreasingRearrangement (‖f ·‖ₑ) s :=
      μ.lt_decreasingRearrangement_iff.2 ((ENNReal.ofReal_le_ofReal hs.2.le).trans_lt ht₁_lt)
    exact (ENNReal.mul_lt_mul_left (ENNReal.ofReal_pos.2 ht₀_pos).ne'
      ENNReal.ofReal_ne_top hcs).trans_le (by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right
        (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ht₀.le hs.1 hα.le)) bot_le)

private theorem iSup_decreasingRearrangement_eq_top_of_measure_eq_top {h : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hμtop : μ {y | c < h y} = ∞) {αr : ℝ} (hα : 0 < αr) :
    (⨆ (t : ℝ) (_ : 0 < t), ENNReal.ofReal (t ^ αr) * μ.decreasingRearrangement h t) = ∞ := by
  have hbound : ∀ n : ℕ, (n : ℝ≥0∞) * c ≤
      ⨆ (t : ℝ) (_ : 0 < t), ENNReal.ofReal (t ^ αr) * μ.decreasingRearrangement h t := fun n ↦ by
    set t := ((n : ℝ) + 1) ^ αr⁻¹
    have ht : 0 < t := Real.rpow_pos_of_pos (by positivity) _
    have hct : c < μ.decreasingRearrangement h t := by
      rw [μ.lt_decreasingRearrangement_iff, hμtop]
      exact ENNReal.ofReal_lt_top
    refine le_iSup₂_of_le t ht ?_
    have htα : ENNReal.ofReal (t ^ αr) = (n : ℝ≥0∞) + 1 := by
      dsimp [t]
      rw [← Real.rpow_mul (by positivity), inv_mul_cancel₀ hα.ne', Real.rpow_one,
        ENNReal.ofReal_add (Nat.cast_nonneg n) zero_le_one, ENNReal.ofReal_natCast,
        ENNReal.ofReal_one]
    exact (mul_le_mul_of_nonneg_right (htα ▸ le_self_add) bot_le).trans
      (mul_le_mul_of_nonneg_left hct.le bot_le)
  have htop : (⨆ n : ℕ, (n : ℝ≥0∞) * c) = ∞ := by
    rw [← ENNReal.iSup_mul, ENNReal.iSup_natCast, ENNReal.top_mul hc0]
  exact eq_top_iff.2 (htop ▸ iSup_le hbound)

/-- **Weak-`Lᵖ` distribution formula.** For `0 < p < ∞` and an a.e. strongly measurable `f`,
`‖f‖_{L^{p,∞}(μ)} = ⨆ c : ℝ≥0∞, c * μ {y | c < ‖f y‖ₑ} ^ (1 / p)`. -/
theorem eLorentzNorm_top_eq_iSup_measure_lt (hf : AEStronglyMeasurable f μ)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    eLorentzNorm f p ∞ μ =
      ⨆ c : ℝ≥0∞, c * μ {y | c < ‖f y‖ₑ} ^ p.toReal⁻¹ := by
  rw [eLorentzNorm_top_eq_iSup_decreasingRearrangement hf hp0 hptop]
  set αr := p.toReal⁻¹
  have hα : 0 < αr := inv_pos.2 (ENNReal.toReal_pos hp0 hptop)
  refine le_antisymm (iSup₂_le fun t ht ↦ ?_) (iSup_le fun c ↦ ?_)
  · rw [μ.decreasingRearrangement_def, ENNReal.mul_iSup]
    refine iSup_le fun c ↦ ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun htc ↦ le_iSup_of_le c ?_
    rw [mul_comm]
    gcongr
    rw [← ENNReal.ofReal_rpow_of_pos ht]
    exact ENNReal.rpow_le_rpow htc.le hα.le
  · rcases eq_or_ne c 0 with rfl | hc0
    · simp
    rcases eq_or_ne c ∞ with rfl | hctop
    · simp [ENNReal.zero_rpow_of_pos hα]
    rcases eq_or_ne (μ {y | c < ‖f y‖ₑ}) 0 with hμ0 | hμ0
    · simp [hμ0, ENNReal.zero_rpow_of_pos hα]
    rcases eq_or_ne (μ {y | c < ‖f y‖ₑ}) ∞ with hμtop | hμtop
    · rw [iSup_decreasingRearrangement_eq_top_of_measure_eq_top hc0 hμtop hα]
      exact le_top
    · -- Finite positive measure `m`: let `t ↑ m` along `Ioo 0 m`.
      set m := (μ {y | c < ‖f y‖ₑ}).toReal
      have hm_pos : 0 < m := ENNReal.toReal_pos hμ0 hμtop
      have hm_eq : ENNReal.ofReal m = μ {y | c < ‖f y‖ₑ} := ENNReal.ofReal_toReal hμtop
      have h_le : ∀ t ∈ Ioo 0 m, ENNReal.ofReal (t ^ αr) * c ≤
          ⨆ (s : ℝ) (_ : 0 < s),
            ENNReal.ofReal (s ^ αr) * μ.decreasingRearrangement (‖f ·‖ₑ) s := by
        rintro t ⟨ht0, htm⟩
        have hct : c < μ.decreasingRearrangement (‖f ·‖ₑ) t := by
          rw [μ.lt_decreasingRearrangement_iff, ← hm_eq]
          exact (ENNReal.ofReal_lt_ofReal_iff hm_pos).2 htm
        exact le_iSup₂_of_le t ht0 (mul_le_mul_of_nonneg_left hct.le bot_le)
      have htend : Tendsto (fun t : ℝ ↦ ENNReal.ofReal (t ^ αr) * c)
          (𝓝[<] m) (𝓝 (ENNReal.ofReal (m ^ αr) * c)) :=
        ENNReal.Tendsto.mul_const
          ((ENNReal.continuous_ofReal.continuousAt.comp
            (Real.continuousAt_rpow_const m αr (Or.inl hm_pos.ne'))).tendsto.mono_left
              nhdsWithin_le_nhds) (Or.inr hctop)
      have hlim := le_of_tendsto htend (eventually_of_mem (Ioo_mem_nhdsLT hm_pos) h_le)
      rwa [← hm_eq, ENNReal.ofReal_rpow_of_pos hm_pos, mul_comm c]

/-- **Weak-`Lᵖ` distribution formula over positive real levels.** For `0 < p < ∞` and an a.e.
strongly measurable `f`,
`‖f‖_{L^{p,∞}(μ)} = ⨆ r > 0, ENNReal.ofReal r * μ {y | ENNReal.ofReal r < ‖f y‖ₑ} ^ (1 / p)`. -/
theorem eLorentzNorm_top_eq_iSup_ofReal_measure_lt (hf : AEStronglyMeasurable f μ)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    eLorentzNorm f p ∞ μ =
      ⨆ (r : ℝ) (_ : 0 < r),
        ENNReal.ofReal r * μ {y | ENNReal.ofReal r < ‖f y‖ₑ} ^ p.toReal⁻¹ := by
  rw [eLorentzNorm_top_eq_iSup_measure_lt hf hp0 hptop]
  have hα : 0 < p.toReal⁻¹ := inv_pos.2 (ENNReal.toReal_pos hp0 hptop)
  refine le_antisymm (iSup_le fun c ↦ ?_)
    (iSup₂_le fun r _ ↦ le_iSup_of_le (ENNReal.ofReal r) le_rfl)
  rcases eq_or_ne c 0 with rfl | hc0
  · simp
  rcases eq_or_ne c ∞ with rfl | hctop
  · simp [ENNReal.zero_rpow_of_pos hα]
  refine le_iSup₂_of_le c.toReal (ENNReal.toReal_pos hc0 hctop) ?_
  rw [ENNReal.ofReal_toReal hctop]

/-- Weak-`Lᵖ` bound criterion: for `0 < p < ∞` and `f` a.e. strongly measurable,
`‖f‖_{L^{p,∞}} ≤ M` iff `c * μ {c < ‖f‖ₑ} ^ (1 / p) ≤ M` for all `c`. -/
theorem eLorentzNorm_top_le_iff {M : ℝ≥0∞} (hf : AEStronglyMeasurable f μ)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    eLorentzNorm f p ∞ μ ≤ M ↔
      ∀ c : ℝ≥0∞, c * μ {y | c < ‖f y‖ₑ} ^ p.toReal⁻¹ ≤ M := by
  rw [eLorentzNorm_top_eq_iSup_measure_lt hf hp0 hptop, iSup_le_iff]

private theorem rpow_mul_antitone_rpow_le_lintegral_multHaar {g : ℝ → ℝ≥0∞} (hg : Antitone g)
    {αr r₀ t : ℝ} (hα : 0 < αr) (hr₀ : 0 < r₀) (ht : 0 < t) :
    (ENNReal.ofReal (t ^ αr) * g t) ^ r₀ ≤
      ENNReal.ofReal (αr * r₀) *
        ∫⁻ s, (ENNReal.ofReal (s ^ αr) * g s) ^ r₀ ∂multHaar := by
  set β := αr * r₀
  have hβ : 0 < β := mul_pos hα hr₀
  have hint : ENNReal.ofReal (β⁻¹ * t ^ β) * (g t ^ r₀) ≤
      ∫⁻ s, (ENNReal.ofReal (s ^ αr) * g s) ^ r₀ ∂multHaar := by
    calc ENNReal.ofReal (β⁻¹ * t ^ β) * (g t ^ r₀)
        = (∫⁻ s in Ioc 0 t, ENNReal.ofReal (s ^ β) ∂multHaar) * (g t ^ r₀) := by
          rw [setLIntegral_Ioc_rpow_multHaar hβ ht]
      _ = ∫⁻ s in Ioc 0 t, ENNReal.ofReal (s ^ β) * (g t ^ r₀) ∂multHaar :=
          (lintegral_mul_const _ ((measurable_id.pow_const β).ennreal_ofReal)).symm
      _ ≤ _ := (setLIntegral_mono' measurableSet_Ioc fun s hs ↦ by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hr₀.le,
            ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hs.1 αr), ← Real.rpow_mul hs.1.le]
          gcongr
          exact hg hs.2).trans (setLIntegral_le_lintegral _ _)
  calc (ENNReal.ofReal (t ^ αr) * g t) ^ r₀
      = ENNReal.ofReal β * (ENNReal.ofReal (β⁻¹ * t ^ β) * (g t ^ r₀)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hr₀.le,
          ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos ht αr),
          ← Real.rpow_mul ht.le, ← mul_assoc, ← ENNReal.ofReal_mul hβ.le,
          mul_inv_cancel_left₀ hβ.ne']
    _ ≤ _ := by gcongr

/-- Endpoint case `q₁ = ∞`, `0 < q₀ < ∞` of secondary-exponent monotonicity. -/
private theorem eLorentzNorm_top_le_of_ne_top {q₀ : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    (hq₀0 : q₀ ≠ 0) (hq₀top : q₀ ≠ ∞) :
    eLorentzNorm f p ∞ μ ≤
      ENNReal.ofReal ((q₀.toReal / p.toReal) ^ q₀.toReal⁻¹) * eLorentzNorm f p q₀ μ := by
  have hr₀ : 0 < q₀.toReal := ENNReal.toReal_pos hq₀0 hq₀top
  have hα : 0 < p.toReal⁻¹ := inv_pos.2 (ENNReal.toReal_pos hp0 hptop)
  have hC0 : ENNReal.ofReal ((q₀.toReal / p.toReal) ^ q₀.toReal⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos
      (div_pos hr₀ (ENNReal.toReal_pos hp0 hptop)) _)).ne'
  by_cases hf : AEStronglyMeasurable f μ; swap
  · simp [eLorentzNorm_of_not_aestronglyMeasurable hf, ENNReal.mul_top hC0]
  rw [eLorentzNorm_top_eq_iSup_decreasingRearrangement hf hp0 hptop,
    eLorentzNorm_eq_eLpNorm_multHaar hp0 hf,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hq₀0 hq₀top
      (measurable_ofReal_rpow_mul_decreasingRearrangement μ _ _).aestronglyMeasurable]
  simp only [eNorm_eq_self]
  set r₀ := q₀.toReal
  set αr := p.toReal⁻¹
  have hβ : 0 < αr * r₀ := mul_pos hα hr₀
  have hβ_eq : αr * r₀ = q₀.toReal / p.toReal := by dsimp [αr, r₀]; ring
  refine iSup₂_le fun t ht ↦ ?_
  calc ENNReal.ofReal (t ^ αr) * μ.decreasingRearrangement (‖f ·‖ₑ) t
      = ((ENNReal.ofReal (t ^ αr) * μ.decreasingRearrangement (‖f ·‖ₑ) t) ^ r₀) ^ (1 / r₀) := by
        rw [← ENNReal.rpow_mul, one_div, mul_inv_cancel₀ hr₀.ne', ENNReal.rpow_one]
    _ ≤ (ENNReal.ofReal (αr * r₀) *
          ∫⁻ s, (ENNReal.ofReal (s ^ αr) *
            μ.decreasingRearrangement (‖f ·‖ₑ) s) ^ r₀ ∂multHaar) ^ (1 / r₀) :=
        ENNReal.rpow_le_rpow
          (rpow_mul_antitone_rpow_le_lintegral_multHaar
            (μ.antitone_decreasingRearrangement _) hα hr₀ ht) (by positivity)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.ofReal_rpow_of_pos hβ, hβ_eq, one_div]

/-- **Monotonicity of Lorentz spaces in the secondary exponent** (Bergh–Löfström Proposition 1.3.1):
for `0 < p < ∞` and `0 < q₀ ≤ q₁ ≤ ∞`,
`‖f‖_{L^{p,q₁}(μ)} ≤ (q₀ / p) ^ (1 / q₀ - 1 / q₁) ‖f‖_{L^{p,q₀}(μ)}`. -/
theorem eLorentzNorm_le_of_le_exponent {q₀ q₁ : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    (hq₀ : q₀ ≠ 0) (hq : q₀ ≤ q₁) :
    eLorentzNorm f p q₁ μ ≤
      ENNReal.ofReal ((q₀.toReal / p.toReal) ^ (q₀.toReal⁻¹ - q₁.toReal⁻¹)) *
        eLorentzNorm f p q₀ μ := by
  rcases eq_or_ne q₁ ∞ with rfl | hq₁top
  · rcases eq_or_ne q₀ ∞ with rfl | hq₀top
    · simp
    · simpa using eLorentzNorm_top_le_of_ne_top (f := f) (μ := μ) hp0 hptop hq₀ hq₀top
  have hq₀top : q₀ ≠ ∞ := (lt_of_le_of_lt hq hq₁top.lt_top).ne
  have hr₀ : 0 < q₀.toReal := ENNReal.toReal_pos hq₀ hq₀top
  have hr₀₁ : q₀.toReal ≤ q₁.toReal := ENNReal.toReal_mono hq₁top hq
  have hr₁ : 0 < q₁.toReal := hr₀.trans_le hr₀₁
  have hpos_div : 0 < q₀.toReal / p.toReal := div_pos hr₀ (ENNReal.toReal_pos hp0 hptop)
  have hC0 : ENNReal.ofReal ((q₀.toReal / p.toReal) ^ (q₀.toReal⁻¹ - q₁.toReal⁻¹)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hpos_div _)).ne'
  by_cases hf : AEStronglyMeasurable f μ; swap
  · simp [eLorentzNorm_of_not_aestronglyMeasurable hf, ENNReal.mul_top hC0]
  have hlog : eLorentzNorm f p q₁ μ ≤
      eLorentzNorm f p ∞ μ ^ (1 - q₀.toReal / q₁.toReal) *
        eLorentzNorm f p q₀ μ ^ (q₀.toReal / q₁.toReal) := by
    rw [eLorentzNorm_eq_eLpNorm_multHaar hp0 hf, eLorentzNorm_eq_eLpNorm_multHaar hp0 hf,
      eLorentzNorm_eq_eLpNorm_multHaar hp0 hf]
    exact eLpNorm_le_eLpNorm_top_rpow_mul_rpow
      (measurable_ofReal_rpow_mul_decreasingRearrangement μ _ _).aestronglyMeasurable hq₀ hq₁top hq
  have h1 : 0 ≤ 1 - q₀.toReal / q₁.toReal := sub_nonneg.2 ((div_le_one hr₁).2 hr₀₁)
  have h2 : 0 ≤ q₀.toReal / q₁.toReal := div_nonneg hr₀.le hr₁.le
  calc eLorentzNorm f p q₁ μ
      ≤ (ENNReal.ofReal ((q₀.toReal / p.toReal) ^ q₀.toReal⁻¹) *
          eLorentzNorm f p q₀ μ) ^ (1 - q₀.toReal / q₁.toReal) *
          eLorentzNorm f p q₀ μ ^ (q₀.toReal / q₁.toReal) := by
        refine hlog.trans ?_
        gcongr
        exact eLorentzNorm_top_le_of_ne_top hp0 hptop hq₀ hq₀top
    _ = ENNReal.ofReal ((q₀.toReal / p.toReal) ^ q₀.toReal⁻¹) ^ (1 - q₀.toReal / q₁.toReal) *
          (eLorentzNorm f p q₀ μ ^ (1 - q₀.toReal / q₁.toReal) *
            eLorentzNorm f p q₀ μ ^ (q₀.toReal / q₁.toReal)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ h1, mul_assoc]
    _ = _ := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ h1 h2, sub_add_cancel, ENNReal.rpow_one,
          ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hpos_div _),
          ← Real.rpow_mul hpos_div.le]
        congr 3
        field_simp

/-- **Secondary-exponent inclusion `L^{p,q₀} ⊆ L^{p,q₁}`** for `0 < p < ∞` and `0 < q₀ ≤ q₁ ≤ ∞`. -/
theorem MemLorentz.mono_exponent {q₀ q₁ : ℝ≥0∞} (hf : MemLorentz f p q₀ μ)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) (hq₀ : q₀ ≠ 0) (hq : q₀ ≤ q₁) :
    MemLorentz f p q₁ μ :=
  memLorentz_iff.2 <| (eLorentzNorm_le_of_le_exponent hp0 hptop hq₀ hq).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLorentzNorm_lt_top)

/-- An antitone function on `ℝ` with finite `multHaar` integral vanishes on `(0, ∞)`, since
`multHaar [t e⁻ⁿ, t] = n` for all `n : ℕ`. -/
private theorem eq_zero_of_lintegral_antitone_multHaar_lt_top {g : ℝ → ℝ≥0∞} (hg : Antitone g)
    (hfin : ∫⁻ s, g s ∂multHaar < ∞) {t : ℝ} (ht : 0 < t) : g t = 0 := by
  by_contra hc
  have hbound : ∀ n : ℕ, (n : ℝ≥0∞) * g t ≤ ∫⁻ s, g s ∂multHaar := fun n ↦ by
    set a := t * Real.exp (-(n : ℝ))
    have ha : 0 < a := mul_pos ht (Real.exp_pos _)
    have hat : a ≤ t := mul_le_of_le_one_right ht.le
      (Real.exp_le_one_iff.2 (neg_nonpos.2 (Nat.cast_nonneg n)))
    have hmeas : multHaar (Icc a t) = n := by
      rw [multHaar_Icc ha hat, Real.log_mul ht.ne' (Real.exp_pos _).ne', Real.log_exp]
      ring_nf
      exact ENNReal.ofReal_natCast n
    calc (n : ℝ≥0∞) * g t = ∫⁻ _ in Icc a t, g t ∂multHaar := by
          rw [setLIntegral_const, hmeas, mul_comm]
      _ ≤ ∫⁻ s in Icc a t, g s ∂multHaar :=
          setLIntegral_mono' measurableSet_Icc fun s hs ↦ hg hs.2
      _ ≤ _ := setLIntegral_le_lintegral _ _
  have htop_iSup : (⨆ n : ℕ, (n : ℝ≥0∞) * g t) = ∞ := by
    rw [← ENNReal.iSup_mul, ENNReal.iSup_natCast, ENNReal.top_mul hc]
  exact hfin.ne (eq_top_iff.2 (htop_iSup ▸ iSup_le hbound))

/-- **Degeneracy of `L^{∞,q}` for `0 < q < ∞`:** because `∫₀ᵗ ds / s = ∞` for every `t > 0`, a
function has finite `(∞, q)` Lorentz gauge (`0 < q < ∞`) if and only if it is a.e. strongly
measurable and `‖f‖ₑ = 0` almost everywhere. -/
theorem memLorentz_top_left_iff {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqtop : q ≠ ∞) :
    MemLorentz f ∞ q μ ↔ AEStronglyMeasurable f μ ∧ (‖f ·‖ₑ) =ᵐ[μ] 0 := by
  constructor
  · intro hf
    have hfm := hf.aestronglyMeasurable
    refine ⟨hfm, ?_⟩
    have hr : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
    have hfin : ∫⁻ s, μ.decreasingRearrangement (‖f ·‖ₑ) s ^ q.toReal ∂multHaar < ∞ := by
      have hlt := hf.eLorentzNorm_lt_top
      rw [eLorentzNorm_eq_eLpNorm_multHaar ENNReal.top_ne_zero hfm] at hlt
      simp only [ENNReal.toReal_top, inv_zero, Real.rpow_zero, ENNReal.ofReal_one, one_mul] at hlt
      exact lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top hq0 hqtop hlt
    have h_antitone : Antitone fun s ↦ μ.decreasingRearrangement (‖f ·‖ₑ) s ^ q.toReal :=
      fun _ _ hab ↦ ENNReal.rpow_le_rpow (μ.antitone_decreasingRearrangement _ hab) hr.le
    have h_ae : μ.decreasingRearrangement (‖f ·‖ₑ) =ᵐ[volume.restrict (Ioi 0)] 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hpow0 := eq_zero_of_lintegral_antitone_multHaar_lt_top h_antitone hfin ht
      exact ((ENNReal.rpow_eq_zero_iff.1 hpow0).resolve_right fun h2 ↦ hr.not_gt h2.2).1
    have hess : essSup (‖f ·‖ₑ) μ = 0 := by
      rw [← μ.essSup_decreasingRearrangement, essSup_congr_ae h_ae]
      simp
    exact ENNReal.essSup_eq_zero_iff.1 hess
  · rintro ⟨hfm, h0⟩
    rw [memLorentz_iff, eLorentzNorm_eq_eLpNorm_multHaar ENNReal.top_ne_zero hfm]
    have hrear : ∀ t, μ.decreasingRearrangement (‖f ·‖ₑ) t = 0 := fun t ↦ by
      rw [μ.decreasingRearrangement_congr_ae h0]
      exact le_antisymm (μ.decreasingRearrangement_le_iff.2 (by simp)) bot_le
    simp [hrear]

end ENorm

section ContinuousENorm

variable {α ε : Type*} {mα : MeasurableSpace α} {μ : Measure α}
  [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε} {p : ℝ≥0∞}

/-- **Chebyshev's inequality in Lorentz form:** `‖f‖_{L^{p,∞}} ≤ ‖f‖_{Lᵖ}` for every
`p ∈ [0, ∞]`. -/
theorem eLorentzNorm_top_le_eLpNorm (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm f p ∞ μ ≤ eLpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ; swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hf]
    exact le_top
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [hf]
  rcases eq_or_ne p ∞ with rfl | hptop
  · rw [eLorentzNorm_self]
  calc eLorentzNorm f p ∞ μ
      ≤ ENNReal.ofReal ((p.toReal / p.toReal) ^ (p.toReal⁻¹ - (∞ : ℝ≥0∞).toReal⁻¹)) *
          eLorentzNorm f p p μ :=
        eLorentzNorm_le_of_le_exponent hp0 hptop hp0 le_top
    _ = eLpNorm f p μ := by
        rw [div_self (ENNReal.toReal_pos hp0 hptop).ne', Real.one_rpow, ENNReal.ofReal_one,
          one_mul, eLorentzNorm_self]

theorem _root_.MeasureTheory.MemLp.memLorentz_top (hf : MemLp f p μ) :
    MemLorentz f p ∞ μ :=
  memLorentz_iff.2 ((eLorentzNorm_top_le_eLpNorm f p μ).trans_lt hf.eLpNorm_lt_top)

/-- **Integrating the decreasing rearrangement against a weak-`Lᵖ` bound:** for `1 < p ≤ ∞` and
`t ≥ 0`,
`∫₀ᵗ (‖f‖ₑ)* ≤ (t ^ (1 - 1 / p) / (1 - 1 / p)) * ‖f‖_{L^{p,∞}(μ)}`.
In particular, every function in `L^{p,q}(μ)` (`1 < p ≤ ∞`, `q ≠ 0`) has `∫₀ᵗ (‖f‖ₑ)* < ∞`, so
it decomposes into `L¹(μ) + L^∞(μ)`. -/
theorem setLIntegral_decreasingRearrangement_le_eLorentzNorm_top (f : α → ε) {p : ℝ≥0∞}
    (hp : 1 < p) {t : ℝ} (ht : 0 ≤ t) (μ : Measure α) :
    ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s ≤
      ENNReal.ofReal (t ^ (1 - p.toReal⁻¹) / (1 - p.toReal⁻¹)) *
        eLorentzNorm f p ∞ μ := by
  obtain rfl | ht := ht.eq_or_lt
  · simp
  have h_inv_lt : p.toReal⁻¹ < 1 := by
    rcases eq_or_ne p ∞ with rfl | hptop
    · simp
    · exact inv_lt_one_of_one_lt₀
        (by simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hptop).2 hp)
  have hC0 : ENNReal.ofReal (t ^ (1 - p.toReal⁻¹) / (1 - p.toReal⁻¹)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (div_pos (Real.rpow_pos_of_pos ht _) (sub_pos.2 h_inv_lt))).ne'
  by_cases hf : AEStronglyMeasurable f μ; swap
  · rw [eLorentzNorm_of_not_aestronglyMeasurable hf, ENNReal.mul_top hC0]
    exact le_top
  rcases eq_or_ne p ∞ with rfl | hptop
  · simp only [ENNReal.toReal_top, inv_zero, sub_zero, Real.rpow_one, div_one,
      eLorentzNorm_self, eLpNorm_exponent_top hf, eLpNormEssSup_eq_essSup_eNorm]
    calc ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s
        ≤ ∫⁻ _ in Ioc 0 t, essSup (‖f ·‖ₑ) μ := by
          refine setLIntegral_mono' measurableSet_Ioc fun s hs ↦ ?_
          rw [← μ.decreasingRearrangement_zero (‖f ·‖ₑ)]
          exact μ.antitone_decreasingRearrangement _ hs.1.le
      _ = ENNReal.ofReal t * essSup (‖f ·‖ₑ) μ := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  set M := eLorentzNorm f p ∞ μ
  have hpoint : ∀ s ∈ Ioc 0 t,
      μ.decreasingRearrangement (‖f ·‖ₑ) s ≤ ENNReal.ofReal (s ^ (-p.toReal⁻¹)) * M := by
    intro s hs
    have hle : ENNReal.ofReal (s ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) s ≤ M := by
      dsimp [M]
      rw [eLorentzNorm_top_eq_iSup_decreasingRearrangement hf hp0 hptop]
      exact le_iSup₂_of_le s hs.1 le_rfl
    calc μ.decreasingRearrangement (‖f ·‖ₑ) s
        = ENNReal.ofReal (s ^ (-p.toReal⁻¹)) *
            (ENNReal.ofReal (s ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) s) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.1.le _),
            ← Real.rpow_add hs.1, neg_add_cancel, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (s ^ (-p.toReal⁻¹)) * M := by gcongr
  calc ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s
      ≤ ∫⁻ s in Ioc 0 t, ENNReal.ofReal (s ^ (-p.toReal⁻¹)) * M :=
        setLIntegral_mono' measurableSet_Ioc hpoint
    _ = (∫⁻ s in Ioc 0 t, ENNReal.ofReal (s ^ (-p.toReal⁻¹))) * M :=
        lintegral_mul_const _ (measurable_id.pow_const _).ennreal_ofReal
    _ = _ := by rw [setLIntegral_Ioc_rpow_neg h_inv_lt ht]

/-- Every function in `L^{p,q}(μ)` with `1 < p ≤ ∞` and `q ≠ 0` has finite rearrangement integral
`∫₀ᵗ (‖f‖ₑ)* < ∞` for all `t ≥ 0`. -/
theorem MemLorentz.setLIntegral_decreasingRearrangement_lt_top {f : α → ε} {p q : ℝ≥0∞}
    (hf : MemLorentz f p q μ) (hp : 1 < p) (hq : q ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s < ∞ := by
  have htop : MemLorentz f p ∞ μ := by
    rcases eq_or_ne p ∞ with rfl | hptop
    · rcases eq_or_ne q ∞ with rfl | hqtop
      · exact hf
      · obtain ⟨hfm, h0⟩ := (memLorentz_top_left_iff hq hqtop).1 hf
        rw [memLorentz_iff, eLorentzNorm_self, eLpNorm_exponent_top hfm,
          eLpNormEssSup_eq_essSup_eNorm, ENNReal.essSup_eq_zero_iff.2 h0]
        exact ENNReal.zero_lt_top
    · exact hf.mono_exponent (zero_lt_one.trans hp).ne' hptop hq le_top
  exact (setLIntegral_decreasingRearrangement_le_eLorentzNorm_top f hp ht μ).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top htop.eLorentzNorm_lt_top)

end ContinuousENorm

section Indicator

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

private theorem eLorentzNorm_indicator_one_top {A : Set α} (hA : NullMeasurableSet A μ)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    eLorentzNorm (A.indicator fun _ ↦ (1 : ℝ≥0∞)) p ∞ μ = μ A ^ p.toReal⁻¹ := by
  have h1 : AEStronglyMeasurable (A.indicator fun _ ↦ (1 : ℝ≥0∞)) μ :=
    aestronglyMeasurable_const.indicator₀ hA
  set αr := p.toReal⁻¹
  have hα : 0 < αr := inv_pos.2 (ENNReal.toReal_pos hp0 hptop)
  rw [eLorentzNorm_top_eq_iSup_measure_lt h1 hp0 hptop]
  refine le_antisymm (iSup_le fun b ↦ ?_) ?_
  · by_cases hb1 : b < 1
    · have hset : {y | b < ‖A.indicator (fun _ ↦ (1 : ℝ≥0∞)) y‖ₑ} = A := by
        ext y; by_cases hy : y ∈ A <;> simp [hy, hb1]
      rw [hset]
      exact mul_le_of_le_one_left bot_le hb1.le
    · have hset : {y | b < ‖A.indicator (fun _ ↦ (1 : ℝ≥0∞)) y‖ₑ} = ∅ := by
        ext y; by_cases hy : y ∈ A <;> simp [hy, hb1]
      rw [hset, measure_empty, ENNReal.zero_rpow_of_pos hα, mul_zero]
      exact bot_le
  · have h_le : ∀ r ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal r * μ A ^ αr ≤
        ⨆ b : ℝ≥0∞, b * μ {y | b < ‖A.indicator (fun _ ↦ (1 : ℝ≥0∞)) y‖ₑ} ^ αr := by
      rintro r ⟨_, hr1⟩
      have hb1 : ENNReal.ofReal r < 1 := ENNReal.ofReal_lt_one.2 hr1
      have hset : {y | ENNReal.ofReal r < ‖A.indicator (fun _ ↦ (1 : ℝ≥0∞)) y‖ₑ} = A := by
        ext y; by_cases hy : y ∈ A <;> simp [hy, hb1]
      exact le_iSup_of_le (ENNReal.ofReal r) (by rw [hset])
    have htend : Tendsto (fun r : ℝ ↦ ENNReal.ofReal r * μ A ^ αr)
        (𝓝[<] 1) (𝓝 (ENNReal.ofReal 1 * μ A ^ αr)) :=
      ENNReal.Tendsto.mul_const
        (ENNReal.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (Or.inl (by simp))
    simpa using le_of_tendsto htend (eventually_of_mem (Ioo_mem_nhdsLT one_pos) h_le)

private theorem lintegral_rpow_indicator_top_eq_top {A : Set α} (hμtop : μ A = ∞)
    {αr r : ℝ} (hα : 0 < αr) (hr : 0 < r) :
    ∫⁻ t, (ENNReal.ofReal (t ^ αr) *
      μ.decreasingRearrangement (A.indicator fun _ ↦ (1 : ℝ≥0∞)) t) ^ r ∂multHaar = ∞ := by
  set β := αr * r
  have hβ : 0 < β := mul_pos hα hr
  have hbound : ∀ n : ℕ, (n : ℝ≥0∞) ≤ ∫⁻ t,
      (ENNReal.ofReal (t ^ αr) *
        μ.decreasingRearrangement (A.indicator fun _ ↦ (1 : ℝ≥0∞)) t) ^ r ∂multHaar := fun n ↦ by
    set T := (β * ((n : ℝ) + 1)) ^ β⁻¹
    have hT : 0 < T := Real.rpow_pos_of_pos (by positivity) _
    have hval : (n : ℝ≥0∞) ≤ ENNReal.ofReal (β⁻¹ * T ^ β) := by
      dsimp [T]
      rw [← Real.rpow_mul (by positivity), inv_mul_cancel₀ hβ.ne', Real.rpow_one,
        inv_mul_cancel_left₀ hβ.ne', ENNReal.ofReal_add (Nat.cast_nonneg n) zero_le_one,
        ENNReal.ofReal_natCast]
      exact le_self_add
    refine hval.trans ((setLIntegral_Ioc_rpow_multHaar hβ hT).symm.le.trans ?_)
    refine (setLIntegral_mono' measurableSet_Ioc fun s hs ↦ ?_).trans
      (setLIntegral_le_lintegral _ _)
    rw [μ.decreasingRearrangement_indicator, hμtop]
    simp only [ENNReal.ofReal_lt_top, ↓reduceIte, mul_one,
      ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hs.1 αr), ← Real.rpow_mul hs.1.le]
    exact le_rfl
  exact eq_top_iff.2 (ENNReal.iSup_natCast ▸ iSup_le hbound)

private theorem ae_rpow_indicator_eq_indicator_Ioc {A : Set α} {a : ℝ} (ha : 0 < a)
    (ha_eq : ENNReal.ofReal a = μ A) (αr : ℝ) {r : ℝ} (hr : 0 < r) :
    (fun t : ℝ ↦ (ENNReal.ofReal (t ^ αr) *
      μ.decreasingRearrangement (A.indicator fun _ ↦ (1 : ℝ≥0∞)) t) ^ r) =ᵐ[multHaar]
        (Ioc 0 a).indicator fun t ↦ ENNReal.ofReal (t ^ (αr * r)) := by
  have h_sng : multHaar {a} = 0 := by
    rw [← Icc_self, multHaar_Icc ha le_rfl, sub_self, ENNReal.ofReal_zero]
  have hae_ne : ∀ᵐ t ∂multHaar, t ≠ a := ae_iff.2 (by simpa using h_sng)
  filter_upwards [ae_pos_multHaar, hae_ne] with t ht ht_ne
  simp_rw [μ.decreasingRearrangement_indicator, ← ha_eq, ENNReal.ofReal_lt_ofReal_iff ha]
  by_cases hta : t < a
  · simp only [hta, ↓reduceIte, indicator_of_mem (mem_Ioc.2 ⟨ht, hta.le⟩), mul_one,
      ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos ht αr), ← Real.rpow_mul ht.le]
  · have hnot : t ∉ Ioc 0 a := fun h ↦ hta (lt_of_le_of_ne (mem_Ioc.1 h).2 ht_ne)
    simp only [hta, ↓reduceIte, indicator_of_notMem hnot, mul_zero, ENNReal.zero_rpow_of_pos hr]

private theorem eLorentzNorm_indicator_one_of_ne_top {A : Set α} (hA : NullMeasurableSet A μ)
    {p q : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ∞) (hq0 : q ≠ 0) (hqtop : q ≠ ∞) :
    eLorentzNorm (A.indicator fun _ ↦ (1 : ℝ≥0∞)) p q μ =
      ENNReal.ofReal ((p.toReal / q.toReal) ^ q.toReal⁻¹) * μ A ^ p.toReal⁻¹ := by
  have h1 : AEStronglyMeasurable (A.indicator fun _ ↦ (1 : ℝ≥0∞)) μ :=
    aestronglyMeasurable_const.indicator₀ hA
  set αr := p.toReal⁻¹
  have hα : 0 < αr := inv_pos.2 (ENNReal.toReal_pos hp0 hptop)
  have hr : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
  set β := αr * q.toReal
  have hβ : 0 < β := mul_pos hα hr
  have hβ_inv : β⁻¹ = p.toReal / q.toReal := by dsimp [β, αr]; rw [inv_mul_eq_div, inv_div]
  rw [eLorentzNorm_eq_eLpNorm_multHaar hp0 h1]
  rcases eq_or_ne (μ A) 0 with hμ0 | hμ0
  · rw [hμ0, ENNReal.zero_rpow_of_pos hα, mul_zero]
    have hcongr : (fun t : ℝ ↦ ENNReal.ofReal (t ^ αr) *
        μ.decreasingRearrangement (‖A.indicator (fun _ ↦ (1 : ℝ≥0∞)) ·‖ₑ) t) =ᵐ[multHaar] 0 := by
      filter_upwards [ae_pos_multHaar] with t _
      simp [eNorm_eq_self, μ.decreasingRearrangement_indicator, hμ0]
    rw [eLpNorm_congr_ae hcongr, eLpNorm_zero]
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hq0 hqtop
    (measurable_ofReal_rpow_mul_decreasingRearrangement μ _ _).aestronglyMeasurable]
  simp only [eNorm_eq_self]
  rcases eq_or_ne (μ A) ∞ with hμtop | hμtop
  · have hC_pos : ENNReal.ofReal ((p.toReal / q.toReal) ^ q.toReal⁻¹) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (hβ_inv ▸ inv_pos.2 hβ) _)).ne'
    rw [hμtop, ENNReal.top_rpow_of_pos hα, ENNReal.mul_top hC_pos,
      lintegral_rpow_indicator_top_eq_top hμtop hα hr, one_div,
      ENNReal.top_rpow_of_pos (inv_pos.2 hr)]
  · set a := (μ A).toReal
    have ha : 0 < a := ENNReal.toReal_pos hμ0 hμtop
    have ha_eq : ENNReal.ofReal a = μ A := ENNReal.ofReal_toReal hμtop
    rw [lintegral_congr_ae (ae_rpow_indicator_eq_indicator_Ioc ha ha_eq αr hr),
      lintegral_indicator measurableSet_Ioc, setLIntegral_Ioc_rpow_multHaar hβ ha, one_div,
      ENNReal.ofReal_rpow_of_pos (mul_pos (inv_pos.2 hβ) (Real.rpow_pos_of_pos ha β)),
      Real.mul_rpow (inv_nonneg.2 hβ.le) (Real.rpow_nonneg ha.le _),
      ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.2 hβ.le) _), hβ_inv,
      ← Real.rpow_mul ha.le,
      (by dsimp [β]; field_simp : β * q.toReal⁻¹ = αr),
      ← ENNReal.ofReal_rpow_of_pos ha, ha_eq]

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]

/-- **Exact Lorentz gauge of an indicator `A.indicator (fun _ ↦ c)`.** For `0 < p < ∞` and
`0 < q ≤ ∞`,
`‖c 1_A‖_{L^{p,q}(μ)} = (p / q) ^ (1 / q) * ‖c‖ₑ * μ A ^ (1 / p)`
(at `q = ∞`, `q.toReal⁻¹ = 0`, so the prefactor `(p / q) ^ (1 / q)` is `1`). -/
theorem eLorentzNorm_indicator_const {A : Set α} (hA : NullMeasurableSet A μ) (c : ε) {p q : ℝ≥0∞}
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) (hq0 : q ≠ 0) :
    eLorentzNorm (A.indicator fun _ ↦ c) p q μ =
      ENNReal.ofReal ((p.toReal / q.toReal) ^ q.toReal⁻¹) * ‖c‖ₑ * μ A ^ p.toReal⁻¹ := by
  have hf : AEStronglyMeasurable (A.indicator fun _ ↦ c) μ :=
    aestronglyMeasurable_const.indicator₀ hA
  have h1 : AEStronglyMeasurable (A.indicator fun _ ↦ (1 : ℝ≥0∞)) μ :=
    aestronglyMeasurable_const.indicator₀ hA
  have hfactor : eLorentzNorm (A.indicator fun _ ↦ c) p q μ =
      ‖c‖ₑ * eLorentzNorm (A.indicator fun _ ↦ (1 : ℝ≥0∞)) p q μ := by
    rw [← eLorentzNorm_const_mul_ennreal h1]
    refine eLorentzNorm_congr_eNorm_ae hf
      (h1.aemeasurable.const_mul ‖c‖ₑ).aestronglyMeasurable (.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ A <;> simp [hx]
  rw [hfactor]
  rcases eq_or_ne q ∞ with rfl | hqtop
  · simp [eLorentzNorm_indicator_one_top hA hp0 hptop]
  · rw [eLorentzNorm_indicator_one_of_ne_top hA hp0 hptop hq0 hqtop]
    ring

/-- Weak-`Lᵖ` indicator formula (`q = ∞`): `‖c 1_A‖_{L^{p,∞}(μ)} = ‖c‖ₑ * μ A ^ (1 / p)`. -/
@[simp]
theorem eLorentzNorm_indicator_const_top {A : Set α} (hA : NullMeasurableSet A μ) (c : ε)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    eLorentzNorm (A.indicator fun _ ↦ c) p ∞ μ = ‖c‖ₑ * μ A ^ p.toReal⁻¹ := by
  simpa using eLorentzNorm_indicator_const hA c hp0 hptop ENNReal.top_ne_zero

end Indicator

end TauCeti
