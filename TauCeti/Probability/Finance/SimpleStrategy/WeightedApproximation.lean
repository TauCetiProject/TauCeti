/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.MeasureTheory.Integral.Lebesgue.Subsequence

/-!
# Pathwise weighted approximation of stock holdings

Bounded finite-grid holdings approximate a predictable holding in pathwise weighted square
energy. The weight may depend on both time and the sample, and need not be predictable.
Only almost-sure finiteness of the weighted energy and weighted time mass is required;
neither is required to have finite expectation. The approximating heights remain measurable
at the left trading endpoints for the original filtration.

For stock diffusion gains the weight is the squared diffusion coefficient. For drift gains,
one can use the weight `|D| / (1 + |H|)`; weighted Cauchy–Schwarz then controls the drift L¹
error using the finite pathwise integral of `(1 + |H|) |D|`. Adding these two weights permits
one sequence of elementary holdings to control both stock-gains terms.

The construction restricts to sample events on which the total weighted mass and energy are
bounded, trims the resulting finite measures to the predictable sigma algebra, and uses
`Filtration.exists_simpleHolding_eLpNorm_sub_lt`. These sample events need not be known at
time zero: they are used only to measure approximation errors, never to gate the holdings.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer,
  2004, §5.2.
-/

public section

noncomputable section

open MeasureTheory Set Filter TauCeti.Finance
open scoped ENNReal NNReal Topology

namespace MeasureTheory.IsStronglyPredictable

/-- A predictable holding with almost surely finite weighted time mass and square energy
admits bounded, left-measurable finite-grid approximations in pathwise weighted square energy.
The time measure need only be s-finite and have no initial atom; no expected-energy bound,
Brownian motion, or usual filtration conditions are assumed. -/
theorem exists_seq_simpleHolding_tendsto_ae_weighted_energy
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
    {P : Measure Ω} [IsFiniteMeasure P] {ν : Measure ℝ≥0} [SFinite ν]
    {H : ℝ≥0 → Ω → ℝ} (hH : IsStronglyPredictable ℱ H) (hν : ν {0} = 0)
    {w : ℝ≥0 × Ω → ℝ≥0∞} (hw : Measurable w)
    (hfin : ∀ᵐ ω ∂P, ∫⁻ t, w (t, ω) * (1 + ‖H t ω‖ₑ ^ 2) ∂ν < ∞) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      (∀ k, τ k 0 = 0) ∧ (∀ k, StrictMonoOn (τ k) (Iic (n k))) ∧
      (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
      (∀ k j, j < n k → ∀ ω, ‖a k j ω‖ ≤ C k) ∧
      ∀ᵐ ω ∂P, Tendsto (fun k ↦ ∫⁻ t,
        w (t, ω) * ‖simpleHolding (τ k) (n k) (a k) t ω - H t ω‖ₑ ^ 2 ∂ν)
          atTop (𝓝 0) := by
  classical
  -- Localize the error measure, not the holdings, by the terminal weighted energy.
  have hHm : StronglyMeasurable (Function.uncurry H) := hH.mono ℱ.predictable_le_prod
  let A (ω : Ω) := ∫⁻ t, w (t, ω) * (1 + ‖H t ω‖ₑ ^ 2) ∂ν
  have hB : Measurable (fun p : ℝ≥0 × Ω ↦ 1 + ‖H p.1 p.2‖ₑ ^ 2) :=
    measurable_const.add (hHm.measurable.eNorm.pow_const 2)
  have hA : Measurable A := (hw.mul hB).lintegral_prod_left'
  let E (k : ℕ) := {ω | A ω ≤ k}
  have hE (k : ℕ) : MeasurableSet (E k) := measurableSet_le hA measurable_const
  let d (k : ℕ) (p : ℝ≥0 × Ω) := (E k).indicator (fun _ ↦ (1 : ℝ≥0∞)) p.2 * w p
  have hd (k : ℕ) : Measurable (d k) :=
    ((measurable_const.indicator (hE k)).comp measurable_snd).mul hw
  let μ (k : ℕ) := (ν.prod P).withDensity (d k)
  have hbound (k : ℕ) : ∫⁻ p, d k p * (1 + ‖H p.1 p.2‖ₑ ^ 2) ∂ν.prod P ≤
      (k : ℝ≥0∞) * P univ := by
    rw [lintegral_prod_symm (fun p ↦ d k p * (1 + ‖H p.1 p.2‖ₑ ^ 2))
      ((hd k).mul hB).aemeasurable]
    calc
      _ ≤ ∫⁻ _ : Ω, (k : ℝ≥0∞) ∂P := lintegral_mono fun ω ↦ by
        by_cases hω : ω ∈ E k
        · have hAω : A ω ≤ k := hω
          dsimp only [A] at hAω
          simpa only [d, indicator_of_mem hω, one_mul] using hAω
        · simp [d, hω]
      _ = _ := lintegral_const _
  have hμfin (k : ℕ) : IsFiniteMeasure (μ k) := by
    apply isFiniteMeasure_withDensity
    have hle : ∫⁻ p, d k p ∂ν.prod P ≤
        ∫⁻ p, d k p * (1 + ‖H p.1 p.2‖ₑ ^ 2) ∂ν.prod P :=
      lintegral_mono fun p ↦
        le_mul_of_one_le_right' (le_self_add : (1 : ℝ≥0∞) ≤ 1 + ‖H p.1 p.2‖ₑ ^ 2)
    exact (hle.trans_lt ((hbound k).trans_lt
      (ENNReal.mul_lt_top (by simp) (measure_lt_top P univ)))).ne
  have hH₂ (k : ℕ) : MemLp (Function.uncurry H) 2 ((μ k).trim ℱ.predictable_le_prod) := by
    rw [memLp_iff, eLpNorm_trim ℱ.predictable_le_prod hH]
    apply (eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top (by norm_num) (by norm_num)
      hHm.aestronglyMeasurable).2
    rw [lintegral_withDensity_eq_lintegral_mul (ν.prod P) (hd k)
      (hHm.measurable.eNorm.pow_const _)]
    simp only [Pi.mul_apply, ENNReal.toReal_ofNat, ENNReal.rpow_two]
    exact (lintegral_mono fun p ↦ mul_le_mul' le_rfl (le_add_of_nonneg_left bot_le)).trans_lt
      ((hbound k).trans_lt (ENNReal.mul_lt_top (by simp) (measure_lt_top P univ)))
  -- Apply predictable L² density on each finite localized measure.
  have hex (k : ℕ) := ℱ.exists_simpleHolding_eLpNorm_sub_lt
    ((μ k).trim ℱ.predictable_le_prod)
    (by let := hμfin k; exact fun _ _ _ _ ↦ measure_ne_top _ _)
    (by
      have hz : MeasurableSet[ℱ.predictable] ({0} ×ˢ (univ : Set Ω)) := by
        simpa only [NNReal.bot_eq_zero] using
          measurableSet_predictable_singleton_bot_prod (𝓕 := ℱ) MeasurableSet.univ
      rw [trim_measurableSet_eq ℱ.predictable_le_prod hz]
      apply withDensity_absolutelyContinuous
      simp [Measure.prod_prod, hν])
    (hH₂ k) (ε := (k : ℝ≥0∞)⁻¹) (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top k))
  choose n τ a C hτ₀ hτ ha hb herr using hex
  let err (k : ℕ) (p : ℝ≥0 × Ω) := simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2
  have herrm (k : ℕ) : StronglyMeasurable[ℱ.predictable] (err k) :=
    (isStronglyPredictable_simpleHolding (ha k)).sub hH
  -- Tonelli converts the product-space errors into expected pathwise errors.
  let F (k : ℕ) (ω : Ω) := ∫⁻ t, d k (t, ω) * ‖err k (t, ω)‖ₑ ^ 2 ∂ν
  have hFm (k : ℕ) : Measurable (F k) :=
    ((hd k).mul
      (((herrm k).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const 2)).lintegral_prod_left'
  have hFnorm (k : ℕ) : ∫⁻ ω, F k ω ∂P =
      eLpNorm (err k) 2 ((μ k).trim ℱ.predictable_le_prod) ^ 2 := by
    dsimp only [F]
    rw [← lintegral_prod_symm (fun p ↦ d k p * ‖err k p‖ₑ ^ 2)
      (((hd k).mul
        (((herrm k).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const 2)).aemeasurable)]
    rw [eLpNorm_trim ℱ.predictable_le_prod (herrm k)]
    have hnorm := eLpNorm_nnreal_pow_eq_lintegral (μ := μ k) (p := (2 : ℝ≥0))
      (by norm_num) ((herrm k).mono ℱ.predictable_le_prod).aestronglyMeasurable
    simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] at hnorm
    rw [hnorm, lintegral_withDensity_eq_lintegral_mul (ν.prod P) (hd k)
      (((herrm k).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const 2)]
    rfl
  have hFlim : Tendsto (fun k ↦ ∫⁻ ω, F k ω ∂P) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using ENNReal.Tendsto.pow ENNReal.tendsto_inv_nat_nhds_zero (n := 2))
      (Eventually.of_forall fun _ ↦ bot_le)
    exact Eventually.of_forall fun k ↦ by rw [hFnorm]; exact pow_le_pow_left' (herr k).le 2
  obtain ⟨φ, hφ, hlim⟩ := TauCeti.exists_strictMono_ae_tendsto_zero_of_tendsto_lintegral
    (fun k ↦ (hFm k).aemeasurable) hFlim
  refine ⟨n ∘ φ, τ ∘ φ, a ∘ φ, C ∘ φ, fun k ↦ hτ₀ _, fun k ↦ hτ _,
    fun k ↦ ha _, fun k ↦ hb _, ?_⟩
  -- Almost every sample eventually belongs to every remaining localization event.
  filter_upwards [hfin, hlim] with ω hω hlimω
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hω.ne
  apply hlimω.congr'
  filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop N)] with k hk
  have hmem : ω ∈ E (φ k) := hN.le.trans (by exact_mod_cast hk)
  simp [F, d, hmem, err]

end MeasureTheory.IsStronglyPredictable
