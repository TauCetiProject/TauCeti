/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy.WeightedApproximation

/-!
# Finite-grid approximation without a moment bound

A predictable holding whose paths are integrable for a finite time measure admits bounded
finite-grid approximations converging almost surely in pathwise L¹. No integrability of the
random path norm is required. In particular the time measure may be the absolute variation
of a deterministic bond, including intervals on which the bond is constant.

The sample measure need only be s-finite. The construction uses
`IsStronglyPredictable.exists_seq_simpleHolding_ae_tendsto_lintegral_mul_enorm_sub_sq`
with weight `(1 + ‖H‖ₑ)⁻¹`. Weighted Cauchy–Schwarz converts its pathwise square-energy
convergence to L¹ convergence. The grids need not be nested or share their last date.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

noncomputable section

open MeasureTheory Set Filter TauCeti TauCeti.Finance
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Filtration

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 mΩ)

/-- Almost-sure pathwise L¹ integrability suffices for approximation by bounded finite-grid
holdings with left-measurable heights. The time measure must be finite and have no atom at
zero, where elementary holdings vanish. There is no expected-integrability hypothesis. -/
theorem exists_seq_simpleHolding_ae_tendsto_lintegral_enorm_sub
    (ν : Measure ℝ≥0) [IsFiniteMeasure ν] (P : Measure Ω) [SFinite P]
    (hν : ν {0} = 0) {H : ℝ≥0 → Ω → ℝ} (hH : IsStronglyPredictable ℱ H)
    (hint : ∀ᵐ ω ∂P, Integrable (fun t ↦ H t ω) ν) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      (∀ k, τ k 0 = 0) ∧ (∀ k, StrictMonoOn (τ k) (Iic (n k))) ∧
      (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
      (∀ k j, j < n k → ∀ ω, ‖a k j ω‖ ≤ C k) ∧
      ∀ᵐ ω ∂P, Tendsto (fun k ↦ ∫⁻ t,
        ‖simpleHolding (τ k) (n k) (a k) t ω - H t ω‖ₑ ∂ν) atTop (𝓝 0) := by
  let B (p : ℝ≥0 × Ω) := 1 + ‖H p.1 p.2‖ₑ
  have hB : Measurable B :=
    measurable_const.add ((hH.mono ℱ.predictable_le_prod).measurable.eNorm)
  have hB₀ (p) : B p ≠ 0 := by positivity
  have hBtop (p) : B p ≠ ∞ := by simp [B]
  have hmass : ∀ᵐ ω ∂P, ∫⁻ t, B (t, ω) ∂ν < ∞ := by
    filter_upwards [hint] with ω hω
    rw [lintegral_add_left measurable_const]
    exact ENNReal.add_lt_top.mpr ⟨by simp, hasFiniteIntegral_iff_eNorm.mp hω.2⟩
  -- The reciprocal weight turns pathwise L¹ integrability into finite weighted energy.
  have hfin : ∀ᵐ ω ∂P, ∫⁻ t, (B (t, ω))⁻¹ * (1 + ‖H t ω‖ₑ ^ 2) ∂ν < ∞ := by
    filter_upwards [hmass] with ω hω
    apply lt_of_le_of_lt (lintegral_mono fun t ↦ ?_) hω
    calc
      _ ≤ (B (t, ω))⁻¹ * B (t, ω) ^ 2 := by
        gcongr
        simpa only [B, one_pow] using
          pow_add_pow_le (x := (1 : ℝ≥0∞)) (y := ‖H t ω‖ₑ) bot_le bot_le (by decide : 2 ≠ 0)
      _ = B (t, ω) := by
        rw [pow_two, ← mul_assoc, ENNReal.inv_mul_cancel (hB₀ _) (hBtop _), one_mul]
  obtain ⟨n, τ, a, C, hτ₀, hτ, ha, hb, hpath⟩ :=
    hH.exists_seq_simpleHolding_ae_tendsto_lintegral_mul_enorm_sub_sq hν hB.inv.aemeasurable hfin
  refine ⟨n, τ, a, C, hτ₀, hτ, ha, hb, ?_⟩
  filter_upwards [hmass, hpath] with ω hω herror
  -- Weighted Cauchy–Schwarz controls the L¹ error by the vanishing square-energy error.
  have hlim := ENNReal.Tendsto.mul_const (b := (∫⁻ t, B (t, ω) ∂ν) ^ (1 / 2 : ℝ))
    (herror.ennrpow_const (1 / 2 : ℝ))
    (Or.inr ((ENNReal.rpow_lt_top_of_nonneg (by norm_num) hω.ne).ne))
  simp only [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2), zero_mul] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ bot_le) (Eventually.of_forall fun k ↦ ?_)
  have hm : Measurable (fun t ↦
      simpleHolding (τ k) (n k) (a k) t ω - H t ω) :=
    (((isStronglyPredictable_simpleHolding (ha k)).sub hH).mono
      ℱ.predictable_le_prod).measurable.comp measurable_prodMk_right
  have hBω : Measurable (fun t ↦ B (t, ω)) := hB.comp measurable_prodMk_right
  have hCS := ENNReal.lintegral_mul_norm_pow_le (μ := ν)
    ((hBω.inv.mul (hm.eNorm.pow_const 2)).aemeasurable) hBω.aemeasurable
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  convert hCS using 1
  apply lintegral_congr
  intro t
  simp only [Pi.mul_apply, Pi.inv_apply]
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    mul_right_comm, ENNReal.inv_mul_cancel (hB₀ _) (hBtop _), one_mul,
    ← ENNReal.rpow_natCast_mul]
  norm_num

end MeasureTheory.Filtration
