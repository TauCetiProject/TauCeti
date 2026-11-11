/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Elementary approximation in pathwise square energy

On a fixed finite horizon, every predictable real process with almost surely finite
square energy admits bounded elementary predictable approximations whose square errors
converge to zero almost surely. No expected-energy bound is required. In particular this
supplies the elementary approximation needed for locally square-integrable Brownian
integrands, including initial-measurable heavy-tailed integrands.

The grids are deterministic, start at zero, and have bounded left-endpoint-measurable
heights. Neither nesting nor a common bound on the heights is asserted. The exceptional
sample set and the sequence may depend on the horizon. The error uses a nonnegative
lower integral, so infinite energies are not replaced by default-valued Bochner integrals.
This is an integrand approximation theorem, not a construction of a stochastic integral.

The construction uses value truncations, the expected-energy density theorem
`MeasureTheory.Filtration.exists_simpleHolding_eLpNorm_sub_lt_timeMeasure`, and summably
small expected approximation errors. Value truncation does not require stopping times
or usual filtration conditions.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

open MeasureTheory Set Filter TauCeti.Finance
open scoped ENNReal NNReal Topology

namespace MeasureTheory.IsStronglyPredictable

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {H : ℝ≥0 → Ω → ℝ}

/-- A predictable process with finite pathwise square energy on a finite horizon has bounded
finite-grid approximations converging in square energy on almost every sample path.
The original process need not have a finite expected square energy. -/
theorem exists_seq_simpleHolding_tendsto_ae_energy
    (hH : IsStronglyPredictable ℱ H) (T : ℝ≥0)
    (hH₂ : ∀ᵐ ω ∂P, MemLp (fun t ↦ H t ω) 2 (TauCeti.Probability.timeMeasure T)) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      (∀ m, τ m 0 = 0) ∧ (∀ m, StrictMonoOn (τ m) (Iic (n m))) ∧
      (∀ m j, j < n m → StronglyMeasurable[ℱ (τ m j)] (a m j)) ∧
      (∀ m j, j < n m → ∀ ω, ‖a m j ω‖ ≤ C m) ∧
      ∀ᵐ ω ∂P, Tendsto (fun m ↦ ∫⁻ t,
        ‖simpleHolding (τ m) (n m) (a m) t ω - H t ω‖ₑ ^ 2
          ∂TauCeti.Probability.timeMeasure T) atTop (𝓝 0) := by
  classical
  let ν := TauCeti.Probability.timeMeasure T
  let K (m : ℕ) (t : ℝ≥0) (ω : Ω) := if ‖H t ω‖ ≤ m then H t ω else 0
  have hK (m : ℕ) : IsStronglyPredictable ℱ (K m) :=
    hH.ite (measurableSet_le hH.norm.measurable measurable_const) stronglyMeasurable_const
  have hKbound (m : ℕ) (t : ℝ≥0) (ω : Ω) : ‖K m t ω‖ ≤ m := by
    simp only [K]
    split_ifs with h <;> simp_all
  have hK₂ (m : ℕ) : MemLp (Function.uncurry (K m)) 2 (ν.prod P) := by
    refine (memLp_const (m : ℝ)).mono'
      ((hK m).mono ℱ.predictable_le_prod).aestronglyMeasurable ?_
    exact Eventually.of_forall fun p ↦ hKbound m p.1 p.2
  -- Approximate each bounded truncation with a summable sequence of expected errors.
  have hex (m : ℕ) := ℱ.exists_simpleHolding_eLpNorm_sub_lt_timeMeasure P T (hK m) (hK₂ m)
    (ε := ((1 / 2 : ℝ≥0) ^ m : ℝ≥0∞)) (by positivity)
  choose n τ a C hτ₀ hτ ha hb herr using hex
  let L (m : ℕ) := simpleHolding (τ m) (n m) (a m)
  let E (m : ℕ) (ω : Ω) := ∫⁻ t, ‖L m t ω - K m t ω‖ₑ ^ 2 ∂ν
  have hpred (m : ℕ) : IsStronglyPredictable ℱ (fun t ω ↦ L m t ω - K m t ω) :=
    (isStronglyPredictable_simpleHolding (ha m)).sub (hK m)
  have hmeas (m : ℕ) : Measurable (fun p : ℝ≥0 × Ω ↦ ‖L m p.1 p.2 - K m p.1 p.2‖ₑ ^ 2) :=
    ((hpred m).mono ℱ.predictable_le_prod).measurable.enorm.pow_const 2
  have hE (m : ℕ) : Measurable (E m) := (hmeas m).lintegral_prod_left'
  have hmean (m : ℕ) : ∫⁻ ω, E m ω ∂P ≤ ((1 / 2 : ℝ≥0) ^ m : ℝ≥0∞) := by
    rw [← lintegral_lintegral_swap (hmeas m).aemeasurable]
    rw [← lintegral_prod _ (hmeas m).aemeasurable]
    have hpow := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
      ((hpred m).mono ℱ.predictable_le_prod).aestronglyMeasurable (μ := ν.prod P)
    simp only [NNReal.coe_ofNat, ENNReal.rpow_two, Function.uncurry_def,
      ENNReal.coe_ofNat] at hpow
    rw [← hpow]
    have hle : eLpNorm (Function.uncurry (fun t ω ↦ L m t ω - K m t ω)) 2 (ν.prod P) ≤ 1 :=
      (herr m).le.trans (by
        exact_mod_cast pow_le_one₀ (by norm_num : (0 : ℝ≥0) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ≥0) ≤ 1))
    calc
      _ ≤ eLpNorm (Function.uncurry (fun t ω ↦ L m t ω - K m t ω)) 2 (ν.prod P) := by
        rw [pow_two]
        exact mul_le_of_le_one_right' hle
      _ ≤ _ := (herr m).le
  have hsum : (∑' m, ((1 / 2 : ℝ≥0) ^ m : ℝ≥0∞)) ≠ ∞ :=
    ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_geometric (by norm_num))
  have hELim : ∀ᵐ ω ∂P, Tendsto (fun m ↦ E m ω) atTop (𝓝 0) := by
    have hfinite : ∫⁻ ω, ∑' m, E m ω ∂P ≠ ∞ := by
      rw [lintegral_tsum (fun m ↦ (hE m).aemeasurable)]
      exact ne_top_of_le_ne_top hsum (tsum_le_tsum hmean)
    filter_upwards [ae_lt_top' (AEMeasurable.tsum fun m ↦ (hE m).aemeasurable) hfinite] with ω hω
    exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  -- On each finite-energy path the value-truncation error vanishes by dominated convergence.
  have htrunc : ∀ᵐ ω ∂P, Tendsto
      (fun m ↦ ∫⁻ t, ‖K m t ω - H t ω‖ₑ ^ 2 ∂ν) atTop (𝓝 0) := by
    filter_upwards [hH₂] with ω hω
    have hsec : StronglyMeasurable (fun t ↦ H t ω) :=
      (hH.mono ℱ.predictable_le_prod).comp_measurable
        (measurable_id.prodMk measurable_const)
    have hdom (m : ℕ) (t : ℝ≥0) : ‖K m t ω - H t ω‖ₑ ^ 2 ≤ ‖H t ω‖ₑ ^ 2 := by
      by_cases h : ‖H t ω‖ ≤ m <;>
        simp only [K, h, ite_true, ite_false, sub_self, zero_sub, enorm_neg, enorm_zero,
          zero_pow (by decide : 2 ≠ 0), zero_le, le_refl]
    have hfinite : ∫⁻ t, ‖H t ω‖ₑ ^ 2 ∂ν < ∞ := by
      simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
        lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num) (by norm_num)
          hω.eLpNorm_lt_top
    have hlim (t : ℝ≥0) : Tendsto (fun m ↦ ‖K m t ω - H t ω‖ₑ ^ 2) atTop (𝓝 0) := by
      obtain ⟨N, hN⟩ := exists_nat_ge ‖H t ω‖
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with m hm
      have hm' : ‖H t ω‖ ≤ (m : ℝ) := hN.trans (Nat.cast_le.mpr hm)
      simp only [K, hm', ite_true, sub_self, enorm_zero, zero_pow (by decide : 2 ≠ 0)]
    simpa using tendsto_lintegral_of_dominated_convergence (fun t ↦ ‖H t ω‖ₑ ^ 2)
      (fun m ↦ (((hK m).mono ℱ.predictable_le_prod).comp_measurable
        (measurable_id.prodMk measurable_const)).sub hsec |>.measurable.enorm.pow_const 2)
      (fun m ↦ Eventually.of_forall (hdom m)) hfinite.ne (Eventually.of_forall hlim)
  -- The square error is at most twice each of the two square errors.
  refine ⟨n, τ, a, C, hτ₀, hτ, ha, hb, ?_⟩
  filter_upwards [hELim, htrunc] with ω hEω hKω
  have hbound (m : ℕ) : (∫⁻ t, ‖L m t ω - H t ω‖ₑ ^ 2 ∂ν) ≤
      2 * E m ω + 2 * ∫⁻ t, ‖K m t ω - H t ω‖ₑ ^ 2 ∂ν := by
    calc
      _ ≤ ∫⁻ t, 2 * ‖L m t ω - K m t ω‖ₑ ^ 2 +
          2 * ‖K m t ω - H t ω‖ₑ ^ 2 ∂ν := by
        apply lintegral_mono
        intro t
        have h := enorm_add_le (L m t ω - K m t ω) (K m t ω - H t ω)
        rw [sub_add_sub_cancel] at h
        have hsq := ENNReal.rpow_add_le_mul_rpow_add_rpow
          ‖L m t ω - K m t ω‖ₑ ‖K m t ω - H t ω‖ₑ (p := (2 : ℝ)) (by norm_num)
        norm_num [ENNReal.rpow_two, mul_add] at hsq
        exact (pow_le_pow_left' h 2).trans hsq
      _ = _ := by
        have hmω : Measurable (fun t ↦ ‖L m t ω - K m t ω‖ₑ ^ 2) :=
          (hmeas m).comp (measurable_id.prodMk (measurable_const (a := ω)))
        rw [lintegral_add_left (hmω.const_mul 2),
          lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
  have hlim := (ENNReal.Tendsto.const_mul (a := 2) hEω (Or.inr (by norm_num))).add
    (ENNReal.Tendsto.const_mul (a := 2) hKω (Or.inr (by norm_num)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [mul_zero, zero_add] using hlim)
    (Eventually.of_forall fun _ ↦ bot_le) (Eventually.of_forall hbound)

end MeasureTheory.IsStronglyPredictable
