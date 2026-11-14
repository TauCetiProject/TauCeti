/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Integral.Lebesgue.Subsequence
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Finite-grid approximation without a moment bound

A predictable holding whose paths are integrable for a finite time measure admits bounded
finite-grid approximations converging almost surely in pathwise L¹. No integrability of the
random path norm is required. In particular the time measure may be the absolute variation
of a deterministic bond, including intervals on which the bond is constant.

The construction uses Mathlib's finite-valued `SimpleFunc.approxOn` quantizations, followed
by finite-grid L² approximation of each quantized process. Only the latter errors are
integrated over the sample space. Taking a subsequence makes these errors vanish on almost
every path; the original quantizations converge in L¹ separately on every integrable path.
The grids need not be nested or share their last date.

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
    (ν : Measure ℝ≥0) [IsFiniteMeasure ν] (P : Measure Ω) [IsFiniteMeasure P]
    (hν : ν {0} = 0) {H : ℝ≥0 → Ω → ℝ} (hH : IsStronglyPredictable ℱ H)
    (hint : ∀ᵐ ω ∂P, Integrable (fun t ↦ H t ω) ν) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      (∀ k, τ k 0 = 0) ∧ (∀ k, StrictMonoOn (τ k) (Iic (n k))) ∧
      (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
      (∀ k j, j < n k → ∀ ω, ‖a k j ω‖ ≤ C k) ∧
      ∀ᵐ ω ∂P, Tendsto (fun k ↦ ∫⁻ t,
        ‖simpleHolding (τ k) (n k) (a k) t ω - H t ω‖ₑ ∂ν) atTop (𝓝 0) := by
  -- Quantize values first: finite range gives L² without a moment assumption on H.
  let q (k : ℕ) : SimpleFunc ℝ ℝ :=
    SimpleFunc.approxOn id measurable_id univ 0 (mem_univ 0) k
  let G (k : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ := q k (H t ω)
  have hG (k : ℕ) : IsStronglyPredictable ℱ (G k) :=
    (q k).stronglyMeasurable.comp_measurable hH.measurable
  let μ := (ν.prod P).trim ℱ.predictable_le_prod
  have hG₂ (k : ℕ) : MemLp (Function.uncurry (G k)) 2 μ := by
    let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    exact ((q k).comp (Function.uncurry H) hH.measurable).memLp_of_isFiniteMeasure 2 μ
  have hzero : μ ({0} ×ˢ (univ : Set Ω)) = 0 := by
    have hz : MeasurableSet[ℱ.predictable] ({0} ×ˢ (univ : Set Ω)) := by
      simpa only [NNReal.bot_eq_zero] using
        measurableSet_predictable_singleton_bot_prod (𝓕 := ℱ) MeasurableSet.univ
    simp only [μ, trim_measurableSet_eq _ hz, Measure.prod_prod, hν, zero_mul]
  -- Approximate each quantization by a finite grid; only these errors have small expectation.
  have hex (k : ℕ) := ℱ.exists_simpleHolding_eLpNorm_sub_lt μ
    (fun _ _ _ _ ↦ measure_ne_top _ _) hzero (hG₂ k)
    (ε := (k : ℝ≥0∞)⁻¹) (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top k))
  choose n τ a C hτ₀ hτ ha hb herr using hex
  let D (k : ℕ) (p : ℝ≥0 × Ω) : ℝ :=
    simpleHolding (τ k) (n k) (a k) p.1 p.2 - G k p.1 p.2
  have hD (k : ℕ) : StronglyMeasurable[ℱ.predictable] (D k) :=
    (isStronglyPredictable_simpleHolding (ℱ := ℱ) (ha k)).sub (hG k)
  have hDprod (k : ℕ) : StronglyMeasurable (D k) := (hD k).mono ℱ.predictable_le_prod
  have hL₂ : Tendsto (fun k ↦ eLpNorm (D k) 2 (ν.prod P)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      ENNReal.tendsto_inv_nat_nhds_zero (Eventually.of_forall fun _ ↦ bot_le)
    filter_upwards with k
    have hk : eLpNorm (D k) 2 μ ≤ (k : ℝ≥0∞)⁻¹ := (herr k).le
    simpa only [μ, eLpNorm_trim ℱ.predictable_le_prod (hD k)] using hk
  have hL₁ := TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hL₂
  have hiter : Tendsto (fun k ↦ ∫⁻ ω, ∫⁻ t, ‖D k (t, ω)‖ₑ ∂ν ∂P)
      atTop (𝓝 0) := by
    simpa only [eLpNorm_one_eq_lintegral_eNorm (hDprod _).aestronglyMeasurable,
      lintegral_prod_symm _ (hDprod _).measurable.eNorm.aemeasurable] using hL₁
  -- One subsequence makes the grid-to-quantization L¹ errors vanish almost surely.
  obtain ⟨φ, hφ, hpath⟩ := exists_strictMono_ae_tendsto_zero_of_tendsto_lintegral
    (fun k ↦ ((hDprod k).measurable.eNorm.lintegral_prod_left).aemeasurable) hiter
  refine ⟨n ∘ φ, fun k ↦ τ (φ k), fun k ↦ a (φ k), C ∘ φ,
    fun k ↦ hτ₀ (φ k), fun k ↦ hτ (φ k), fun k ↦ ha (φ k), fun k ↦ hb (φ k), ?_⟩
  filter_upwards [hint, hpath] with ω hω herror
  -- On each integrable path, Mathlib's quantizations converge in L¹; add the two errors.
  have hm : Measurable (fun t ↦ H t ω) :=
    (hH.measurable.mono ℱ.predictable_le_prod le_rfl).comp measurable_prodMk_right
  have hquant : Tendsto (fun k ↦ ∫⁻ t, ‖G k t ω - H t ω‖ₑ ∂ν) atTop (𝓝 0) := by
    have h := SimpleFunc.tendsto_approxOn_L1_eNorm hm (mem_univ (0 : ℝ))
      (ae_of_all ν fun _ ↦ by simp) (by simpa using hω.hasFiniteIntegral)
    have heq (k : ℕ) : (q k).comp (fun t ↦ H t ω) hm =
        SimpleFunc.approxOn (fun t ↦ H t ω) hm univ 0 (mem_univ 0) k :=
      (SimpleFunc.approxOn_comp measurable_id hm (mem_univ 0) k).symm
    simpa only [← heq, SimpleFunc.coe_comp, Function.comp_apply] using h
  have hsum := herror.add (hquant.comp hφ.tendsto_atTop)
  simp only [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ ↦ bot_le) (Eventually.of_forall fun k ↦ ?_)
  calc
    _ ≤ ∫⁻ t, ‖D (φ k) (t, ω)‖ₑ + ‖G (φ k) t ω - H t ω‖ₑ ∂ν := by
      apply lintegral_mono
      intro t
      simpa only [D, Function.comp_apply, sub_add_sub_cancel] using eNorm_add_le
        (simpleHolding (τ (φ k)) (n (φ k)) (a (φ k)) t ω - G (φ k) t ω)
        (G (φ k) t ω - H t ω)
    _ = _ := lintegral_add_left
      ((hDprod (φ k)).measurable.comp measurable_prodMk_right).eNorm _

end MeasureTheory.Filtration
