/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.MaximalInequality

import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
/-!
# Uniform approximation of martingales

Doob's weak maximal inequality converts a terminal L¹ error into a uniform path-error
probability. Consequently, martingale approximants which are L¹-Cauchy at each integer
horizon have a single subsequence with summable uniform increment-error probabilities on
every finite horizon. These bounds are the probabilistic input to selecting continuous
limits of elementary stochastic integrals.

The approximants need only have almost surely right-continuous paths. No completion or
right continuity of the filtration is assumed. The path-error events are measured by outer
measure, so no literal measurability of an uncountable supremum is asserted. The norm
estimate uses Mathlib's conditional Jensen inequality `norm_condExp_le`.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §§1.3 and 3.2.
-/

public section

noncomputable section

open Filter Set Topology
open scoped ENNReal NNReal

namespace MeasureTheory.Martingale

variable {Ω E ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [IsFiniteMeasure μ]

/-- **Doob's weak maximal inequality for the norm of a martingale.** A terminal L¹
bound controls the outer probability of a uniform path error. -/
theorem mul_measure_exists_le_norm_lt_le [LinearOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] {ℱ : Filtration ι mΩ}
    {M : ι → Ω → E} (hM : Martingale M ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ M u ω) (Ioi t) t)
    (ε : ℝ≥0) :
    ε * μ {ω | ∃ t ≤ T, (ε : ℝ) < ‖M t ω‖} ≤
      ENNReal.ofReal (∫ ω, ‖M T ω‖ ∂μ) := by
  have hnorm : Submartingale (fun t ω ↦ ‖M t ω‖) ℱ μ := by
    refine ⟨fun t ↦ (hM.stronglyAdapted t).norm, fun s t hst ↦ ?_,
      fun t ↦ (hM.integrable t).norm⟩
    filter_upwards [norm_condExp_le (m := ℱ s) (M t), hM.condExp_ae_eq hst] with ω h₁ h₂
    simpa only [h₂] using h₁
  exact hnorm.mul_measure_exists_le_lt_le (fun _ _ ↦ norm_nonneg _)
    (hcont.mono fun ω hω t ht ↦ (hω t ht).norm) ε

/-- Martingale approximants which are terminally L¹-Cauchy have a subsequence whose
uniform increment errors at horizon `n` exceed `2⁻ⁿ` with outer probability at most `2⁻ⁿ`.
The same subsequence has summable error probabilities on every fixed finite horizon.
Only the integer-horizon L¹ classes are required to be Cauchy. -/
theorem exists_strictMono_summable_uniform_errors {ℱ : Filtration ℝ≥0 mΩ}
    {M : ℕ → ℝ≥0 → Ω → E} (hM : ∀ n, Martingale (M n) ℱ μ)
    (hcont : ∀ n, ∀ᵐ ω ∂μ, ∀ t, ContinuousWithinAt (fun u ↦ M n u ω) (Ioi t) t)
    (hCauchy : ∀ k : ℕ, CauchySeq (fun n ↦
      ((hM n).integrable (k : ℝ≥0)).toL1 (M n k))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ n : ℕ, μ {ω | ∃ t ≤ (n : ℝ≥0),
        (2 : ℝ)⁻¹ ^ n < ‖M (φ (n + 1)) t ω - M (φ n) t ω‖} ≤
          (2 : ℝ≥0∞)⁻¹ ^ n) ∧
      ∀ T : ℝ≥0, (∑' n, μ {ω | ∃ t ≤ T,
        (2 : ℝ)⁻¹ ^ n < ‖M (φ (n + 1)) t ω - M (φ n) t ω‖}) < ∞ := by
  -- Select terminal errors smaller than the product of the desired path threshold
  -- and probability bound. A monotone majorant makes one subsequence work at all horizons.
  have hsmall (k : ℕ) := Metric.cauchySeq_iff.1 (hCauchy k)
    ((2 : ℝ)⁻¹ ^ k * (2 : ℝ)⁻¹ ^ k) (by positivity)
  choose N hN using hsmall
  obtain ⟨φ, hφmono, hφN⟩ : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, N n ≤ φ n := by
    let φ : ℕ → ℕ := fun n ↦ n + (Finset.range (n + 1)).sup N
    refine ⟨φ, strictMono_nat_of_lt_succ fun n ↦ ?_, fun n ↦ ?_⟩
    · have hsup : (Finset.range (n + 1)).sup N ≤ (Finset.range (n + 1 + 1)).sup N :=
        Finset.sup_mono (Finset.range_mono (by omega))
      dsimp [φ]
      omega
    · exact (Finset.le_sup (f := N) (Finset.mem_range.2 (Nat.lt_succ_self n))).trans
        (Nat.le_add_left _ _)
  have hbound (n : ℕ) : μ {ω | ∃ t ≤ (n : ℝ≥0),
      (2 : ℝ)⁻¹ ^ n < ‖M (φ (n + 1)) t ω - M (φ n) t ω‖} ≤
        (2 : ℝ≥0∞)⁻¹ ^ n := by
    have hdist := hN n (φ (n + 1)) ((hφN n).trans (hφmono.monotone (Nat.le_succ n)))
      (φ n) (hφN n)
    rw [dist_eq_norm, ← Integrable.toL1_sub, Integrable.norm_toL1] at hdist
    simp only [edist_zero_right] at hdist
    rw [← integral_norm_eq_lintegral_enorm
        (((hM (φ (n + 1))).integrable n).sub ((hM (φ n)).integrable n)).aestronglyMeasurable]
      at hdist
    have hmax := ((hM (φ (n + 1))).sub (hM (φ n))).mul_measure_exists_le_norm_lt_le
      (T := (n : ℝ≥0)) (by
        filter_upwards [hcont (φ (n + 1)), hcont (φ n)] with ω h₁ h₂ t _
        exact (h₁ t).sub (h₂ t)) ((2 : ℝ≥0)⁻¹ ^ n)
    have hlt : ENNReal.ofReal (∫ ω, ‖M (φ (n + 1)) n ω - M (φ n) n ω‖ ∂μ) ≤
        ((2 : ℝ≥0)⁻¹ ^ n : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n := by
      refine (ENNReal.ofReal_le_ofReal hdist.le).trans_eq ?_
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity) n,
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    exact (ENNReal.mul_le_mul_iff_right (by positivity) (by finiteness)).1 (hmax.trans hlt)
  refine ⟨φ, hφmono, hbound, fun T ↦ ?_⟩
  -- On a fixed horizon only finitely many indices precede its integer ceiling.
  have hmajor : ∀ᶠ n : ℕ in atTop,
      μ {ω | ∃ t ≤ T, (2 : ℝ)⁻¹ ^ n <
        ‖M (φ (n + 1)) t ω - M (φ n) t ω‖} ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    filter_upwards [eventually_ge_atTop (⌈T⌉₊)] with n hn
    refine (measure_mono ?_).trans (hbound n)
    rintro ω ⟨t, ht, hω⟩
    exact ⟨t, ht.trans ((Nat.le_ceil T).trans (by exact_mod_cast hn)), hω⟩
  obtain ⟨K, hK⟩ := eventually_atTop.1 hmajor
  rw [← sum_add_tsum_compl (Finset.range K)]
  refine ENNReal.add_lt_top.2 ⟨ENNReal.sum_lt_top.2 (fun _ _ ↦ measure_lt_top μ _), ?_⟩
  refine lt_of_le_of_lt (tsum_le_tsum fun n ↦ hK n (by simpa using n.property)) ?_
  refine lt_of_le_of_lt (tsum_comp_le_tsum_of_injective
    Subtype.val_injective (fun n : ℕ ↦ (2 : ℝ≥0∞)⁻¹ ^ n)) ?_
  rw [ENNReal.tsum_geometric]
  norm_num

end MeasureTheory.Martingale
