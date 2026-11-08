/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.MaximalInequality

/-!
# Uniform approximation of martingales

Doob's weak maximal inequality converts a terminal L¹ error into a uniform path-error
probability. Consequently, martingale approximants which are L¹-Cauchy at each integer
horizon have a single subsequence with summable uniform increment-error probabilities on
every finite horizon. These bounds are the probabilistic input to selecting continuous
limits of elementary stochastic integrals.

The approximants need only have almost surely right-continuous paths. No completion or
right continuity of the filtration is assumed. The path-error events are measured by outer
measure, so no literal measurability of an uncountable supremum is asserted. The imported norm
estimate uses Mathlib's conditional Jensen inequality `norm_condExp_le`.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §§1.3 and 3.2.
-/

public section

noncomputable section

open Filter Set Topology
open scoped ENNReal NNReal

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [IsFiniteMeasure μ]

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
  -- and probability bound. Mathlib's extraction lemma handles all integer horizons.
  have hsmall (k : ℕ) := Metric.cauchySeq_iff.1 (hCauchy k)
    ((2 : ℝ)⁻¹ ^ k * (2 : ℝ)⁻¹ ^ k) (by positivity)
  choose N hN using hsmall
  obtain ⟨φ, hφmono, hφN⟩ :=
    Filter.extraction_forall_of_eventually fun n ↦ eventually_ge_atTop (N n)
  have hbound (n : ℕ) : μ {ω | ∃ t ≤ (n : ℝ≥0),
      (2 : ℝ)⁻¹ ^ n < ‖M (φ (n + 1)) t ω - M (φ n) t ω‖} ≤
        (2 : ℝ≥0∞)⁻¹ ^ n := by
    have hdist := hN n (φ (n + 1)) ((hφN n).trans (hφmono.monotone (Nat.le_succ n)))
      (φ n) (hφN n)
    rw [dist_eq_norm, ← Integrable.toL1_sub, L1.norm_of_fun_eq_integral_norm] at hdist
    simpa only [ENNReal.coe_pow, ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0),
      ENNReal.coe_ofNat, NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_ofNat, Pi.sub_apply] using
      ((hM (φ (n + 1))).sub (hM (φ n))).measure_exists_le_norm_lt_le
        (T := (n : ℝ≥0)) (by
          filter_upwards [hcont (φ (n + 1)), hcont (φ n)] with ω h₁ h₂ t _
          exact (h₁ t).sub (h₂ t))
        (ε := (2 : ℝ≥0)⁻¹ ^ n) (δ := (2 : ℝ≥0)⁻¹ ^ n) (by positivity)
        (by simpa using hdist.le)
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

end MeasureTheory
