/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.Martingale.Basic

/-!
# Azuma-Hoeffding inequality

This file proves the Azuma-Hoeffding tail bound for a finite sum of bounded martingale
differences. The conditional form of Hoeffding's lemma turns each bounded, conditionally centered
increment into a conditionally sub-Gaussian random variable; Mathlib's sub-Gaussian martingale
inequality then controls the sum.

## Main results

* `ProbabilityTheory.hasCondSubgaussianMGF_of_bounded` — a bounded conditionally centered
  random variable is conditionally sub-Gaussian;
* `ProbabilityTheory.measureReal_sum_range_ge_le_of_bounded_martingale_differences` — the
  one-sided Azuma-Hoeffding inequality;
* `ProbabilityTheory.measureReal_abs_sum_range_ge_le_of_bounded_martingale_differences` — its
  two-sided form.

## References

* K. Azuma, *Weighted sums of certain dependent random variables*, Tohoku Mathematical Journal 19
  (1967), 357-367.
* C. McDiarmid, *On the method of bounded differences*, Surveys in Combinatorics 141 (1989),
  148-188.
-/

public section

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-- A conditionally centered random variable whose values lie in `[-b, b]` is conditionally
sub-Gaussian with parameter `b ^ 2`. -/
theorem hasCondSubgaussianMGF_of_bounded [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {X : Ω → ℝ} {b : ℝ}
    (hb : 0 ≤ b) (hX : Measurable[mΩ] X)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ b)
    (hmean : μ[X | m] =ᵐ[μ] 0) :
    HasCondSubgaussianMGF m hm X ⟨b ^ 2, sq_nonneg b⟩ μ := by
  have hIcc : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (-b) b := by
    filter_upwards [hbound] with ω hω
    exact abs_le.mp hω
  have hX_int : Integrable X μ := Integrable.of_mem_Icc (-b) b hX.aemeasurable hIcc
  have hmean_trim : μ[X | m] =ᵐ[μ.trim hm] 0 :=
    (stronglyMeasurable_condExp.ae_eq_trim_iff hm stronglyMeasurable_const).2 hmean
  have hzero_kernel :
      ∀ᵐ ω ∂μ.trim hm, ∫ y, X y ∂condExpKernel (mΩ := mΩ) μ m ω = 0 := by
    exact (condExp_ae_eq_trim_integral_condExpKernel (mΩ := mΩ) hm hX_int).symm.trans
      hmean_trim
  have hbound_kernel :
      ∀ᵐ ω ∂μ.trim hm, ∀ᵐ y ∂condExpKernel (mΩ := mΩ) μ m ω,
        X y ∈ Set.Icc (-b) b := by
    have hcomp : condExpKernel (mΩ := mΩ) μ m ∘ₘ μ.trim hm = μ :=
      condExpKernel_comp_trim (mΩ := mΩ) hm
    apply Measure.ae_ae_of_ae_comp
    rw [hcomp]
    exact hIcc
  change Kernel.HasSubgaussianMGF X ⟨b ^ 2, sq_nonneg b⟩
    (condExpKernel (mΩ := mΩ) μ m) (μ.trim hm)
  refine Kernel.HasSubgaussianMGF.of_rat ?_ ?_
  · intro t
    rw [condExpKernel_comp_trim (mΩ := mΩ) hm]
    exact integrable_exp_mul_of_mem_Icc hX.aemeasurable hIcc
  · intro q
    filter_upwards [hzero_kernel, hbound_kernel] with ω hzero hω
    have : IsProbabilityMeasure (condExpKernel (mΩ := mΩ) μ m ω) :=
      (inferInstance : IsMarkovKernel (condExpKernel (mΩ := mΩ) μ m)).isProbabilityMeasure ω
    have hsub := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (hX.aemeasurable) hω hzero
    have hparam : ((‖b - -b‖₊ / 2) ^ 2 : ℝ≥0) = ⟨b ^ 2, sq_nonneg b⟩ := by
      apply Subtype.ext
      simp only [sub_neg_eq_add, NNReal.val_eq_coe, NNReal.coe_pow, NNReal.coe_div, coe_nnnorm,
        norm_eq_abs, NNReal.coe_ofNat]
      rw [abs_of_nonneg (by positivity : 0 ≤ b + b)]
      ring
    rw [hparam] at hsub
    exact hsub.mgf_le q

/-- **Azuma-Hoeffding inequality.** Let `Y i` be a strongly adapted sequence of martingale
differences with `|Y i| ≤ b i` almost surely, mean zero at time zero, and conditional mean zero at
each later step. Then the upper tail of the sum of its first `n` terms is bounded by
`exp (-ε ^ 2 / (2 * ∑ i < n, b i ^ 2))`. -/
theorem measureReal_sum_range_ge_le_of_bounded_martingale_differences
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {Y : ℕ → Ω → ℝ} {b : ℕ → ℝ≥0}
    (h_adapted : StronglyAdapted ℱ Y)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ (b i : ℝ))
    (hmean0 : ∫ ω, Y 0 ω ∂μ = 0)
    (hmean : ∀ i, μ[Y (i + 1) | ℱ i] =ᵐ[μ] 0)
    (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω} ≤
      exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, (b i : ℝ) ^ 2)) := by
  let c : ℕ → ℝ≥0 := fun i => b i ^ 2
  have hparam (i : ℕ) :
      ((‖(b i : ℝ) - -(b i : ℝ)‖₊ / 2) ^ 2 : ℝ≥0) = c i := by
    apply Subtype.ext
    simp only [sub_neg_eq_add, NNReal.val_eq_coe, NNReal.coe_pow, NNReal.coe_div, coe_nnnorm,
      norm_eq_abs, NNReal.coe_ofNat]
    rw [abs_of_nonneg (by positivity : 0 ≤ (b i : ℝ) + (b i : ℝ))]
    simp only [c, NNReal.coe_pow]
    ring
  have hparam_sq (i : ℕ) :
      (⟨(b i : ℝ) ^ 2, sq_nonneg (b i : ℝ)⟩ : ℝ≥0) = c i := by
    apply Subtype.ext
    simp [c, NNReal.coe_pow]
  have hIcc0 : ∀ᵐ ω ∂μ, Y 0 ω ∈ Set.Icc (-(b 0 : ℝ)) (b 0 : ℝ) := by
    filter_upwards [hbound 0] with ω hω
    exact abs_le.mp hω
  have h0 := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    ((h_adapted 0).mono (ℱ.le 0)).measurable.aemeasurable hIcc0 hmean0
  rw [hparam 0] at h0
  have hsubG : ∀ i < n - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (c (i + 1)) μ := by
    intro i hi
    have hYi : Measurable[mΩ] (Y (i + 1)) :=
      ((h_adapted (i + 1)).mono (ℱ.le (i + 1))).measurable
    have hYi_subG := hasCondSubgaussianMGF_of_bounded (ℱ.le i)
      (NNReal.coe_nonneg _) hYi (hbound (i + 1)) (hmean i)
    rw [hparam_sq (i + 1)] at hYi_subG
    exact hYi_subG
  have htail := measure_sum_ge_le_of_hasCondSubgaussianMGF
    h_adapted h0 n hsubG hε
  simpa [c, NNReal.coe_pow] using htail

/-- **Two-sided Azuma-Hoeffding inequality.** Under the same assumptions as
`measureReal_sum_range_ge_le_of_bounded_martingale_differences`, the absolute value of the sum
exceeds `ε` with probability at most twice the one-sided bound. -/
theorem measureReal_abs_sum_range_ge_le_of_bounded_martingale_differences
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {Y : ℕ → Ω → ℝ} {b : ℕ → ℝ≥0}
    (h_adapted : StronglyAdapted ℱ Y)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ (b i : ℝ))
    (hmean0 : ∫ ω, Y 0 ω ∂μ = 0)
    (hmean : ∀ i, μ[Y (i + 1) | ℱ i] =ᵐ[μ] 0)
    (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i ∈ Finset.range n, Y i ω|} ≤
      2 * exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, (b i : ℝ) ^ 2)) := by
  have hneg_adapted : StronglyAdapted ℱ (fun i ω ↦ -Y i ω) := by
    intro i
    exact (h_adapted i).neg
  have hneg_bound : ∀ i, ∀ᵐ ω ∂μ, |-(Y i ω)| ≤ (b i : ℝ) := by
    intro i
    simpa using hbound i
  have hneg_mean0 : ∫ ω, -Y 0 ω ∂μ = 0 := by
    simp [integral_neg, hmean0]
  have hneg_mean : ∀ i, μ[-Y (i + 1) | ℱ i] =ᵐ[μ] 0 := by
    intro i
    calc
      μ[-Y (i + 1) | ℱ i] =ᵐ[μ] -μ[Y (i + 1) | ℱ i] := condExp_neg _ _
      _ =ᵐ[μ] 0 := by simpa using (hmean i).neg
  have hupper := measureReal_sum_range_ge_le_of_bounded_martingale_differences
    h_adapted hbound hmean0 hmean n hε
  have hlower := measureReal_sum_range_ge_le_of_bounded_martingale_differences
    hneg_adapted hneg_bound hneg_mean0 hneg_mean n hε
  simp only [Finset.sum_neg_distrib] at hlower
  calc
    μ.real {ω | ε ≤ |∑ i ∈ Finset.range n, Y i ω|}
      ≤ μ.real ({ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω} ∪
          {ω | ε ≤ -∑ i ∈ Finset.range n, Y i ω}) := by
        refine measureReal_mono fun ω hω ↦ ?_
        simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
        rcases le_abs'.1 hω with h | h
        · exact Or.inr (by linarith)
        · exact Or.inl h
    _ ≤ _ := (measureReal_union_le _ _).trans (by linarith)

end ProbabilityTheory
