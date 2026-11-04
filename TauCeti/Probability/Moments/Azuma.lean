/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.SubGaussian
import TauCeti.MeasureTheory.Measure.Tail

/-!
# Azuma-Hoeffding inequality

This file proves the Azuma-Hoeffding tail bound for a finite sum of bounded martingale
differences. The conditional form of Hoeffding's lemma turns each bounded, conditionally centered
increment into a conditionally sub-Gaussian random variable; Mathlib's sub-Gaussian martingale
inequality then controls the sum.

## Main results

* `TauCeti.Probability.hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero` — conditional
  Hoeffding's lemma for an arbitrary interval;
* `TauCeti.Probability.measureReal_sum_range_ge_le_of_mem_Icc_martingale_differences` — the
  one-sided Azuma-Hoeffding inequality with interval bounds;
* `TauCeti.Probability.measureReal_sum_range_ge_le_of_bounded_martingale_differences` — the
  one-sided Azuma-Hoeffding inequality for increments with `|Y i| ≤ b i`;
* `TauCeti.Probability.measureReal_abs_sum_range_ge_le_of_mem_Icc_martingale_differences` — its
  two-sided interval-bounded form;
* `TauCeti.Probability.measureReal_abs_sum_range_ge_le_of_bounded_martingale_differences` — the
  two-sided bounded-increment form.

## References

* K. Azuma, *Weighted sums of certain dependent random variables*, Tohoku Mathematical Journal 19
  (1967), 357-367.
* C. McDiarmid, *On the method of bounded differences*, in *Surveys in Combinatorics*, 1989,
  London Math. Soc. Lecture Note Ser. 141, Cambridge Univ. Press (1989), 148-188.
-/

public section

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-- A conditionally centered random variable whose values lie in `[a, b]` is conditionally
sub-Gaussian with parameter `((‖b - a‖₊ / 2) ^ 2)`. -/
theorem hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero [StandardBorelSpace Ω]
    [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {X : Ω → ℝ} {a b : ℝ}
    (hX : Measurable[mΩ] X) (hbound : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hmean : μ[X | m] =ᵐ[μ] 0) :
    HasCondSubgaussianMGF m hm X ((‖b - a‖₊ / 2) ^ 2) μ := by
  have hX_int : Integrable X μ := Integrable.of_mem_Icc a b hX.aemeasurable hbound
  have hmean_trim : μ[X | m] =ᵐ[μ.trim hm] 0 :=
    (stronglyMeasurable_condExp.ae_eq_trim_iff hm stronglyMeasurable_const).2 hmean
  have hzero_kernel :
      ∀ᵐ ω ∂μ.trim hm, ∫ y, X y ∂condExpKernel (mΩ := mΩ) μ m ω = 0 := by
    exact (condExp_ae_eq_trim_integral_condExpKernel (mΩ := mΩ) hm hX_int).symm.trans
      hmean_trim
  have hbound_kernel :
      ∀ᵐ ω ∂μ.trim hm, ∀ᵐ y ∂condExpKernel (mΩ := mΩ) μ m ω,
        X y ∈ Set.Icc a b := by
    have hcomp : condExpKernel (mΩ := mΩ) μ m ∘ₘ μ.trim hm = μ :=
      condExpKernel_comp_trim (mΩ := mΩ) hm
    apply Measure.ae_ae_of_ae_comp
    rw [hcomp]
    exact hbound
  -- The conditional predicate is the kernel-level sub-Gaussian bound.
  change Kernel.HasSubgaussianMGF X ((‖b - a‖₊ / 2) ^ 2)
    (condExpKernel (mΩ := mΩ) μ m) (μ.trim hm)
  refine Kernel.HasSubgaussianMGF.of_rat ?_ ?_
  · intro t
    rw [condExpKernel_comp_trim (mΩ := mΩ) hm]
    exact integrable_exp_mul_of_mem_Icc hX.aemeasurable hbound
  · intro q
    filter_upwards [hzero_kernel, hbound_kernel] with ω hzero hω
    have : IsProbabilityMeasure (condExpKernel (mΩ := mΩ) μ m ω) :=
      (inferInstance : IsMarkovKernel (condExpKernel (mΩ := mΩ) μ m)).isProbabilityMeasure ω
    have hsub := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      hX.aemeasurable hω hzero
    exact hsub.mgf_le q

/-- **Azuma-Hoeffding inequality for interval-bounded martingale differences.** Let `Y i` be a
strongly adapted sequence with conditionally centered increments in `[a i, b i]` almost surely.
Then the upper tail is bounded using Hoeffding's variance proxy
`∑ i < n, ((‖b i - a i‖₊ / 2) ^ 2)`. -/
theorem measureReal_sum_range_ge_le_of_mem_Icc_martingale_differences
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {Y : ℕ → Ω → ℝ} {a b : ℕ → ℝ}
    (h_adapted : StronglyAdapted ℱ Y) (n : ℕ)
    (hbound : ∀ i < n, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (a i) (b i))
    (hmean0 : ∫ ω, Y 0 ω ∂μ = 0)
    (hmean : ∀ i < n - 1, μ[Y (i + 1) | ℱ i] =ᵐ[μ] 0)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω} ≤
      exp (-ε ^ 2 /
        (2 * ∑ i ∈ Finset.range n, ((‖b i - a i‖₊ / 2) ^ 2 : ℝ))) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [measureReal_le_one]
  let c : ℕ → ℝ≥0 := fun i => (‖b i - a i‖₊ / 2) ^ 2
  have h0 : HasSubgaussianMGF (Y 0) (c 0) μ := by
    simpa [c] using
      (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        ((h_adapted 0).mono (ℱ.le 0)).measurable.aemeasurable (hbound 0 hn) hmean0)
  have hsubG : ∀ i < n - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (c (i + 1)) μ := by
    intro i hi
    have hYi : Measurable[mΩ] (Y (i + 1)) :=
      ((h_adapted (i + 1)).mono (ℱ.le (i + 1))).measurable
    simpa [c] using
      (hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero (ℱ.le i) hYi
        (hbound (i + 1) (by omega)) (hmean i hi))
  have htail := measure_sum_ge_le_of_hasCondSubgaussianMGF
    h_adapted h0 n hsubG hε
  simpa [c] using htail

/-- **Azuma-Hoeffding inequality.** Let `Y i` be a strongly adapted sequence of martingale
differences with `|Y i| ≤ b i` almost surely, mean zero at time zero, and conditional mean zero at
each later step. Then the upper tail of the sum of its first `n` terms is bounded by
`exp (-ε ^ 2 / (2 * ∑ i < n, b i ^ 2))`. -/
theorem measureReal_sum_range_ge_le_of_bounded_martingale_differences
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {Y : ℕ → Ω → ℝ} {b : ℕ → ℝ≥0}
    (h_adapted : StronglyAdapted ℱ Y) (n : ℕ)
    (hbound : ∀ i < n, ∀ᵐ ω ∂μ, |Y i ω| ≤ (b i : ℝ))
    (hmean0 : ∫ ω, Y 0 ω ∂μ = 0)
    (hmean : ∀ i < n - 1, μ[Y (i + 1) | ℱ i] =ᵐ[μ] 0)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω} ≤
      exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, (b i : ℝ) ^ 2)) := by
  have hIcc : ∀ i < n, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (-(b i : ℝ)) (b i : ℝ) := by
    intro i hi
    filter_upwards [hbound i hi] with ω hω
    exact abs_le.mp hω
  have hterm (i : ℕ) :
      ((‖(b i : ℝ) - -(b i : ℝ)‖₊ / 2) ^ 2 : ℝ) = (b i : ℝ) ^ 2 := by
    simp only [coe_nnnorm, Real.norm_eq_abs, sub_neg_eq_add]
    rw [abs_of_nonneg (by positivity : 0 ≤ (b i : ℝ) + (b i : ℝ))]
    ring
  have hbound' := measureReal_sum_range_ge_le_of_mem_Icc_martingale_differences
      (a := fun i => -(b i : ℝ)) (b := fun i => (b i : ℝ))
      h_adapted n hIcc hmean0 hmean hε
  simp_rw [hterm] at hbound'
  exact hbound'

/-- **Two-sided Azuma-Hoeffding inequality for interval-bounded martingale differences.** Under
the assumptions of the one-sided interval theorem, the absolute value of the sum exceeds `ε` with
probability at most twice its one-sided bound. -/
theorem measureReal_abs_sum_range_ge_le_of_mem_Icc_martingale_differences
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {Y : ℕ → Ω → ℝ} {a b : ℕ → ℝ}
    (h_adapted : StronglyAdapted ℱ Y) (n : ℕ)
    (hbound : ∀ i < n, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (a i) (b i))
    (hmean0 : ∫ ω, Y 0 ω ∂μ = 0)
    (hmean : ∀ i < n - 1, μ[Y (i + 1) | ℱ i] =ᵐ[μ] 0)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i ∈ Finset.range n, Y i ω|} ≤
      2 * exp (-ε ^ 2 /
        (2 * ∑ i ∈ Finset.range n, ((‖b i - a i‖₊ / 2) ^ 2 : ℝ))) := by
  have hneg_adapted : StronglyAdapted ℱ (fun i ω ↦ -Y i ω) := by
    intro i
    exact (h_adapted i).neg
  have hneg_bound : ∀ i < n, ∀ᵐ ω ∂μ, -Y i ω ∈ Set.Icc (-b i) (-a i) := by
    intro i hi
    filter_upwards [hbound i hi] with ω hω
    exact ⟨neg_le_neg hω.2, neg_le_neg hω.1⟩
  have hneg_mean0 : ∫ ω, -Y 0 ω ∂μ = 0 := by
    simp [integral_neg, hmean0]
  have hneg_mean : ∀ i < n - 1, μ[-Y (i + 1) | ℱ i] =ᵐ[μ] 0 := by
    intro i hi
    calc
      μ[-Y (i + 1) | ℱ i] =ᵐ[μ] -μ[Y (i + 1) | ℱ i] := condExp_neg _ _
      _ =ᵐ[μ] 0 := by simpa using (hmean i hi).neg
  have hupper := measureReal_sum_range_ge_le_of_mem_Icc_martingale_differences
    h_adapted n hbound hmean0 hmean hε
  have hlower := measureReal_sum_range_ge_le_of_mem_Icc_martingale_differences
    (a := fun i => -b i) (b := fun i => -a i)
    hneg_adapted n hneg_bound hneg_mean0 hneg_mean hε
  have hwidth (i : ℕ) : abs (-a i + b i) = abs (b i - a i) := by
    congr 1
    ring
  have hlower' :
      μ.real {ω | ε ≤ -∑ i ∈ Finset.range n, Y i ω} ≤
        exp (-ε ^ 2 /
          (2 * ∑ i ∈ Finset.range n, ((‖b i - a i‖₊ / 2) ^ 2 : ℝ))) := by
    simpa [hwidth] using hlower
  calc
    μ.real {ω | ε ≤ |∑ i ∈ Finset.range n, Y i ω|}
      ≤ μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω} +
          μ.real {ω | ε ≤ -∑ i ∈ Finset.range n, Y i ω} :=
        TauCeti.measureReal_le_abs_le_add
    _ ≤ _ := (add_le_add hupper hlower').trans (le_of_eq (by ring))

/-- **Two-sided Azuma-Hoeffding inequality.** Under the assumptions of
`measureReal_sum_range_ge_le_of_bounded_martingale_differences`, the absolute value of the sum
exceeds `ε` with probability at most twice the one-sided bound. -/
theorem measureReal_abs_sum_range_ge_le_of_bounded_martingale_differences
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {Y : ℕ → Ω → ℝ} {b : ℕ → ℝ≥0}
    (h_adapted : StronglyAdapted ℱ Y) (n : ℕ)
    (hbound : ∀ i < n, ∀ᵐ ω ∂μ, |Y i ω| ≤ (b i : ℝ))
    (hmean0 : ∫ ω, Y 0 ω ∂μ = 0)
    (hmean : ∀ i < n - 1, μ[Y (i + 1) | ℱ i] =ᵐ[μ] 0)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i ∈ Finset.range n, Y i ω|} ≤
      2 * exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, (b i : ℝ) ^ 2)) := by
  have hIcc : ∀ i < n, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (-(b i : ℝ)) (b i : ℝ) := by
    intro i hi
    filter_upwards [hbound i hi] with ω hω
    exact abs_le.mp hω
  have hterm (i : ℕ) :
      ((‖(b i : ℝ) - -(b i : ℝ)‖₊ / 2) ^ 2 : ℝ) = (b i : ℝ) ^ 2 := by
    simp only [coe_nnnorm, Real.norm_eq_abs, sub_neg_eq_add]
    rw [abs_of_nonneg (by positivity : 0 ≤ (b i : ℝ) + (b i : ℝ))]
    ring
  have hbound' := measureReal_abs_sum_range_ge_le_of_mem_Icc_martingale_differences
    (a := fun i => -(b i : ℝ)) (b := fun i => (b i : ℝ))
    h_adapted n hIcc hmean0 hmean hε
  simp_rw [hterm] at hbound'
  exact hbound'

end TauCeti.Probability
