/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Basic

/-!
# Sub-exponential random variables

A real random variable is sub-exponential with parameter `K` when its centered exponential
moments exist and are bounded by `exp (K ^ 2 * t ^ 2)` for `|t| ≤ 1 / K`. Independent centered
variables with a common parameter satisfy a two-sided Bernstein tail bound.

## References

* RandomMatrices roadmap, §2.1.
* R. Vershynin, *High-Dimensional Probability*, Cambridge University Press (2018), §2.7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A real random variable is sub-exponential with parameter `K` if `K > 0`, it is measurable
and integrable, and its centered exponential moments are integrable and bounded by
`exp (K ^ 2 * t ^ 2)` for every `|t| ≤ 1 / K`. -/
structure HasSubexponentialMGF (X : Ω → ℝ) (K : ℝ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] : Prop where
  parameter_pos : 0 < K
  measurable : Measurable X
  integrable : Integrable X μ
  integrable_exp_mul_centered : ∀ t : ℝ, |t| ≤ K⁻¹ →
    Integrable (fun ω => exp (t * (X ω - μ[X]))) μ
  centered_mgf_le : ∀ t : ℝ, |t| ≤ K⁻¹ →
    mgf (fun ω => X ω - μ[X]) μ t ≤ exp (K ^ 2 * t ^ 2)

namespace HasSubexponentialMGF

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {K t : ℝ}

/-- Negating a sub-exponential variable preserves its parameter. -/
theorem neg (h : HasSubexponentialMGF X K μ) : HasSubexponentialMGF (-X) K μ := by
  have hmean : μ[-X] = -μ[X] := by simp [integral_neg]
  have hcenter : (fun ω => -X ω - μ[-X]) = fun ω => -(X ω - μ[X]) := by
    funext ω
    rw [hmean]
    ring
  refine ⟨h.parameter_pos, measurable_neg.comp h.measurable, h.integrable.neg, ?_, ?_⟩
  · intro t ht
    have hexp : (fun ω => exp (t * ((-X) ω - μ[-X]))) =
        fun ω => exp ((-t) * (X ω - μ[X])) := by
      funext ω
      rw [hmean]
      congr 1
      simp only [Pi.neg_apply]
      ring
    rw [hexp]
    exact h.integrable_exp_mul_centered (-t) (by simpa using ht)
  · intro t ht
    calc
      mgf (fun ω => -X ω - μ[-X]) μ t =
          mgf (fun ω => -(X ω - μ[X])) μ t := by
        exact congrArg (fun f : Ω → ℝ => mgf f μ t) hcenter
      _ = mgf (fun ω => X ω - μ[X]) μ (-t) := by
        change mgf (-(fun ω => X ω - μ[X])) μ t = _
        exact mgf_neg
      _ ≤ exp (K ^ 2 * (-t) ^ 2) :=
        h.centered_mgf_le (-t) (by simpa using ht)
      _ = exp (K ^ 2 * t ^ 2) := by simp

end HasSubexponentialMGF

end TauCeti.Probability

namespace ProbabilityTheory.iIndepFun

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Type*} {X : ι → Ω → ℝ}

/-- The MGF of a finite sum of independent, centered sub-exponential variables is bounded by
the product of their individual quadratic MGF bounds. -/
theorem mgf_sum_le_exp_of_hasSubexponentialMGF (h_indep : iIndepFun X μ) {s : Finset ι}
    {K t : ℝ} (hX : ∀ i, HasSubexponentialMGF (X i) K μ)
    (hmean : ∀ i, μ[X i] = 0) (ht : |t| ≤ K⁻¹) :
    mgf (fun ω => ∑ i ∈ s, X i ω) μ t ≤
      exp ((s.card : ℝ) * K ^ 2 * t ^ 2) := by
  have hprod :
      mgf (fun ω => ∑ i ∈ s, X i ω) μ t = ∏ i ∈ s, mgf (X i) μ t := by
    have h := (h_indep.precomp Subtype.val_injective).mgf_sum₀
      (fun i : s => (hX i).measurable.aemeasurable) Finset.univ (t := t)
    rw [Finset.prod_coe_sort s (fun i => mgf (X i) μ t)] at h
    rw [← h]
    congr 1
    ext ω
    simp only [Finset.sum_apply]
    exact (Finset.sum_coe_sort s (fun i => X i ω)).symm
  rw [hprod]
  calc
    ∏ i ∈ s, mgf (X i) μ t ≤ ∏ i ∈ s, exp (K ^ 2 * t ^ 2) := by
      apply Finset.prod_le_prod₀ (fun i _ => mgf_nonneg)
      intro i hi
      have hbound := (hX i).centered_mgf_le t ht
      simpa [hmean i] using hbound
    _ = exp ((s.card : ℝ) * K ^ 2 * t ^ 2) := by
      rw [Finset.prod_const, ← exp_nat_mul]
      congr 1
      ring

/-- **Sub-exponential Bernstein inequality.** If the `Xᵢ`, `i ∈ s`, are independent, centered
and sub-exponential with common parameter `K`, then for `t > 0`

`P(|∑ i ∈ s, Xᵢ| ≥ t) ≤ 2 * exp (-t^2 / (4 * (|s| * K^2 + K * t)))`.

The constants follow directly from the centered MGF bound `E exp (λ Xᵢ) ≤ exp (K ^ 2 * λ ^ 2)`
for `|λ| ≤ 1 / K`. -/
theorem measureReal_abs_sum_ge_le_of_hasSubexponentialMGF (h_indep : iIndepFun X μ)
    {s : Finset ι} {K t : ℝ} (hK : 0 < K)
    (hX : ∀ i, HasSubexponentialMGF (X i) K μ)
    (hmean : ∀ i, μ[X i] = 0) (ht : 0 < t) :
    μ.real {ω | t ≤ |∑ i ∈ s, X i ω|} ≤
      2 * exp (-t ^ 2 / (4 * ((s.card : ℝ) * K ^ 2 + K * t))) := by
  let V : ℝ := (s.card : ℝ) * K ^ 2
  let D : ℝ := V + K * t
  have hV : 0 ≤ V := by positivity
  have hD : 0 < D := by
    dsimp [D]
    positivity
  let θ : ℝ := t / (2 * D)
  have hθ : 0 < θ := by
    dsimp [θ]
    positivity
  have hθle : θ ≤ K⁻¹ := by
    calc
      θ ≤ (2 * K)⁻¹ := by
        dsimp [θ]
        rw [← one_div]
        have hden : 0 < 2 * D := mul_pos (by norm_num) hD
        have hKden : 0 < 2 * K := mul_pos (by norm_num) hK
        apply (div_le_div_iff₀ hden hKden).2
        nlinarith [hV, mul_pos hK ht]
      _ ≤ K⁻¹ := by
        rw [← one_div, ← one_div]
        rw [div_le_div_iff₀ (mul_pos (by norm_num) hK) hK]
        nlinarith [hK]
  have hθbound : |θ| ≤ K⁻¹ := by
    rw [abs_of_pos hθ]
    exact hθle
  have hupperInt : Integrable (fun ω => exp (θ * (∑ i ∈ s, X i ω))) μ :=
    by
      simpa only [Finset.sum_apply] using
        h_indep.integrable_exp_mul_sum (fun i => (hX i).measurable) (fun i _ => by
          simpa [hmean i] using (hX i).integrable_exp_mul_centered θ hθbound)
  have hexponent : -θ * t + V * θ ^ 2 ≤ -t ^ 2 / (4 * D) := by
    dsimp [θ, D, V]
    field_simp
    have hVle : (s.card : ℝ) * K ^ 2 ≤ (s.card : ℝ) * K ^ 2 + K * t := by
      nlinarith [mul_pos hK ht]
    nlinarith [sq_nonneg t, mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hVle)]
  have hupper :
      μ.real {ω | t ≤ ∑ i ∈ s, X i ω} ≤
        exp (-t ^ 2 / (4 * D)) := by
    have hmgf := ProbabilityTheory.iIndepFun.mgf_sum_le_exp_of_hasSubexponentialMGF
      (s := s) h_indep hX hmean hθbound
    calc
      μ.real {ω | t ≤ ∑ i ∈ s, X i ω}
          ≤ exp (-θ * t) * mgf (fun ω => ∑ i ∈ s, X i ω) μ θ :=
            measure_ge_le_exp_mul_mgf t hθ.le hupperInt
      _ ≤ exp (-θ * t) * exp (V * θ ^ 2) := by
        gcongr
      _ = exp (-θ * t + V * θ ^ 2) := by rw [exp_add]
      _ ≤ exp (-t ^ 2 / (4 * D)) := (exp_le_exp).2 hexponent
  have hneg_indep : iIndepFun (fun i ω => -X i ω) μ :=
    h_indep.comp (fun _ => Neg.neg) (fun _ => measurable_neg)
  have hnegX : ∀ i, HasSubexponentialMGF (-X i) K μ := fun i => (hX i).neg
  have hnegmean : ∀ i, μ[-X i] = 0 := fun i => by
    simp [integral_neg, hmean i]
  have hsum_neg (ω : Ω) : ∑ i ∈ s, -X i ω = -(∑ i ∈ s, X i ω) := by
    rw [Finset.sum_neg_distrib]
  have hnegInt : Integrable (fun ω => exp (θ * (∑ i ∈ s, -X i ω))) μ := by
    have hnegθbound : |-θ| ≤ K⁻¹ := by simpa using hθbound
    have hbase : Integrable (fun ω => exp ((-θ) * (∑ i ∈ s, X i ω))) μ := by
      simpa only [Finset.sum_apply] using
        h_indep.integrable_exp_mul_sum (fun i => (hX i).measurable) (fun i _ => by
          simpa [hmean i] using
            (hX i).integrable_exp_mul_centered (-θ) hnegθbound)
    convert hbase using 1
    ext ω
    rw [hsum_neg]
    congr 1
    ring
  have hnegMgf := ProbabilityTheory.iIndepFun.mgf_sum_le_exp_of_hasSubexponentialMGF
    (X := fun i ω => -X i ω) (s := s) hneg_indep hnegX hnegmean hθbound
  have hlower :
      μ.real {ω | t ≤ -∑ i ∈ s, X i ω} ≤
        exp (-t ^ 2 / (4 * D)) := by
    have hset : {ω | t ≤ -∑ i ∈ s, X i ω} =
        {ω | t ≤ ∑ i ∈ s, -X i ω} := by
      ext ω
      change (t ≤ -(∑ i ∈ s, X i ω)) ↔ t ≤ ∑ i ∈ s, -X i ω
      exact (Iff.of_eq (congrArg (fun y : ℝ => t ≤ y) (hsum_neg ω))).symm
    rw [hset]
    calc
      μ.real {ω | t ≤ ∑ i ∈ s, -X i ω}
          ≤ exp (-θ * t) * mgf (fun ω => ∑ i ∈ s, -X i ω) μ θ :=
            measure_ge_le_exp_mul_mgf t hθ.le hnegInt
      _ ≤ exp (-θ * t) * exp (V * θ ^ 2) := by
        gcongr
      _ = exp (-θ * t + V * θ ^ 2) := by rw [exp_add]
      _ ≤ exp (-t ^ 2 / (4 * D)) := (exp_le_exp).2 hexponent
  have hboth :
      μ.real ({ω | t ≤ ∑ i ∈ s, X i ω} ∪ {ω | t ≤ -∑ i ∈ s, X i ω}) ≤
        2 * exp (-t ^ 2 / (4 * D)) := by
    calc
      μ.real ({ω | t ≤ ∑ i ∈ s, X i ω} ∪ {ω | t ≤ -∑ i ∈ s, X i ω})
          ≤ μ.real {ω | t ≤ ∑ i ∈ s, X i ω} +
              μ.real {ω | t ≤ -∑ i ∈ s, X i ω} :=
            measureReal_union_le _ _
      _ ≤ exp (-t ^ 2 / (4 * D)) + exp (-t ^ 2 / (4 * D)) := by
        exact add_le_add hupper hlower
      _ = 2 * exp (-t ^ 2 / (4 * D)) := by ring
  have hsubset :
      {ω | t ≤ |∑ i ∈ s, X i ω|} ⊆
        {ω | t ≤ ∑ i ∈ s, X i ω} ∪ {ω | t ≤ -∑ i ∈ s, X i ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    by_cases hsum : 0 ≤ ∑ i ∈ s, X i ω
    · left
      simpa [abs_of_nonneg hsum] using hω
    · right
      have hsum_neg : ∑ i ∈ s, X i ω < 0 := lt_of_not_ge hsum
      simpa [abs_of_neg hsum_neg] using hω
  calc
    μ.real {ω | t ≤ |∑ i ∈ s, X i ω|}
        ≤ μ.real ({ω | t ≤ ∑ i ∈ s, X i ω} ∪ {ω | t ≤ -∑ i ∈ s, X i ω}) :=
          measureReal_mono hsubset
    _ ≤ 2 * exp (-t ^ 2 / (4 * ((s.card : ℝ) * K ^ 2 + K * t))) := by
      simpa [D, V] using hboth

end ProbabilityTheory.iIndepFun
