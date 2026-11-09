/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Moments.Basic

/-!
# Sub-exponential random variables

A real random variable is sub-exponential with parameter `K` when its centered exponential
moments exist and are bounded by `exp (K ^ 2 * t ^ 2)` for `|t| ≤ 1 / K`. Independent centered
variables with a common parameter satisfy a two-sided Bernstein tail bound.

## References

* R. Vershynin, *High-Dimensional Probability*, Cambridge University Press (2018), §2.7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A real random variable is sub-exponential with parameter `K` if `K > 0`, it is integrable,
and its centered exponential moments are integrable and bounded by
`exp (K ^ 2 * t ^ 2)` for every `|t| ≤ 1 / K`. -/
structure HasSubexponentialMGF (X : Ω → ℝ) (K : ℝ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] : Prop where
  parameter_pos : 0 < K
  integrable : Integrable X μ
  integrable_exp_mul_centered : ∀ t : ℝ, |t| ≤ K⁻¹ →
    Integrable (fun ω => exp (t * (X ω - μ[X]))) μ
  centered_mgf_le : ∀ t : ℝ, |t| ≤ K⁻¹ →
    mgf (fun ω => X ω - μ[X]) μ t ≤ exp (K ^ 2 * t ^ 2)

namespace HasSubexponentialMGF

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {K t : ℝ}

/-- Centering a sub-exponential random variable preserves its parameter. -/
theorem center (h : HasSubexponentialMGF X K μ) :
    HasSubexponentialMGF (fun ω => X ω - μ[X]) K μ := by
  have hmean : μ[fun ω => X ω - μ[X]] = 0 := by
    rw [integral_sub h.integrable (integrable_const _)]
    simp [integral_const]
  have hcenter : (fun ω => (X ω - μ[X]) - μ[fun ω => X ω - μ[X]]) =
      fun ω => X ω - μ[X] := by
    funext ω
    rw [hmean, sub_zero]
  refine ⟨h.parameter_pos, h.integrable.sub (integrable_const _), ?_, ?_⟩
  · intro t ht
    have hexp :
        (fun ω => exp (t * (X ω - μ[X]))) =
          fun ω => exp (t * ((X ω - μ[X]) - μ[fun ω => X ω - μ[X]])) :=
      congrArg (fun f : Ω → ℝ => fun ω => exp (t * f ω)) hcenter.symm
    exact (h.integrable_exp_mul_centered t ht).congr
      (Filter.Eventually.of_forall fun ω => congrFun hexp ω)
  · intro t ht
    calc
      mgf (fun ω => (X ω - μ[X]) - μ[fun ω => X ω - μ[X]]) μ t =
          mgf (fun ω => X ω - μ[X]) μ t :=
        congrArg (fun f : Ω → ℝ => mgf f μ t) hcenter
      _ ≤ exp (K ^ 2 * t ^ 2) := h.centered_mgf_le t ht

/-- Negating a sub-exponential variable preserves its parameter. -/
theorem neg (h : HasSubexponentialMGF X K μ) : HasSubexponentialMGF (-X) K μ := by
  have hmean : μ[-X] = -μ[X] := by simp [integral_neg]
  have hcenter : (fun ω => -X ω - μ[-X]) = fun ω => -(X ω - μ[X]) := by
    funext ω
    rw [hmean]
    ring
  refine ⟨h.parameter_pos, h.integrable.neg, ?_, ?_⟩
  · intro t ht
    have hexp : (fun ω => exp (t * ((-X) ω - μ[-X]))) =
        fun ω => exp ((-t) * (X ω - μ[X])) := by
      funext ω
      rw [hmean]
      simp only [Pi.neg_apply]
      congr 1
      ring
    rw [hexp]
    exact h.integrable_exp_mul_centered (-t) (by simpa using ht)
  · intro t ht
    calc
      mgf (fun ω => -X ω - μ[-X]) μ t =
          mgf (fun ω => -(X ω - μ[X])) μ t := by
        exact congrArg (fun f : Ω → ℝ => mgf f μ t) hcenter
      _ = mgf (fun ω => X ω - μ[X]) μ (-t) := by
        have hpoint : (fun ω => -(X ω - μ[X])) = -(fun ω => X ω - μ[X]) := by
          rfl
        rw [hpoint]
        exact mgf_neg (X := fun ω => X ω - μ[X]) (μ := μ) (t := t)
      _ ≤ exp (K ^ 2 * (-t) ^ 2) :=
        h.centered_mgf_le (-t) (by simpa using ht)
      _ = exp (K ^ 2 * t ^ 2) := by simp

end HasSubexponentialMGF

end TauCeti.Probability

namespace ProbabilityTheory.iIndepFun

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Type*} {X : ι → Ω → ℝ} {t : ℝ}

/-- The MGF of a finite sum of independent, centered sub-exponential variables is bounded by
the product of their individual quadratic MGF bounds. -/
theorem mgf_sum_le_exp_of_hasSubexponentialMGF (h_indep : iIndepFun X μ) {s : Finset ι}
    {K t : ℝ} (hX : ∀ i ∈ s, HasSubexponentialMGF (X i) K μ)
    (hmean : ∀ i ∈ s, μ[X i] = 0) (ht : |t| ≤ K⁻¹) :
    mgf (fun ω => ∑ i ∈ s, X i ω) μ t ≤
      exp ((s.card : ℝ) * K ^ 2 * t ^ 2) := by
  have hprod :
      mgf (fun ω => ∑ i ∈ s, X i ω) μ t = ∏ i ∈ s, mgf (X i) μ t :=
    h_indep.mgf_sum_of_aemeasurable fun i hi =>
      (hX i hi).integrable.aestronglyMeasurable.aemeasurable
  rw [hprod]
  calc
    ∏ i ∈ s, mgf (X i) μ t ≤ ∏ i ∈ s, exp (K ^ 2 * t ^ 2) := by
      apply Finset.prod_le_prod₀ (fun i _ => mgf_nonneg)
      intro i hi
      have hbound := (hX i hi).centered_mgf_le t ht
      simpa [hmean i hi] using hbound
    _ = exp ((s.card : ℝ) * K ^ 2 * t ^ 2) := by
      rw [Finset.prod_const, ← exp_nat_mul]
      congr 1
      ring

/-- **One-sided sub-exponential Bernstein inequality.** For independent centered variables with
common parameter `K`, this bounds the upper tail of a finite sum. -/
theorem measureReal_sum_ge_le_of_hasSubexponentialMGF (h_indep : iIndepFun X μ)
   {s : Finset ι} {K t : ℝ} (hK : 0 < K)
   (hX : ∀ i ∈ s, HasSubexponentialMGF (X i) K μ)
   (hmean : ∀ i ∈ s, μ[X i] = 0) (ht : 0 < t) :
   μ.real {ω | t ≤ ∑ i ∈ s, X i ω} ≤
     exp (-t ^ 2 / (4 * ((s.card : ℝ) * K ^ 2 + K * t))) := by
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
 have hupperInt : Integrable (fun ω => exp (θ * (∑ i ∈ s, X i ω))) μ := by
   exact integrable_exp_mul_sum_of_aemeasurable h_indep (s := s)
     (fun i hi => (hX i hi).integrable.aestronglyMeasurable.aemeasurable)
     (fun i hi => by
       simpa [hmean i hi] using (hX i hi).integrable_exp_mul_centered θ hθbound)
 have hexponent : -θ * t + V * θ ^ 2 ≤ -t ^ 2 / (4 * D) := by
   dsimp [θ, D, V]
   field_simp
   have hVle : (s.card : ℝ) * K ^ 2 ≤ (s.card : ℝ) * K ^ 2 + K * t := by
     nlinarith [mul_pos hK ht]
   nlinarith [sq_nonneg t, mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hVle)]
 have hmgf := ProbabilityTheory.iIndepFun.mgf_sum_le_exp_of_hasSubexponentialMGF
   (s := s) h_indep hX hmean hθbound
 calc
   μ.real {ω | t ≤ ∑ i ∈ s, X i ω}
       ≤ exp (-θ * t) * mgf (fun ω => ∑ i ∈ s, X i ω) μ θ :=
         measure_ge_le_exp_mul_mgf t hθ.le hupperInt
   _ ≤ exp (-θ * t) * exp (V * θ ^ 2) := by gcongr
   _ = exp (-θ * t + V * θ ^ 2) := by rw [exp_add]
   _ ≤ exp (-t ^ 2 / (4 * D)) := (exp_le_exp).2 hexponent
   _ = exp (-t ^ 2 / (4 * ((s.card : ℝ) * K ^ 2 + K * t))) := by rfl

/-- **Sub-exponential Bernstein inequality.** If the `Xᵢ`, `i ∈ s`, are independent, centered
and sub-exponential with common parameter `K`, then for `t > 0`

`P(|∑ i ∈ s, Xᵢ| ≥ t) ≤ 2 * exp (-t^2 / (4 * (|s| * K^2 + K * t)))`.

The constants follow directly from the centered MGF bound `E exp (λ Xᵢ) ≤ exp (K ^ 2 * λ ^ 2)`
for `|λ| ≤ 1 / K`. -/
theorem measureReal_abs_sum_ge_le_of_hasSubexponentialMGF (h_indep : iIndepFun X μ)
    {s : Finset ι} {K t : ℝ} (hK : 0 < K)
    (hX : ∀ i ∈ s, HasSubexponentialMGF (X i) K μ)
    (hmean : ∀ i ∈ s, μ[X i] = 0) (ht : 0 < t) :
    μ.real {ω | t ≤ |∑ i ∈ s, X i ω|} ≤
      2 * exp (-t ^ 2 / (4 * ((s.card : ℝ) * K ^ 2 + K * t))) := by
  have hupper := measureReal_sum_ge_le_of_hasSubexponentialMGF
    h_indep hK hX hmean ht
  have hneg_indep : iIndepFun (fun i ω => -X i ω) μ :=
    h_indep.comp (fun _ => Neg.neg) (fun _ => measurable_neg)
  have hnegX : ∀ i ∈ s, HasSubexponentialMGF (-X i) K μ := fun i hi => (hX i hi).neg
  have hnegmean : ∀ i ∈ s, μ[-X i] = 0 := fun i hi => by
    simp [integral_neg, hmean i hi]
  have hsum_neg (ω : Ω) : ∑ i ∈ s, -X i ω = -(∑ i ∈ s, X i ω) := by
    rw [Finset.sum_neg_distrib]
  have hlower :
      μ.real {ω | t ≤ -∑ i ∈ s, X i ω} ≤
        exp (-t ^ 2 / (4 * ((s.card : ℝ) * K ^ 2 + K * t))) := by
    have hset : {ω | t ≤ -∑ i ∈ s, X i ω} =
        {ω | t ≤ ∑ i ∈ s, -X i ω} := by
      ext ω
      simp only [Set.mem_ofPred_eq, hsum_neg ω]
    rw [hset]
    exact measureReal_sum_ge_le_of_hasSubexponentialMGF
      hneg_indep hK hnegX hnegmean ht
  have hboth :
      μ.real ({ω | t ≤ ∑ i ∈ s, X i ω} ∪ {ω | t ≤ -∑ i ∈ s, X i ω}) ≤
        2 * exp (-t ^ 2 / (4 * ((s.card : ℝ) * K ^ 2 + K * t))) := by
    calc
      μ.real ({ω | t ≤ ∑ i ∈ s, X i ω} ∪ {ω | t ≤ -∑ i ∈ s, X i ω})
          ≤ μ.real {ω | t ≤ ∑ i ∈ s, X i ω} +
              μ.real {ω | t ≤ -∑ i ∈ s, X i ω} :=
            measureReal_union_le _ _
      _ ≤ exp (-t ^ 2 / (4 * ((s.card : ℝ) * K ^ 2 + K * t))) +
          exp (-t ^ 2 / (4 * ((s.card : ℝ) * K ^ 2 + K * t))) := by
        exact add_le_add hupper hlower
      _ = 2 * exp (-t ^ 2 / (4 * ((s.card : ℝ) * K ^ 2 + K * t))) := by ring
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
    _ ≤ 2 * exp (-t ^ 2 / (4 * ((s.card : ℝ) * K ^ 2 + K * t))) := hboth

end ProbabilityTheory.iIndepFun
