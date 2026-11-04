/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.Analysis.SpecialFunctions.Exp.QuadraticBound
import TauCeti.Probability.Moments.Basic

/-!
# Bernstein's inequality

Let `X₁, …, Xₙ` be independent real random variables with mean zero, finite second moments and
`Xᵢ ≤ b` almost surely, and put `v = ∑ᵢ E Xᵢ²`. Bernstein's inequality bounds the upper tail of
`S = ∑ᵢ Xᵢ` by `exp (-ε ^ 2 / (2 * (v + b * ε / 3)))` for every `ε ≥ 0`. For moderate `ε` this is
the Gaussian tail with the true variance `v`, rather than the worst-case variance proxy of
Hoeffding's inequality (`ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`);
for large `ε` it decays exponentially at rate `3 / (2 b)`.

## Main results

* `MeasureTheory.MemLp.mgf_le_exp_of_ae_le`: if `E X = 0`, `E X² < ∞` and `X ≤ b` almost
  surely, then `E exp (t X) ≤ exp (E X² * t ^ 2 / (2 * (1 - t * b / 3)))` for `0 ≤ t` with
  `t * b < 3`;
* `ProbabilityTheory.iIndepFun.mgf_sum_le_exp_of_ae_le`: the same bound for an independent sum,
  with `E X²` replaced by `v`;
* `ProbabilityTheory.iIndepFun.measureReal_sum_ge_le_of_ae_le`: **Bernstein's inequality** for the
  upper tail;
* `ProbabilityTheory.iIndepFun.measureReal_abs_sum_ge_le_of_abs_le`: the two-sided form
  `P(|S| ≥ ε) ≤ 2 * exp (-ε ^ 2 / (2 * (v + b * ε / 3)))` when `|Xᵢ| ≤ b`.

## References

* S. Bernstein, *Theory of Probability* (in Russian), Moscow (1927).
* S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities: A Nonasymptotic Theory of
  Independence*, Oxford University Press (2013), §2.8.
-/

public section

open MeasureTheory ProbabilityTheory Real

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

namespace MeasureTheory.MemLp

/-- **Bernstein's moment-generating-function bound.** If `X` has mean zero, a finite second
moment and `X ≤ b` almost surely, then for `0 ≤ t` with `t * b < 3`,
`E exp (t X) ≤ exp (E X² * t ^ 2 / (2 * (1 - t * b / 3)))`. -/
theorem mgf_le_exp_of_ae_le [IsProbabilityMeasure μ] {X : Ω → ℝ} {b t : ℝ}
    (hX : MemLp X 2 μ) (hmean : μ[X] = 0) (hb : ∀ᵐ ω ∂μ, X ω ≤ b) (ht : 0 ≤ t)
    (htb : t * b < 3) :
    mgf X μ t ≤ exp ((∫ ω, X ω ^ 2 ∂μ) * t ^ 2 / (2 * (1 - t * b / 3))) := by
  have hXi : Integrable X μ := hX.integrable one_le_two
  have hX2 : Integrable (fun ω ↦ X ω ^ 2) μ := hX.integrable_sq
  have hb0 : 0 ≤ b := by simpa [hmean] using integral_mono_ae hXi (integrable_const b) hb
  set k : ℝ := t ^ 2 / (2 * (1 - t * b / 3))
  -- Pointwise, `exp (t X) ≤ 1 + t X + k X²` by `Real.exp_le_one_add_add_sq_div_of_le`.
  have hpt : ∀ᵐ ω ∂μ, exp (t * X ω) ≤ 1 + t * X ω + k * X ω ^ 2 := by
    filter_upwards [hb] with ω hω
    have := exp_le_one_add_add_sq_div_of_le (mul_le_mul_of_nonneg_left hω ht)
      (mul_nonneg ht hb0) htb
    convert this using 2
    ring
  have hint₁ : Integrable (fun ω ↦ 1 + t * X ω) μ := (integrable_const 1).add (hXi.const_mul t)
  have hint : Integrable (fun ω ↦ 1 + t * X ω + k * X ω ^ 2) μ := hint₁.add (hX2.const_mul k)
  calc mgf X μ t ≤ ∫ ω, (1 + t * X ω + k * X ω ^ 2) ∂μ :=
        integral_mono_ae (integrable_exp_mul_of_le t b ht hXi.aemeasurable hb) hint hpt
    _ = 1 + k * ∫ ω, X ω ^ 2 ∂μ := by
        rw [integral_add hint₁ (hX2.const_mul k),
          integral_add (integrable_const 1) (hXi.const_mul t), integral_const_mul,
          integral_const_mul, hmean]
        simp
    _ ≤ exp (k * ∫ ω, X ω ^ 2 ∂μ) := by linarith [add_one_le_exp (k * ∫ ω, X ω ^ 2 ∂μ)]
    _ = exp ((∫ ω, X ω ^ 2 ∂μ) * t ^ 2 / (2 * (1 - t * b / 3))) := by
        congr 1
        simp only [k]
        ring

end MeasureTheory.MemLp

namespace ProbabilityTheory.iIndepFun

/-- **Bernstein's moment-generating-function bound for independent sums.** If the `Xᵢ`, `i ∈ s`,
are independent with mean zero, finite second moments and `Xᵢ ≤ b` almost surely, then for
`0 ≤ t` with `t * b < 3` the moment-generating function of `∑ i ∈ s, Xᵢ` at `t` is at most
`exp (v * t ^ 2 / (2 * (1 - t * b / 3)))`, where `v = ∑ i ∈ s, E Xᵢ²`. -/
theorem mgf_sum_le_exp_of_ae_le {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {s : Finset ι} {b t : ℝ} (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hmean : ∀ i ∈ s, μ[X i] = 0)
    (hb : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ≤ b) (ht : 0 ≤ t) (htb : t * b < 3) :
    mgf (fun ω ↦ ∑ i ∈ s, X i ω) μ t ≤
      exp ((∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ) * t ^ 2 / (2 * (1 - t * b / 3))) := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  -- Restrict the family to `s`, where the measurability hypotheses hold.
  have hprod : mgf (fun ω ↦ ∑ i ∈ s, X i ω) μ t = ∏ i ∈ s, mgf (X i) μ t := by
    have h := (h_indep.precomp Subtype.val_injective).mgf_sum₀ (t := t)
      (fun i : s ↦ (hX i i.2).aestronglyMeasurable.aemeasurable) Finset.univ
    rw [Finset.prod_coe_sort s (fun i ↦ mgf (X i) μ t)] at h
    rw [← h]
    congr 1
    ext ω
    simp only [Finset.sum_apply]
    exact (Finset.sum_coe_sort s (fun i ↦ X i ω)).symm
  rw [hprod, Finset.sum_mul, Finset.sum_div, exp_sum]
  exact Finset.prod_le_prod₀ (fun i _ ↦ mgf_nonneg)
    (fun i hi ↦ (hX i hi).mgf_le_exp_of_ae_le (hmean i hi) (hb i hi) ht htb)

/-- **Bernstein's inequality.** Let the `Xᵢ`, `i ∈ s`, be independent with mean zero, finite
second moments and `Xᵢ ≤ b` almost surely, and let `v = ∑ i ∈ s, E Xᵢ²`. Then for `0 ≤ ε`,
`P(ε ≤ ∑ i ∈ s, Xᵢ) ≤ exp (-ε ^ 2 / (2 * (v + b * ε / 3)))`. -/
theorem measureReal_sum_ge_le_of_ae_le {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {s : Finset ι} {b ε : ℝ} (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hmean : ∀ i ∈ s, μ[X i] = 0)
    (hb : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ≤ b) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ s, X i ω} ≤
      exp (-ε ^ 2 / (2 * ((∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ) + b * ε / 3))) := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  set v := ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ
  have hv0 : 0 ≤ v := Finset.sum_nonneg fun i _ ↦ integral_nonneg fun ω ↦ sq_nonneg _
  rcases hε.eq_or_lt with rfl | hε
  · simp
  rcases hv0.eq_or_lt with hv | hv
  · -- Zero variance: the sum vanishes almost surely, so the event is null.
    have hzero := TauCeti.ae_sum_eq_zero_of_sum_integral_sq_eq_zero hX hv.symm
    have hnull : μ.real {ω | ε ≤ ∑ i ∈ s, X i ω} = 0 := by
      rw [measureReal_eq_zero_iff]
      refine measure_mono_null (fun ω hω ↦ ?_) (ae_iff.1 hzero)
      simp only [Set.mem_ofPred_eq] at hω ⊢
      linarith
    rw [hnull]
    positivity
  -- Positive variance: some `Xᵢ` is present, so `0 ≤ b`; optimise the Chernoff bound.
  obtain ⟨j, hj⟩ : s.Nonempty := Finset.nonempty_of_sum_ne_zero hv.ne'
  have hb0 : 0 ≤ b := by
    simpa [hmean j hj] using
      integral_mono_ae ((hX j hj).integrable one_le_two) (integrable_const b) (hb j hj)
  have hD : 0 < v + b * ε / 3 := by positivity
  set t := ε / (v + b * ε / 3)
  have ht : 0 ≤ t := by positivity
  have htb : t * b < 3 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hD]
    nlinarith
  have hS_le : ∀ᵐ ω ∂μ, ∑ i ∈ s, X i ω ≤ s.card * b := by
    filter_upwards [(Filter.eventually_all_finset s).2 hb] with ω hω
    simpa using Finset.sum_le_card_nsmul s (fun i ↦ X i ω) b hω
  have hS_meas : AEMeasurable (fun ω ↦ ∑ i ∈ s, X i ω) μ :=
    Finset.aemeasurable_fun_sum s fun i hi ↦ (hX i hi).aestronglyMeasurable.aemeasurable
  calc μ.real {ω | ε ≤ ∑ i ∈ s, X i ω}
      ≤ exp (-t * ε) * mgf (fun ω ↦ ∑ i ∈ s, X i ω) μ t :=
        measure_ge_le_exp_mul_mgf ε ht (integrable_exp_mul_of_le t _ ht hS_meas hS_le)
    _ ≤ exp (-t * ε) * exp (v * t ^ 2 / (2 * (1 - t * b / 3))) := by
        gcongr
        exact h_indep.mgf_sum_le_exp_of_ae_le hX hmean hb ht htb
    _ = exp (-ε ^ 2 / (2 * (v + b * ε / 3))) := by
        rw [← exp_add]
        congr 1
        have h3 : (1 - t * b / 3) = v / (v + b * ε / 3) := by
          simp only [t]
          field_simp
          ring
        rw [h3]
        simp only [t]
        field_simp
        ring

/-- **Bernstein's inequality, two-sided form.** Let the `Xᵢ`, `i ∈ s`, be independent and
almost-everywhere measurable with mean zero and `|Xᵢ| ≤ b` almost surely, and let
`v = ∑ i ∈ s, E Xᵢ²`. Then for `0 ≤ ε`,
`P(ε ≤ |∑ i ∈ s, Xᵢ|) ≤ 2 * exp (-ε ^ 2 / (2 * (v + b * ε / 3)))`. -/
theorem measureReal_abs_sum_ge_le_of_abs_le {ι : Type*} {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) {s : Finset ι} {b ε : ℝ} (hX : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hmean : ∀ i ∈ s, μ[X i] = 0) (hb : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ b) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i ∈ s, X i ω|} ≤
      2 * exp (-ε ^ 2 / (2 * ((∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ) + b * ε / 3))) := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  have hL2 : ∀ i ∈ s, MemLp (X i) 2 μ := fun i hi ↦
    MemLp.of_bound (hX i hi).aestronglyMeasurable b (by simpa using hb i hi)
  have hup : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ≤ b := fun i hi ↦ by
    filter_upwards [hb i hi] with ω hω using (le_abs_self _).trans hω
  -- The lower tail is the upper tail of the negated family.
  have hneg_indep : iIndepFun (fun i ω ↦ -X i ω) μ :=
    h_indep.comp (fun _ ↦ Neg.neg) fun _ ↦ measurable_neg
  have hlow := hneg_indep.measureReal_sum_ge_le_of_ae_le (s := s) (b := b)
    (fun i hi ↦ (hL2 i hi).neg) (fun i hi ↦ by simpa [integral_neg] using hmean i hi)
    (fun i hi ↦ by filter_upwards [hb i hi] with ω hω using (neg_le_abs _).trans hω) hε
  have hupper := h_indep.measureReal_sum_ge_le_of_ae_le hL2 hmean hup hε
  simp only [neg_sq, Finset.sum_neg_distrib] at hlow
  calc μ.real {ω | ε ≤ |∑ i ∈ s, X i ω|}
      ≤ μ.real ({ω | ε ≤ ∑ i ∈ s, X i ω} ∪ {ω | ε ≤ -∑ i ∈ s, X i ω}) := by
        refine measureReal_mono (fun ω hω ↦ ?_)
        simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
        rcases le_abs'.1 hω with h | h
        · exact Or.inr (by linarith)
        · exact Or.inl h
    _ ≤ _ := (measureReal_union_le _ _).trans (by linarith)

end ProbabilityTheory.iIndepFun
