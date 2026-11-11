/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Sub-Gaussian linear forms

For independent sub-Gaussian coordinates, a fixed linear form has a sub-Gaussian tail with
variance proxy equal to the sum of the coordinate proxies weighted by the squared coefficients.
Applying this to coefficients of the form `u i * v j` gives the fixed-bilinear-form estimate
used in the operator-norm tail bound for random matrices.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ProbabilityTheory.iIndepFun

/-- Two-sided sub-Gaussian tail bound for a linear combination of independent coordinates. -/
theorem measureReal_abs_sum_mul_ge_le_of_iIndepFun
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω}
    {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ) {c : ι → ℝ≥0}
    (hX : ∀ i, HasSubgaussianMGF (X i) (c i) μ) (a : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, a i * X i ω|} ≤
      2 * Real.exp
        (-t ^ 2 / (2 * ∑ i, (a i) ^ 2 * (c i : ℝ))) := by
  let Y : ι → Ω → ℝ := fun i ω ↦ a i * X i ω
  let a2 : ι → ℝ≥0 := fun i ↦ ⟨(a i) ^ 2, sq_nonneg (a i)⟩
  let S : Ω → ℝ := fun ω ↦ ∑ i, Y i ω
  have hY_indep : iIndepFun Y μ :=
    h_indep.comp (fun i x ↦ a i * x) (by intro i; fun_prop)
  have hY : ∀ i, HasSubgaussianMGF (Y i) (a2 i * c i) μ := by
    intro i
    exact (hX i).const_mul (a i)
  have hS : HasSubgaussianMGF S (∑ i, a2 i * c i) μ := by
    exact HasSubgaussianMGF.sum_of_iIndepFun hY_indep
      (c := fun i ↦ a2 i * c i) (s := Finset.univ) (by
        intro i hi
        exact hY i)
  have hset : {ω | t ≤ |S ω|} =
      {ω | t ≤ S ω} ∪ {ω | t ≤ -S ω} := by
    ext ω
    simpa only [Set.mem_ofPred_eq, Set.mem_union] using (le_abs : t ≤ |S ω| ↔ _)
  have hset' : {ω | t ≤ |∑ i, a i * X i ω|} =
      {ω | t ≤ S ω} ∪ {ω | t ≤ -S ω} := hset
  have hbound : μ.real {ω | t ≤ |∑ i, a i * X i ω|} ≤
      2 * Real.exp (-t ^ 2 / (2 * ∑ i, a2 i * c i)) := by
    calc
      μ.real {ω | t ≤ |∑ i, a i * X i ω|} =
          μ.real ({ω | t ≤ S ω} ∪ {ω | t ≤ -S ω}) := by
            rw [hset']
      _ ≤ μ.real {ω | t ≤ S ω} + μ.real {ω | t ≤ -S ω} :=
        measureReal_union_le _ _
      _ ≤ Real.exp (-t ^ 2 / (2 * ∑ i, a2 i * c i)) +
          Real.exp (-t ^ 2 / (2 * ∑ i, a2 i * c i)) :=
        add_le_add (hS.measure_ge_le ht) (hS.neg.measure_ge_le ht)
      _ = 2 * Real.exp (-t ^ 2 / (2 * ∑ i, a2 i * c i)) := by ring
  have hproxy : ((∑ i, a2 i * c i : ℝ≥0) : ℝ) =
      ∑ i, (a i) ^ 2 * (c i : ℝ) := by
    rw [NNReal.coe_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [NNReal.coe_mul]
    rfl
  simpa only [hproxy] using hbound

/-- The linear-form tail bound when all coordinates have the same variance proxy. -/
theorem measureReal_abs_sum_mul_ge_le_of_iIndepFun_const
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω}
    {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ) {c : ℝ≥0}
    (hX : ∀ i, HasSubgaussianMGF (X i) c μ) (a : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, a i * X i ω|} ≤
      2 * Real.exp (-t ^ 2 / (2 * ((c : ℝ) * ∑ i, (a i) ^ 2))) := by
  simpa only [Finset.mul_sum, mul_comm] using
    h_indep.measureReal_abs_sum_mul_ge_le_of_iIndepFun hX a ht

end ProbabilityTheory.iIndepFun
