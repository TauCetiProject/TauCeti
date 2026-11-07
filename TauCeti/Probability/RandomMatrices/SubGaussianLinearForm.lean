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

namespace TauCeti

namespace Probability

/-- Two-sided sub-Gaussian tail bound for a linear combination of independent coordinates. -/
theorem measureReal_abs_sum_mul_ge_le_of_iIndepFun
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω}
    {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ) {c : ℝ≥0}
    (hX : ∀ i, HasSubgaussianMGF (X i) c μ) (a : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, a i * X i ω|} ≤
      2 * Real.exp
        (-t ^ 2 / (2 * (c * ∑ i, (⟨(a i) ^ 2, sq_nonneg (a i)⟩ : ℝ≥0)))) := by
  let Y : ι → Ω → ℝ := fun i ω ↦ a i * X i ω
  let a2 : ι → ℝ≥0 := fun i ↦ ⟨(a i) ^ 2, sq_nonneg (a i)⟩
  let S : Ω → ℝ := fun ω ↦ ∑ i, Y i ω
  have hY_indep : iIndepFun Y μ := by
    change iIndepFun (fun i ω ↦ a i * X i ω) μ
    exact h_indep.comp (fun i x ↦ a i * x) (by intro i; fun_prop)
  have hY : ∀ i, HasSubgaussianMGF (Y i) (a2 i * c) μ := by
    intro i
    exact (hX i).const_mul (a i)
  have hS : HasSubgaussianMGF S (c * ∑ i, a2 i) μ := by
    have hsum := HasSubgaussianMGF.sum_of_iIndepFun hY_indep
      (c := fun i ↦ a2 i * c) (s := Finset.univ) (by
        intro i hi
        exact hY i)
    have hc : ∑ i, a2 i * c = c * ∑ i, a2 i := by
      rw [← Finset.sum_mul, mul_comm]
    rw [← hc]
    exact hsum
  have hset : {ω | t ≤ |S ω|} =
      {ω | t ≤ S ω} ∪ {ω | t ≤ -S ω} := by
    ext ω
    change t ≤ |S ω| ↔ t ≤ S ω ∨ t ≤ -S ω
    exact le_abs
  have hset' : {ω | t ≤ |∑ i, a i * X i ω|} =
      {ω | t ≤ S ω} ∪ {ω | t ≤ -S ω} := hset
  calc
    μ.real {ω | t ≤ |∑ i, a i * X i ω|} =
        μ.real ({ω | t ≤ S ω} ∪ {ω | t ≤ -S ω}) := by
          rw [hset']
    _ ≤ μ.real {ω | t ≤ S ω} + μ.real {ω | t ≤ -S ω} :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-t ^ 2 / (2 * (c * ∑ i, a2 i))) +
        Real.exp (-t ^ 2 / (2 * (c * ∑ i, a2 i))) :=
      add_le_add (hS.measure_ge_le ht) (hS.neg.measure_ge_le ht)
    _ = 2 * Real.exp (-t ^ 2 / (2 * (c * ∑ i, a2 i))) := by ring

end Probability

end TauCeti
