/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Nontangential.Function
public import TauCeti.Analysis.Complex.UpperHalfPlane.Nontangential.Limit

/-!
# Checks for nontangential cones and maximal bounds on the half-plane

Worked examples for the nontangential cones `Γ^α_h(x)`, the cone comparison of Poisson kernels and
the nontangential maximal function of Poisson integrals, in the namespace
`TauCeti.Examples.Nontangential`:

* the constant `3` of the cone comparison: `0.99 + i` lies in `Γ_∞(0)` but its boundary point
  `1 + i` does not (`mem_nontangentialCone_ninetyNine`, `one_add_I_notMem_nontangentialCone`);
  `P(0.99 + i, 1) = 1 / (1.0001 π)` and `P(i, 1) = 1 / (2 π)`
  (`upperHalfPlanePoissonKernel_ninetyNine_one`, `upperHalfPlanePoissonKernel_I_one`), and the
  comparison `P(0.99 + i, 1) ≤ 3 P(i, 1)` holds (`upperHalfPlanePoissonKernel_ninetyNine_one_le`);
* `h = 0`: the nontangential maximal function of `P[h]` vanishes
  (`nontangentialMaximalFunction_upperHalfPlanePoissonIntegralFun_zero`);
* `h ≡ 1`, in `L¹(Π)` but not in `L¹`: `P[h] ≡ 1` on the upper half-plane and `M_1 P[h] ≡ 1`
  (`TauCeti.upperHalfPlanePoissonIntegralFun_const`,
  `nontangentialMaximalFunction_upperHalfPlanePoissonIntegralFun_one`);
* the vertical approach `x + it`, `t → 0⁺`, is nontangential, and the nontangential filter for a
  positive aperture is nontrivial (`nontangentialFilter_one_neBot`).
-/

public section

noncomputable section

namespace TauCeti.Examples.Nontangential

open Complex Filter MeasureTheory

open scoped Real ENNReal

/-- `0.99 + i` lies in the cone `Γ_∞(0)` of aperture one. -/
theorem mem_nontangentialCone_ninetyNine :
    ((0.99 : ℝ) : ℂ) + I ∈ nontangentialCone 1 ⊤ 0 := by
  rw [mem_nontangentialCone]
  norm_num

/-- `1 + i` lies on the boundary of the cone `Γ_∞(0)`, not in it. -/
theorem one_add_I_notMem_nontangentialCone : (1 : ℂ) + I ∉ nontangentialCone 1 ⊤ 0 := by
  rw [mem_nontangentialCone]
  norm_num

/-- `P(0.99 + i, 1) = 1 / (1.0001 π)`. -/
theorem upperHalfPlanePoissonKernel_ninetyNine_one :
    upperHalfPlanePoissonKernel (((0.99 : ℝ) : ℂ) + I) 1 = 1 / (1.0001 * π) := by
  rw [upperHalfPlanePoissonKernel_eq, normSq_apply]
  norm_num
  ring

/-- `P(i, 1) = 1 / (2 π)`. -/
theorem upperHalfPlanePoissonKernel_I_one : upperHalfPlanePoissonKernel I 1 = 1 / (2 * π) := by
  rw [upperHalfPlanePoissonKernel_eq, normSq_apply]
  norm_num
  ring

/-- The cone comparison at `z = 0.99 + i`, `s = 1`: `P(0.99 + i, 1) ≤ 3 P(i, 1)`. -/
theorem upperHalfPlanePoissonKernel_ninetyNine_one_le :
    upperHalfPlanePoissonKernel (((0.99 : ℝ) : ℂ) + I) 1 ≤ 3 * upperHalfPlanePoissonKernel I 1 := by
  simpa using upperHalfPlanePoissonKernel_le_three_mul_of_mem_nontangentialCone
    mem_nontangentialCone_ninetyNine 1

/-- For `h = 0` the nontangential maximal function of `P[h]` vanishes. -/
theorem nontangentialMaximalFunction_upperHalfPlanePoissonIntegralFun_zero (α : ℝ) (k : ℝ≥0∞)
    (x : ℝ) : nontangentialMaximalFunction α k (upperHalfPlanePoissonIntegralFun 0) x = 0 := by
  refine le_antisymm ?_ zero_le
  simpa [maximalFunction_zero] using
    nontangentialMaximalFunction_upperHalfPlanePoissonIntegralFun_le α k 0 x

/-- For `h ≡ 1`, `M_1 P[h] ≡ 1`. -/
theorem nontangentialMaximalFunction_upperHalfPlanePoissonIntegralFun_one (x : ℝ) :
    nontangentialMaximalFunction 1 1 (upperHalfPlanePoissonIntegralFun fun _ => 1) x = 1 := by
  refine le_antisymm (nontangentialMaximalFunction_le_iff.2 fun z hz => ?_) ?_
  · rw [upperHalfPlanePoissonIntegralFun_const 1 (mem_nontangentialCone.1 hz).1, eNorm_one]
  · have hz : (x : ℂ) + ((1 / 2 : ℝ) : ℂ) * I ∈ nontangentialCone 1 1 x := by
      rw [mem_nontangentialCone]
      norm_num
    calc (1 : ℝ≥0∞) = ‖upperHalfPlanePoissonIntegralFun (fun _ => 1)
          ((x : ℂ) + ((1 / 2 : ℝ) : ℂ) * I)‖ₑ := by
          rw [upperHalfPlanePoissonIntegralFun_const 1 (mem_nontangentialCone.1 hz).1, eNorm_one]
      _ ≤ _ := le_nontangentialMaximalFunction hz

/-- The nontangential filter of aperture one at `x` is nontrivial. -/
theorem nontangentialFilter_one_neBot (x : ℝ) : (nontangentialFilter 1 x).NeBot :=
  nontangentialFilter_neBot one_pos x

end TauCeti.Examples.Nontangential
