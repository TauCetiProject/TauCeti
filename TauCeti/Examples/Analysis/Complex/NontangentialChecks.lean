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
* `h = 1_{[0, 1]}` at `x = 2`: `P[h](2 + i) = (arctan 2 - π / 4) / π`, which lies in `(0, 1 / 4)`,
  while the maximal function of `h` at `2` is `1 / 4`, attained at radius `2`, so the cone
  comparison `P[h](2 + i) ≤ 3 M h(2)` holds
  (`upperHalfPlanePoissonIntegral_volume_restrict_Icc_zero_one_two_add_I`,
  `maximalFunction_indicator_Icc_zero_one_two`,
  `ofReal_upperHalfPlanePoissonIntegral_volume_restrict_Icc_zero_one_two_add_I_le`);
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

/-! ### The cone comparison for `h = 1_{[0, 1]}` at `x = 2` -/

/-- **`P[1_{[0, 1]}](2 + i) = (arctan 2 - π / 4) / π`**, about `0.102`. -/
theorem upperHalfPlanePoissonIntegral_volume_restrict_Icc_zero_one_two_add_I :
    upperHalfPlanePoissonIntegral (volume.restrict (Set.Icc 0 1)) (2 + I) =
      (Real.arctan 2 - π / 4) / π := by
  rw [upperHalfPlanePoissonIntegral_volume_restrict_Icc zero_le_one]
  norm_num [Real.arctan_neg, Real.arctan_one]
  ring

/-- `P[1_{[0, 1]}](2 + i)` lies strictly between `0` and `1 / 4`, since
`π / 4 = arctan 1 < arctan 2 < π / 2`. -/
theorem upperHalfPlanePoissonIntegral_volume_restrict_Icc_zero_one_two_add_I_mem_Ioo :
    upperHalfPlanePoissonIntegral (volume.restrict (Set.Icc 0 1)) (2 + I) ∈ Set.Ioo 0 (1 / 4) := by
  rw [upperHalfPlanePoissonIntegral_volume_restrict_Icc_zero_one_two_add_I]
  have h1 : π / 4 < Real.arctan 2 := by
    rw [← Real.arctan_one]; exact Real.arctan_strictMono (by norm_num)
  have h2 := Real.arctan_lt_pi_div_two 2
  constructor
  · exact div_pos (by linarith) Real.pi_pos
  · rw [div_lt_iff₀ Real.pi_pos]; linarith

/-- **The maximal function of `1_{[0, 1]}` at `2` is `1 / 4`**, attained at radius `2`: the ball
`B(2, r)` meets `[0, 1]` in a set of length at most `r / 2`, with equality for `r = 2`. -/
theorem maximalFunction_indicator_Icc_zero_one_two :
    maximalFunction volume ((Set.Icc (0 : ℝ) 1).indicator (1 : ℝ → ℝ)) 2 = 1 / 4 := by
  have havg (r : ℝ) : ⨍⁻ y in Metric.ball (2 : ℝ) r,
      ‖(Set.Icc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) y‖ₑ =
        volume (Set.Icc (0 : ℝ) 1 ∩ Metric.ball 2 r) / ENNReal.ofReal (2 * r) := by
    rw [setLAverage_eq, Real.volume_ball]
    congr 1
    simp_rw [eNorm_indicator_eq_indicator_eNorm, Pi.one_apply, eNorm_one]
    rw [lintegral_indicator_const measurableSet_Icc, one_mul,
      Measure.restrict_apply measurableSet_Icc]
  refine le_antisymm (maximalFunction_le fun r hr => ?_) ?_
  · rw [havg, ENNReal.div_le_iff (by simp [hr]) ENNReal.ofReal_ne_top]
    calc volume (Set.Icc (0 : ℝ) 1 ∩ Metric.ball 2 r)
        ≤ volume (Set.Icc (max 0 (2 - r)) 1) := measure_mono fun y ⟨⟨hy0, hy1⟩, hyb⟩ => by
          rw [Real.ball_eq_Ioo] at hyb
          exact ⟨max_le hy0 hyb.1.le, hy1⟩
      _ ≤ ENNReal.ofReal (r / 2) := by
          rw [Real.volume_Icc]
          refine ENNReal.ofReal_le_ofReal ?_
          rcases le_total r 2 with h | h
          · rw [max_eq_right (by linarith)]; linarith
          · rw [max_eq_left (by linarith)]; linarith
      _ = 1 / 4 * ENNReal.ofReal (2 * r) := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_div_of_pos
            (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
          ring_nf
  · refine le_trans ?_ (setLAverage_le_maximalFunction volume _ 2 two_pos)
    rw [havg, ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl ENNReal.ofReal_ne_top)]
    calc 1 / 4 * ENNReal.ofReal (2 * 2) = volume (Set.Ioo (0 : ℝ) 1) := by
          rw [Real.volume_Ioo, ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_one,
            ← ENNReal.ofReal_div_of_pos (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
          norm_num
      _ ≤ volume (Set.Icc (0 : ℝ) 1 ∩ Metric.ball 2 2) :=
          measure_mono fun y ⟨hy0, hy1⟩ => ⟨⟨hy0.le, hy1.le⟩, by
          rw [Real.ball_eq_Ioo]; constructor <;> linarith⟩

/-- **The cone comparison at `x = 2`**: `P[1_{[0, 1]}](2 + i) ≈ 0.102` is at most `3` times the
maximal function `1 / 4` of `1_{[0, 1]}` at `2`. -/
theorem ofReal_upperHalfPlanePoissonIntegral_volume_restrict_Icc_zero_one_two_add_I_le :
    ENNReal.ofReal (upperHalfPlanePoissonIntegral (volume.restrict (Set.Icc 0 1)) (2 + I)) ≤
      3 * maximalFunction volume ((Set.Icc (0 : ℝ) 1).indicator (1 : ℝ → ℝ)) 2 := by
  rw [maximalFunction_indicator_Icc_zero_one_two]
  refine (ENNReal.ofReal_le_ofReal
    upperHalfPlanePoissonIntegral_volume_restrict_Icc_zero_one_two_add_I_mem_Ioo.2.le).trans ?_
  rw [← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_one, ← ENNReal.ofReal_ofNat 4,
    ← ENNReal.ofReal_div_of_pos (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

end TauCeti.Examples.Nontangential
