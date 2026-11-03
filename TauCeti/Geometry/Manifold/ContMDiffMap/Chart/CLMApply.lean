/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.CLMApply
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Seminorm
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Data.Nat.Choose.Sum

/-!
# Compact chart bounds for smooth linear multipliers

A smooth family `A x : F →L[𝕜] G` acts linearly on smooth vector-valued maps by
`f x ↦ A x (f x)`. On a compact coordinate set, its chart `C^k` seminorm is at most
`2^k` times the product of the chart `C^k` seminorms of `A` and `f`.
In particular, mutually inverse smooth families give equivalent fixed-compact
seminorms and preserve exact supports. Applied on an overlap of bundle frames,
these estimates control the change of section coefficients without choosing a
connection or a fibrewise isometric frame.

The bounds use derivatives within the extended chart target, so they also apply
to manifolds with corners. The multiplier need not be bounded globally, the
compact set may be empty, and the model fibres need not be finite dimensional.

The proof uses Mathlib's `norm_iteratedFDerivWithin_clm_apply` (the Leibniz
estimate), and the compact chart seminorms from `Chart.Seminorm`.
-/

public section

open Set TopologicalSpace
open scoped Manifold

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {n : WithTop ℕ∞}

variable [IsManifold I n M]

/-- The compact chart Leibniz estimate for a smooth linear multiplier. -/
theorem chartCkSeminorm_clmApplyLinearMap_le
    (A : C^n⟮I, M; 𝓘(𝕜, F →L[𝕜] G), F →L[𝕜] G⟯)
    (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) (x : M)
    (K : Compacts (extChartAt I x).target) (k : ℕ) (hk : k ≤ n) :
    chartCkSeminorm x K k hk (clmApplyLinearMap A f) ≤
      2 ^ k * chartCkSeminorm x K k hk A * chartCkSeminorm x K k hk f := by
  let pA := chartCkSeminorm x K k hk A
  let pf := chartCkSeminorm x K k hk f
  have hA := (chartCkSeminorm_le_iff x K k hk A (apply_nonneg _ _)).mp le_rfl
  have hf := (chartCkSeminorm_le_iff x K k hk f (apply_nonneg _ _)).mp le_rfl
  have hAc : ContDiffOn 𝕜 n (A ∘ (extChartAt I x).symm) (extChartAt I x).target :=
    (A.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt_symm x)).contDiffOn
  have hfc : ContDiffOn 𝕜 n (f ∘ (extChartAt I x).symm) (extChartAt I x).target :=
    (f.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt_symm x)).contDiffOn
  refine (chartCkSeminorm_le_iff x K k hk _ (by positivity)).mpr fun m hm z hz ↦ ?_
  rw [chartIteratedFDeriv_self_target_apply]
  have h := norm_iteratedFDerivWithin_clm_apply hAc hfc
    (uniqueDiffOn_extChartAt_target x) z.property ((Nat.cast_le.mpr hm).trans hk)
  have hfun : (clmApplyLinearMap A f) ∘ (extChartAt I x).symm =
      fun y ↦ (A ∘ (extChartAt I x).symm) y ((f ∘ (extChartAt I x).symm) y) := by
    ext y
    simp only [Function.comp_apply, clmApplyLinearMap_apply]
  rw [hfun]
  refine h.trans (le_trans (b := ∑ i ∈ Finset.range (m + 1),
    (m.choose i : ℝ) * (pA * pf)) (Finset.sum_le_sum fun i hi ↦ ?_) ?_)
  · have hi : i ≤ m := Finset.mem_range_succ_iff.mp hi
    have hAi := hA i (hi.trans hm) z hz
    have hfi := hf (m - i) ((Nat.sub_le m i).trans hm) z hz
    rw [chartIteratedFDeriv_self_target_apply] at hAi hfi
    calc _ = (m.choose i : ℝ) *
          (‖iteratedFDerivWithin 𝕜 i (A ∘ (extChartAt I x).symm)
              (extChartAt I x).target z‖ *
            ‖iteratedFDerivWithin 𝕜 (m - i) (f ∘ (extChartAt I x).symm)
              (extChartAt I x).target z‖) := mul_assoc _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul hAi hfi (norm_nonneg _) (apply_nonneg _ _)) (Nat.cast_nonneg _)
  · calc ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * (pA * pf)
        = (2 : ℝ) ^ m * (pA * pf) := by
          rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
          simp
      _ ≤ 2 ^ k * pA * pf := by
          rw [mul_assoc]
          gcongr
          norm_num

/-- A smooth left inverse gives the reverse compact-chart seminorm bound.
On a frame overlap, use this with the inverse transition family. -/
theorem chartCkSeminorm_le_clmApplyLinearMap
    (A : C^n⟮I, M; 𝓘(𝕜, F →L[𝕜] G), F →L[𝕜] G⟯)
    (B : C^n⟮I, M; 𝓘(𝕜, G →L[𝕜] F), G →L[𝕜] F⟯)
    (hBA : ∀ y v, B y (A y v) = v) (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) (x : M)
    (K : Compacts (extChartAt I x).target) (k : ℕ) (hk : k ≤ n) :
    chartCkSeminorm x K k hk f ≤
      2 ^ k * chartCkSeminorm x K k hk B *
        chartCkSeminorm x K k hk (clmApplyLinearMap A f) := by
  have heq : clmApplyLinearMap B (clmApplyLinearMap A f) = f := by
    ext y
    simp [hBA]
  simpa only [heq] using
    chartCkSeminorm_clmApplyLinearMap_le B (clmApplyLinearMap A f) x K k hk

end ContMDiffMap
