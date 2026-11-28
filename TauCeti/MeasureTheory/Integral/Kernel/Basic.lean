/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Transposition for continuous operator-valued integral kernels

For a jointly continuous operator-valued kernel `K : X → Y → V →L[𝕜] W` with `W` complete,
continuous `u : Y → V`, and continuous `v : X → W →L[𝕜] M`, Fubini's theorem swaps the nested
Bochner integrals
`∫ x, v x (∫ y, K x y (u y) ∂ν) ∂μ = ∫ y, (∫ x, (v x).comp (K x y) ∂μ) (u y) ∂ν`
whenever the paired integrand has compact support on `X × Y` and each active slice `y ↦ K x y (u y)`
(for `v x ≠ 0`) and `x ↦ (v x).comp (K x y)` (for `u y ≠ 0`) has compact support, for measures
finite on compact subsets (`TauCeti.integral_apply_integral_swap_of_hasCompactSupport`).
-/

public section

open Function MeasureTheory

namespace TauCeti

/-- **Transposition identity for continuous operator-valued kernels with compactly supported
pairings.** If `K : X → Y → V →L[𝕜] W` (`W` complete), `u : Y → V`, and `v : X → W →L[𝕜] M` are
continuous, `(x, y) ↦ v x (K x y (u y))` has compact support, each slice `y ↦ K x y (u y)` has
compact support whenever `v x ≠ 0`, and each transposed slice `x ↦ (v x).comp (K x y)` has compact
support whenever `u y ≠ 0`, then integrating against measures finite on compact subsets satisfies
`∫ x, v x (∫ y, K x y (u y) ∂ν) ∂μ = ∫ y, (∫ x, (v x).comp (K x y) ∂μ) (u y) ∂ν`. -/
theorem integral_apply_integral_swap_of_hasCompactSupport {X Y 𝕜 V W M : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace 𝕜 W] [IsScalarTower ℝ 𝕜 W] [CompleteSpace W]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedSpace 𝕜 M] [IsScalarTower ℝ 𝕜 M]
    {K : X → Y → V →L[𝕜] W} (hKc : Continuous (uncurry K)) {u : Y → V} (hu : Continuous u)
    {v : X → W →L[𝕜] M} (hv : Continuous v)
    (hprod : HasCompactSupport fun p : X × Y ↦ v p.1 (K p.1 p.2 (u p.2)))
    (hLHS_cs : ∀ x, v x = 0 ∨ HasCompactSupport fun y ↦ K x y (u y))
    (hRHS_cs : ∀ y, u y = 0 ∨ HasCompactSupport fun x ↦ (v x).comp (K x y))
    (μ : Measure X := by volume_tac) (ν : Measure Y := by volume_tac)
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] :
    (∫ x, v x (∫ y, K x y (u y) ∂ν) ∂μ) = ∫ y, (∫ x, (v x).comp (K x y) ∂μ) (u y) ∂ν := by
  by_cases hM : CompleteSpace M; swap
  · simp [integral_of_not_completeSpace hM]
  have hcont_comp : Continuous fun p : X × Y ↦ (v p.1).comp (K p.1 p.2) :=
    ((ContinuousLinearMap.compL 𝕜 V W M).continuous.comp (hv.comp continuous_fst)).clm_apply hKc
  have hcont_prod : Continuous fun p : X × Y ↦ v p.1 (K p.1 p.2 (u p.2)) :=
    hcont_comp.clm_apply (hu.comp continuous_snd)
  have hLHS : (∫ x, v x (∫ y, K x y (u y) ∂ν) ∂μ) = ∫ x, ∫ y, v x (K x y (u y)) ∂ν ∂μ := by
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    refine (hLHS_cs x).elim (fun hv0 ↦ by simp [hv0]) fun hcs ↦ ?_
    have hint : Integrable (fun y ↦ K x y (u y)) ν :=
      ((hKc.comp (continuous_const.prodMk continuous_id)).clm_apply
        hu).integrable_of_hasCompactSupport hcs
    exact (((v x).restrictScalars ℝ).integral_comp_comm hint).symm
  have hRHS : (∫ y, ∫ x, v x (K x y (u y)) ∂μ ∂ν) =
      ∫ y, (∫ x, (v x).comp (K x y) ∂μ) (u y) ∂ν := by
    refine integral_congr_ae (.of_forall fun y ↦ ?_)
    refine (hRHS_cs y).elim (fun hu0 ↦ by simp [hu0]) fun hcs ↦ ?_
    have hint : Integrable (fun x ↦ (v x).comp (K x y)) μ :=
      (hcont_comp.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport hcs
    exact ((ContinuousLinearMap.apply 𝕜 M (u y)).restrictScalars ℝ).integral_comp_comm hint
  exact hLHS.trans ((MeasureTheory.integral_integral_swap_of_hasCompactSupport
    (f := fun x y ↦ v x (K x y (u y)))
    (by simpa [Function.uncurry_def] using hcont_prod)
    (by simpa [Function.uncurry_def] using hprod)).trans hRHS)

end TauCeti
