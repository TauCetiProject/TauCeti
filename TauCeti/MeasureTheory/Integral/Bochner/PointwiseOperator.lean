/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Pointwise integrals of families of bounded operators

Let `F y : X →L[𝕜] Z` be a family of bounded operators between Banach spaces such that
`y ↦ F y x` is integrable for every `x`. The map `x ↦ ∫ F y x dμ(y)` is then a bounded operator
(`ContinuousLinearMap.exists_apply_eq_integral`). No bound on `‖F y‖` and no measurability of `F`
in the operator norm is assumed: the map `x ↦ (y ↦ F y x)` into `L¹(μ, Z)` has a closed graph, so
it is bounded by the closed graph theorem. This is the strong (pointwise) integral of `F`, as
opposed to its Bochner integral in the operator norm, which need not exist (for instance for a
family of translation operators).

## Provenance

Adapted from `New.exists_continuousLinearMap_apply_eq_integral` in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/General/Analysis/HolomorphicIntegrals.lean`, where it is stated over `ℂ`.
-/

public section

open MeasureTheory Filter Topology

namespace ContinuousLinearMap

variable {Y X Z 𝕜 : Type*} [MeasurableSpace Y] {μ : Measure Y} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedSpace 𝕜 Z] [SMulCommClass ℝ 𝕜 Z]
  [CompleteSpace Z]

/-- If `F y : X →L[𝕜] Z` is a family of bounded operators between Banach spaces such that
`y ↦ F y x` is integrable for every `x`, then `x ↦ ∫ F y x dμ(y)` is a bounded operator. -/
theorem exists_apply_eq_integral {F : Y → X →L[𝕜] Z}
    (h_int : ∀ x : X, Integrable (fun y : Y ↦ F y x) μ) :
    ∃ A : X →L[𝕜] Z, ∀ x : X, A x = ∫ y : Y, F y x ∂μ := by
  -- The linear map `x ↦ (y ↦ F y x)` into `L¹(μ, Z)` has a closed graph.
  let T : X →ₗ[𝕜] Lp Z 1 μ :=
    { toFun x := (h_int x).toL1
      map_add' x x' := by
        simpa only [map_add, Pi.add_def] using Integrable.toL1_add _ _ (h_int x) (h_int x')
      map_smul' c x := by
        simpa only [map_smul, RingHom.id_apply] using Integrable.toL1_smul _ (h_int x) c }
  have h_closed (u : ℕ → X) (x : X) (g : Lp Z 1 μ) (hu : Tendsto u atTop (𝓝 x))
      (hg : Tendsto (T ∘ u) atTop (𝓝 g)) : g = T x := by
    -- Along a subsequence, `F y (u n)` tends to `g y` for almost every `y`, and to `F y x` for
    -- every `y`.
    have h_measure : TendstoInMeasure μ (fun (n : ℕ) (y : Y) ↦ F y (u n)) atTop g :=
      (tendstoInMeasure_of_tendsto_Lp hg).congr_left fun n ↦ (h_int (u n)).coeFn_toL1
    obtain ⟨φ, hφ, h_ae⟩ := h_measure.exists_seq_tendsto_ae'
    have h_limit : (fun y : Y ↦ F y x) =ᵐ[μ] g :=
      h_ae.mono fun y hy ↦ tendsto_nhds_unique ((F y).continuous.seqContinuous (hu.comp hφ)) hy
    exact Lp.ext ((h_int x).coeFn_toL1.trans h_limit).symm
  have hT (x : X) : T x = (h_int x).toL1 := rfl
  refine ⟨L1.integralCLM' 𝕜 ∘L .ofSeqClosedGraph h_closed, fun x ↦ ?_⟩
  rw [comp_apply, coeFn_ofSeqClosedGraph, hT, integral_eq _ (h_int x), L1.integral_eq' 𝕜]

end ContinuousLinearMap
