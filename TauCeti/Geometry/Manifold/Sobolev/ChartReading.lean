/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
public import TauCeti.Geometry.Manifold.DifferentialOperator.ChartCompression.Schwartz
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Sobolev.BesselPotential.LocalizedChangeOfVariables
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Changing the chart of a Sobolev reading of a function on a manifold

Let `M` be a manifold modelled on `ℝⁿ`. A complex-valued smooth function `u` on `M` is read in a
chart `e` of the maximal atlas through a cutoff `τ` as the Schwartz function `τ · (u ∘ e⁻¹)` on
`ℝⁿ` (`OpenPartialHomeomorph.cutoffPushforwardSchwartz`). This file shows that the `H^s` norm of
such a reading is controlled by the reading in any other chart: if `Ψ` is a cutoff `ψ` in a chart
`e'` read on `M`, then for every real `s`

`‖τ · ((Ψ g) ∘ e⁻¹)‖_{H^s} ≤ C ‖ψ · (g ∘ e'⁻¹)‖_{H^s}`

(`TauCeti.exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_mulLeft_le`). The
reading in `e` is `θ · (w ∘ κ)` for the reading `w` in `e'`, the transition map `κ = e' ∘ e⁻¹` and
a cutoff `θ` with compact support in the source of `κ` (`OpenPartialHomeomorph.overlapCutoff`),
and such localized changes of variables are bounded on `H^s`
(`BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp`).

## Main results

* `TauCeti.exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_mulLeft_le`: changing
  the chart of a reading costs a constant in the `H^s` norm.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §3
  (Sobolev spaces on compact manifolds, defined through a partition of unity and charts).
-/

public section

noncomputable section

open Set TauCeti OpenPartialHomeomorph
open scoped ContDiff Manifold Distributions SchwartzMap

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] {e e' : OpenPartialHomeomorph M (CoordinateSpace n)}

/-- **Changing the chart of a reading.** Let `ψ` be a cutoff in a chart `e'`, with `Ψ` the smooth
function `ψ ∘ e'` on `M`, extended by `0`, and `τ` a cutoff in a chart `e`. For every real `s`
there is a constant `C` such that for every smooth `g` on `M`, the reading `τ · ((Ψ g) ∘ e⁻¹)` of
`Ψ g` in `e` satisfies

`‖τ · ((Ψ g) ∘ e⁻¹)‖_{H^s} ≤ C ‖ψ · (g ∘ e'⁻¹)‖_{H^s}`. -/
theorem exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_mulLeft_le
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (τ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (ψ : 𝓓(⟨e'.target, e'.open_target⟩, ℝ)) (s : ℝ) :
    ∃ C, ∀ g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 (e.cutoffPushforwardSchwartz he τ
          (LinearMap.mulLeft ℂ (ContMDiffMap.ofReal (e'.cutoffPullback he' ψ 1)) g))‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 (e'.cutoffPushforwardSchwartz he' ψ g)‖ := by
  -- The reading in `e` is `θ · (w ∘ κ)` for the reading `w` in `e'`, the transition map
  -- `κ = e' ∘ e⁻¹` and `θ = τ · (ψ₁ ∘ κ)`, with `ψ₁ = 1` on the support of `ψ`.
  obtain ⟨ψ₁, hψ₁, -⟩ := TestFunction.exists_eventually_eq_one
    (Ω := ⟨e'.target, e'.open_target⟩) (n := ⊤) ψ.hasCompactSupport.isCompact ψ.tsupport_subset
  obtain ⟨hθ, hθc, hθs⟩ := overlapCutoff_spec he' he τ ψ₁
  obtain ⟨C, hC⟩ := BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp
    (F := ℂ) (contDiffOn_symm_trans_of_mem_maximalAtlas he he')
    (fun _ hz ↦ (contDiffAt_symm_trans_symm_of_mem_maximalAtlas he he' hz).contDiffWithinAt)
    hθ hθc hθs s
  refine ⟨C, fun g ↦ hC _ _ fun y ↦ ?_⟩
  rw [cutoffPushforwardSchwartz_apply, cutoffPushforwardSchwartz_apply, coe_trans,
    Function.comp_apply]
  by_cases hy : e.symm y ∈ e'.source
  · rw [overlapCutoff_apply_of_mem he' he τ ψ₁ hy, e'.left_inv hy]
    simp only [LinearMap.mulLeft_apply, ContMDiffMap.coe_mul, Pi.mul_apply,
      ContMDiffMap.ofReal_apply, cutoffPullback_one_apply_of_mem he' _ hy]
    by_cases hψ : ψ (e' (e.symm y)) = 0
    · simp [hψ]
    · rw [hψ₁.self_of_nhdsSet _ (subset_tsupport _ hψ), mul_one, ← Complex.real_smul]
  · rw [overlapCutoff_apply he' he, cutoffPullback_apply_of_notMem he' _ _ hy]
    simp [cutoffPullback_apply_of_notMem he' _ _ hy]

end TauCeti
