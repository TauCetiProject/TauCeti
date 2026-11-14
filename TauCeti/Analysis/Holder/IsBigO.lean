/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.MetricSpace.Holder

/-!
# Hölder difference estimates near the diagonal

For `α ≤ 1`, these lemmas express local `α`-Hölder bounds as asymptotic estimates
`φ z - φ w = O(dist z w ^ α)` along `𝓝 z₀ ×ˢ 𝓝 z₀`, the form taken by the hypotheses of
Mathlib's `FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO`.

## Main results

* `TauCeti.isBigO_sub_dist_rpow`: the difference of two points.
* `ContDiffAt.isBigO_sub_dist_rpow`: the differences of a map that is `C^1` at `z₀`.
* `HolderOnWith.isBigO_comp_sub_dist_rpow`: the differences of a map that is `α`-Hölder near
  `τ z₀`, composed with a map `τ` that is `C^1` at `z₀`.
-/

public section

open Asymptotics Filter Set Topology
open scoped NNReal

variable {𝕜 : Type*} [RCLike 𝕜]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [SeminormedAddCommGroup G]

namespace TauCeti

/-- Near the diagonal, the difference of two points is `O(‖z - w‖ ^ α)` for `α ≤ 1`. -/
theorem isBigO_sub_dist_rpow {α : ℝ≥0} (hα : α ≤ 1) (z₀ : E) :
    (fun a : E × E ↦ a.1 - a.2) =O[𝓝 z₀ ×ˢ 𝓝 z₀] fun a ↦ dist a.1 a.2 ^ (α : ℝ) := by
  have hlim : Tendsto (fun a : E × E ↦ dist a.1 a.2) (𝓝 z₀ ×ˢ 𝓝 z₀) (𝓝 0) := by
    rw [← dist_self z₀, ← nhds_prod_eq]
    exact continuous_dist.tendsto (z₀, z₀)
  refine .of_bound 1 ?_
  filter_upwards [hlim.eventually (gt_mem_nhds zero_lt_one)] with a ha
  rw [one_mul, Real.norm_of_nonneg (by positivity), ← dist_eq_norm]
  calc dist a.1 a.2 = dist a.1 a.2 ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ dist a.1 a.2 ^ (α : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge' dist_nonneg ha.le α.coe_nonneg (by exact_mod_cast hα)

end TauCeti

/-- A map that is `C^1` at `z₀` has differences `O(‖z - w‖ ^ α)` near `(z₀, z₀)` for `α ≤ 1`. -/
theorem ContDiffAt.isBigO_sub_dist_rpow {φ : E → F} {z₀ : E} (hφ : ContDiffAt 𝕜 1 φ z₀)
    {α : ℝ≥0} (hα : α ≤ 1) :
    (fun a : E × E ↦ φ a.1 - φ a.2) =O[𝓝 z₀ ×ˢ 𝓝 z₀] fun a ↦ dist a.1 a.2 ^ (α : ℝ) := by
  rw [← nhds_prod_eq]
  refine (hφ.hasStrictFDerivAt_fderiv one_ne_zero).isBigO_sub.trans ?_
  rw [nhds_prod_eq]
  exact TauCeti.isBigO_sub_dist_rpow hα z₀

/-- A map `ψ` that is `α`-Hölder on a neighbourhood of `τ z₀`, composed with a map `τ` that is
`C^1` at `z₀`, has differences `O(‖z - w‖ ^ α)` near `(z₀, z₀)`. -/
theorem HolderOnWith.isBigO_comp_sub_dist_rpow {ψ : F → G} {C α : ℝ≥0} {K : Set F}
    (hH : HolderOnWith C α ψ K) {τ : E → F} {z₀ : E} (hK : K ∈ 𝓝 (τ z₀))
    (hτ : ContDiffAt 𝕜 1 τ z₀) :
    (fun a : E × E ↦ ψ (τ a.1) - ψ (τ a.2)) =O[𝓝 z₀ ×ˢ 𝓝 z₀]
      fun a ↦ dist a.1 a.2 ^ (α : ℝ) := by
  obtain ⟨c, hc, hcτ⟩ := (by
    rw [← nhds_prod_eq]
    exact (hτ.hasStrictFDerivAt_fderiv one_ne_zero).isBigO_sub :
      (fun a : E × E ↦ τ a.1 - τ a.2) =O[𝓝 z₀ ×ˢ 𝓝 z₀] fun a ↦ a.1 - a.2).exists_pos
  have hτK : ∀ᶠ z in 𝓝 z₀, τ z ∈ K := hτ.continuousAt.preimage_mem_nhds hK
  refine .of_bound (C * c ^ (α : ℝ)) ?_
  filter_upwards [hcτ.bound, prod_mem_prod hτK hτK] with a ha hK
  rw [Real.norm_of_nonneg (by positivity), ← dist_eq_norm, mul_assoc,
    ← Real.mul_rpow hc.le dist_nonneg]
  rw [← dist_eq_norm, ← dist_eq_norm] at ha
  refine (hH.dist_le hK.1 hK.2).trans ?_
  gcongr
