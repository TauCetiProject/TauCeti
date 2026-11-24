/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Topology.MetricSpace.Holder

/-!
# Hölder difference estimates near the diagonal

For `α ≤ 1`, these lemmas express local `α`-Hölder bounds as asymptotic estimates
`φ z - φ w = O(dist z w ^ α)` along `𝓝 z₀ ×ˢ 𝓝 z₀`, the form taken by the hypotheses of
Mathlib's `FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO`, and convert such an
estimate back into a Hölder bound on a ball.

## Main results

* `TauCeti.isBigO_sub_dist_rpow`: the difference of two points.
* `HasStrictFDerivAt.isBigO_sub_dist_rpow`, `ContDiffAt.isBigO_sub_dist_rpow`: the differences of
  a map that is strictly differentiable, or `C^n` with `n ≠ 0`, at `z₀`.
* `HolderOnWith.isBigO_comp_sub_dist_rpow_of_lipschitzOnWith`: the differences of a map that is
  `α`-Hölder on a set `K`, composed with a map `τ` that is Lipschitz near `z₀` and maps a
  neighbourhood of `z₀` into `K`.
* `HolderOnWith.isBigO_comp_sub_dist_rpow`: the same for `τ` that is `C^1` at `z₀`.
* `Asymptotics.IsBigO.exists_holderOnWith_ball`: conversely, such an estimate gives a Hölder bound
  on a ball around `z₀`.
-/

public section

open Asymptotics Filter Set Topology
open scoped NNReal

namespace TauCeti

/-- Near the diagonal, the difference of two points is `O(‖z - w‖ ^ α)` for `α ≤ 1`. -/
theorem isBigO_sub_dist_rpow {E : Type*} [SeminormedAddCommGroup E] {α : ℝ≥0} (hα : α ≤ 1)
    (z₀ : E) :
    (fun a : E × E ↦ a.1 - a.2) =O[𝓝 z₀ ×ˢ 𝓝 z₀] fun a ↦ dist a.1 a.2 ^ (α : ℝ) := by
  have hlim : Tendsto (fun a : E × E ↦ dist a.1 a.2) (𝓝 z₀ ×ˢ 𝓝 z₀) (𝓝[≥] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, .of_forall fun _ ↦ dist_nonneg⟩
    rw [← dist_self z₀, ← nhds_prod_eq]
    exact continuous_dist.tendsto (z₀, z₀)
  rw [← isBigO_norm_left]
  simp_rw [← dist_eq_norm]
  exact (IsBigO.id_rpow_of_le_one (by exact_mod_cast hα)).comp_tendsto hlim

end TauCeti

/-- A map that is strictly differentiable at `z₀` has differences `O(‖z - w‖ ^ α)` near
`(z₀, z₀)` for `α ≤ 1`. -/
theorem HasStrictFDerivAt.isBigO_sub_dist_rpow {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {φ : E → F} {φ' : E →L[𝕜] F} {z₀ : E} (hφ : HasStrictFDerivAt φ φ' z₀)
    {α : ℝ≥0} (hα : α ≤ 1) :
    (fun a : E × E ↦ φ a.1 - φ a.2) =O[𝓝 z₀ ×ˢ 𝓝 z₀] fun a ↦ dist a.1 a.2 ^ (α : ℝ) := by
  rw [← nhds_prod_eq]
  refine hφ.isBigO_sub.trans ?_
  rw [nhds_prod_eq]
  exact TauCeti.isBigO_sub_dist_rpow hα z₀

/-- A map that is `C^n` at `z₀`, for some `n ≠ 0`, has differences `O(‖z - w‖ ^ α)` near
`(z₀, z₀)` for `α ≤ 1`. -/
theorem ContDiffAt.isBigO_sub_dist_rpow {𝕜 : Type*} [RCLike 𝕜] {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {φ : E → F} {z₀ : E} {n : WithTop ℕ∞} (hφ : ContDiffAt 𝕜 n φ z₀) (hn : n ≠ 0)
    {α : ℝ≥0} (hα : α ≤ 1) :
    (fun a : E × E ↦ φ a.1 - φ a.2) =O[𝓝 z₀ ×ˢ 𝓝 z₀] fun a ↦ dist a.1 a.2 ^ (α : ℝ) :=
  (hφ.hasStrictFDerivAt_fderiv hn).isBigO_sub_dist_rpow hα

/-- A map `ψ` that is `α`-Hölder on a set `K`, composed with a map `τ` that is Lipschitz on a
neighbourhood of `z₀` and maps a neighbourhood of `z₀` into `K`, has differences
`O(dist z w ^ α)` near `(z₀, z₀)`. -/
theorem HolderOnWith.isBigO_comp_sub_dist_rpow_of_lipschitzOnWith {X Y G : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] [SeminormedAddCommGroup G] {ψ : Y → G}
    {C α : ℝ≥0} {K : Set Y} (hH : HolderOnWith C α ψ K) {τ : X → Y} {z₀ : X} {L : ℝ≥0}
    {U : Set X} (hU : U ∈ 𝓝 z₀) (hτ : LipschitzOnWith L τ U) (hK : ∀ᶠ z in 𝓝 z₀, τ z ∈ K) :
    (fun a : X × X ↦ ψ (τ a.1) - ψ (τ a.2)) =O[𝓝 z₀ ×ˢ 𝓝 z₀]
      fun a ↦ dist a.1 a.2 ^ (α : ℝ) := by
  refine .of_bound (C * L ^ (α : ℝ)) ?_
  filter_upwards [prod_mem_prod (inter_mem hU hK) (inter_mem hU hK)] with a ha
  rw [Real.norm_of_nonneg (by positivity), ← dist_eq_norm, mul_assoc,
    ← Real.mul_rpow L.coe_nonneg dist_nonneg]
  refine (hH.dist_le ha.1.2 ha.2.2).trans ?_
  gcongr
  exact hτ.dist_le_mul _ ha.1.1 _ ha.2.1

/-- A map `ψ` that is `α`-Hölder on a set `K`, composed with a map `τ` that is `C^1` at `z₀` and
maps a neighbourhood of `z₀` into `K`, has differences `O(‖z - w‖ ^ α)` near `(z₀, z₀)`. -/
theorem HolderOnWith.isBigO_comp_sub_dist_rpow {𝕜 : Type*} [RCLike 𝕜] {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [SeminormedAddCommGroup G] {ψ : F → G} {C α : ℝ≥0} {K : Set F}
    (hH : HolderOnWith C α ψ K) {τ : E → F} {z₀ : E} (hτ : ContDiffAt 𝕜 1 τ z₀)
    (hK : ∀ᶠ z in 𝓝 z₀, τ z ∈ K) :
    (fun a : E × E ↦ ψ (τ a.1) - ψ (τ a.2)) =O[𝓝 z₀ ×ˢ 𝓝 z₀]
      fun a ↦ dist a.1 a.2 ^ (α : ℝ) := by
  obtain ⟨L, U, hU, hL⟩ := hτ.exists_lipschitzOnWith
  exact hH.isBigO_comp_sub_dist_rpow_of_lipschitzOnWith hU hL hK

/-- An estimate `φ z - φ w = O(dist z w ^ α)` near `(z₀, z₀)` gives an `α`-Hölder bound for `φ`
on a ball around `z₀`. -/
theorem Asymptotics.IsBigO.exists_holderOnWith_ball {X G : Type*} [PseudoMetricSpace X]
    [SeminormedAddCommGroup G] {φ : X → G} {α : ℝ≥0} {z₀ : X}
    (h : (fun a : X × X ↦ φ a.1 - φ a.2) =O[𝓝 z₀ ×ˢ 𝓝 z₀] fun a ↦ dist a.1 a.2 ^ (α : ℝ)) :
    ∃ r > 0, ∃ L : ℝ≥0, HolderOnWith L α φ (Metric.ball z₀ r) := by
  obtain ⟨c, hc, hcO⟩ := h.exists_pos
  obtain ⟨u, hu, hub⟩ := eventually_prod_self_iff'.mp hcO.bound
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.mp hu
  refine ⟨r, hr, ⟨c, hc.le⟩, HolderOnWith.of_dist_le fun z hz w hw ↦ ?_⟩
  have h := hub z (hru hz) w (hru hw)
  rwa [Real.norm_of_nonneg (by positivity), ← dist_eq_norm] at h
