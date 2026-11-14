/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import TauCeti.Topology.MetricSpace.Holder

/-!
# Hölder continuity of the top derivative of a composite

Let `τ` be `C^{k+1}` near a point `z₀` and `g` be `C^k`, with `k`th derivative `α`-Hölder near
`τ z₀`, for some `α ≤ 1`. Then the `k`th derivative of `g ∘ τ` is `α`-Hölder on a ball around
`z₀` (`TauCeti.exists_holderOnWith_iteratedFDerivWithin_comp`).

By the Faà di Bruno formula (`iteratedFDerivWithin_comp`), the `k`th derivative of `g ∘ τ` is a
sum of multilinear expressions in the derivatives of `g` at `τ z` of order at most `k` and in the
derivatives of `τ` at `z` of order at most `k`, and Mathlib's
`FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO` reduces the Hölder estimate to Hölder
estimates for those factors. The derivatives of `τ`, and those of `g` of order less than `k`, are
`C^1`, hence locally Lipschitz, and a Lipschitz bound gives an `α`-Hölder bound at distances at
most one. The derivative of order `k` of `g` is Hölder by hypothesis, and `τ` is locally
Lipschitz.

This is the estimate behind the independence of the Hölder spaces `C^{k,α}` of a compact manifold
from the choice of charts: with `τ` a transition map between two charts.
-/

public section

open Asymptotics Filter Set Topology
open scoped NNReal

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

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

/-- A map that is `C^1` at `z₀` has differences `O(‖z - w‖ ^ α)` near `(z₀, z₀)` for `α ≤ 1`. -/
theorem _root_.ContDiffAt.isBigO_sub_dist_rpow {φ : E → F} {z₀ : E} (hφ : ContDiffAt 𝕜 1 φ z₀)
    {α : ℝ≥0} (hα : α ≤ 1) :
    (fun a : E × E ↦ φ a.1 - φ a.2) =O[𝓝 z₀ ×ˢ 𝓝 z₀] fun a ↦ dist a.1 a.2 ^ (α : ℝ) := by
  rw [← nhds_prod_eq]
  refine (hφ.hasStrictFDerivAt_fderiv one_ne_zero).isBigO_sub.trans ?_
  rw [nhds_prod_eq]
  exact TauCeti.isBigO_sub_dist_rpow hα z₀

/-- A map continuous at `z₀`, evaluated at either coordinate, is bounded near `(z₀, z₀)`. -/
private theorem isBoundedUnder_norm_comp_fst_snd {φ : E → F} {z₀ : E} (hφ : ContinuousAt φ z₀) :
    (𝓝 z₀ ×ˢ 𝓝 z₀).IsBoundedUnder (· ≤ ·) (fun a : E × E ↦ ‖φ a.1‖) ∧
      (𝓝 z₀ ×ˢ 𝓝 z₀).IsBoundedUnder (· ≤ ·) (fun a : E × E ↦ ‖φ a.2‖) :=
  ⟨(hφ.tendsto.comp tendsto_fst).norm.isBoundedUnder_le,
    (hφ.tendsto.comp tendsto_snd).norm.isBoundedUnder_le⟩

omit [NormedSpace 𝕜 G] in
/-- The top derivative of `g`, Hölder on a neighbourhood of `τ z₀`, composed with a map `τ` that
is `C^1` at `z₀`, has differences `O(‖z - w‖ ^ α)` near `(z₀, z₀)`. -/
private theorem isBigO_holder_comp {τ : E → F} {z₀ : E} (hτ : ContDiffAt 𝕜 1 τ z₀) {K : Set F}
    (hK : K ∈ 𝓝 (τ z₀)) {ψ : F → G} {C α : ℝ≥0} (hH : HolderOnWith C α ψ K) :
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

variable {g : F → G} {τ : E → F} {s : Set E} {t : Set F} {k : ℕ} {α : ℝ≥0} {z₀ : E}

/-- **The Hölder chain rule for the top derivative.** Let `τ` be `C^{k+1}` on a neighbourhood `s`
of `z₀`, mapping it into a set `t` on which `g` is `C^k`, with both sets of unique
differentiability. If the `k`th derivative of `g` within `t` is `α`-Hölder on a neighbourhood of
`τ z₀`, with `α ≤ 1`, then the `k`th derivative of `g ∘ τ` within `s` is `α`-Hölder on a ball
around `z₀`. -/
theorem exists_holderOnWith_iteratedFDerivWithin_comp (hα : α ≤ 1) (hs : s ∈ 𝓝 z₀)
    (hus : UniqueDiffOn 𝕜 s) (hut : UniqueDiffOn 𝕜 t) (hτ : ContDiffOn 𝕜 (k + 1) τ s)
    (hg : ContDiffOn 𝕜 k g t) (hst : MapsTo τ s t) {K : Set F} (hK : K ∈ 𝓝 (τ z₀)) {C : ℝ≥0}
    (hH : HolderOnWith C α (iteratedFDerivWithin 𝕜 k g t) K) :
    ∃ r > 0, ∃ L : ℝ≥0,
      HolderOnWith L α (iteratedFDerivWithin 𝕜 k (g ∘ τ) s) (Metric.ball z₀ r) := by
  have hz₀ : z₀ ∈ s := mem_of_mem_nhds hs
  have hτk : ContDiffOn 𝕜 k τ s := hτ.of_le (by simp)
  have hτt : τ z₀ ∈ t := hst hz₀
  -- The derivatives of `τ` of order at most `k` are `C^1` at `z₀`.
  have hτm (m : ℕ) (hm : m ≤ k) : ContDiffAt 𝕜 1 (iteratedFDerivWithin 𝕜 m τ s) z₀ :=
    (ContDiffWithinAt.iteratedFDerivWithin_right (hτ z₀ hz₀) hus
      (by exact_mod_cast (by omega : 1 + m ≤ k + 1)) hz₀).contDiffAt hs
  -- The derivatives of `g` of order at most `k`, along `τ`, are continuous at `z₀`.
  have hgc (m : ℕ) (hm : m ≤ k) :
      ContinuousAt (fun z ↦ iteratedFDerivWithin 𝕜 m g t (τ z)) z₀ :=
    (((hg.continuousOn_iteratedFDerivWithin (by exact_mod_cast hm) hut) _ hτt).comp
      (ContDiffWithinAt.continuousWithinAt (hτ z₀ hz₀)) hst).continuousAt hs
  have hfor (a : E × E) (ha : a.1 ∈ s ∧ a.2 ∈ s) :
      iteratedFDerivWithin 𝕜 k (g ∘ τ) s a.1 - iteratedFDerivWithin 𝕜 k (g ∘ τ) s a.2 =
        (ftaylorSeriesWithin 𝕜 g t (τ a.1)).taylorComp (ftaylorSeriesWithin 𝕜 τ s a.1) k -
          (ftaylorSeriesWithin 𝕜 g t (τ a.2)).taylorComp (ftaylorSeriesWithin 𝕜 τ s a.2) k := by
    rw [iteratedFDerivWithin_comp (hg _ (hst ha.1)) (hτk _ ha.1) hut hus ha.1 hst le_rfl,
      iteratedFDerivWithin_comp (hg _ (hst ha.2)) (hτk _ ha.2) hut hus ha.2 hst le_rfl]
  have hO := FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO (n := k)
    (p₁ := fun a : E × E ↦ ftaylorSeriesWithin 𝕜 g t (τ a.1))
    (p₂ := fun a : E × E ↦ ftaylorSeriesWithin 𝕜 g t (τ a.2))
    (q₁ := fun a : E × E ↦ ftaylorSeriesWithin 𝕜 τ s a.1)
    (q₂ := fun a : E × E ↦ ftaylorSeriesWithin 𝕜 τ s a.2)
    (f := fun a : E × E ↦ dist a.1 a.2 ^ (α : ℝ)) (l := 𝓝 z₀ ×ˢ 𝓝 z₀)
    (fun m hm ↦ (isBoundedUnder_norm_comp_fst_snd (hgc m hm)).1)
    (fun m hm ↦ by
      rcases hm.lt_or_eq with hm | rfl
      · -- Below the top order, the derivatives of `g` along `τ` are `C^1`.
        refine ContDiffAt.isBigO_sub_dist_rpow (𝕜 := 𝕜)
          (φ := fun z ↦ iteratedFDerivWithin 𝕜 m g t (τ z)) ?_ hα
        exact (ContDiffWithinAt.comp z₀ (ContDiffWithinAt.iteratedFDerivWithin_right (hg _ hτt)
          hut (by exact_mod_cast (by omega : 1 + m ≤ k)) hτt)
          (ContDiffWithinAt.of_le (hτ z₀ hz₀) (by simp)) hst).contDiffAt hs
      · exact isBigO_holder_comp
          ((ContDiffWithinAt.of_le (hτ z₀ hz₀) (by simp)).contDiffAt hs) hK hH)
    (fun m hm ↦ (isBoundedUnder_norm_comp_fst_snd (hτm m hm).continuousAt).1)
    (fun m hm ↦ (isBoundedUnder_norm_comp_fst_snd (hτm m hm).continuousAt).2)
    (fun m hm ↦ (hτm m hm).isBigO_sub_dist_rpow hα)
  obtain ⟨c, hc, hcO⟩ := hO.exists_pos
  obtain ⟨u, hu, hub⟩ := eventually_prod_self_iff'.mp
    ((hcO.bound.and (prod_mem_prod hs hs)).mono fun a ha ↦ by
      rw [hfor a ha.2]
      exact ha.1 :
      ∀ᶠ a in 𝓝 z₀ ×ˢ 𝓝 z₀, ‖iteratedFDerivWithin 𝕜 k (g ∘ τ) s a.1 -
        iteratedFDerivWithin 𝕜 k (g ∘ τ) s a.2‖ ≤ c * ‖dist a.1 a.2 ^ (α : ℝ)‖)
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.mp hu
  refine ⟨r, hr, ⟨c, hc.le⟩, HolderOnWith.of_dist_le fun z hz w hw ↦ ?_⟩
  have h := hub z (hru hz) w (hru hw)
  rwa [Real.norm_of_nonneg (by positivity), ← dist_eq_norm] at h

end TauCeti
