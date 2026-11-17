/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import TauCeti.Topology.MetricSpace.Holder
import TauCeti.Analysis.Holder.IsBigO

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
most one (`ContDiffAt.isBigO_sub_dist_rpow`). The derivative of order `k` of `g` is Hölder by
hypothesis, and `τ` is locally Lipschitz (`HolderOnWith.isBigO_comp_sub_dist_rpow`). The
resulting estimate gives a Hölder bound on a ball (`Asymptotics.IsBigO.exists_holderOnWith_ball`).

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

variable {g : F → G} {τ : E → F} {s : Set E} {t : Set F} {k : ℕ} {α : ℝ≥0} {z₀ : E}

/-- **The Hölder chain rule for the top derivative.** Let `τ` be `C^{k+1}` on a neighbourhood `s`
of `z₀`, mapping it into a set `t` of unique differentiability on which `g` is `C^k`. If the `k`th
derivative of `g` within `t` is `α`-Hölder on a neighbourhood of `τ z₀` within `t`, with `α ≤ 1`,
then the `k`th derivative of `g ∘ τ` within `s` is `α`-Hölder on a ball around `z₀`. -/
theorem exists_holderOnWith_iteratedFDerivWithin_comp (hα : α ≤ 1) (hs : s ∈ 𝓝 z₀)
    (hut : UniqueDiffOn 𝕜 t) (hτ : ContDiffOn 𝕜 (k + 1) τ s) (hg : ContDiffOn 𝕜 k g t)
    (hst : MapsTo τ s t) {K : Set F} (hK : K ∈ 𝓝[t] (τ z₀)) {C : ℝ≥0}
    (hH : HolderOnWith C α (iteratedFDerivWithin 𝕜 k g t) K) :
    ∃ r > 0, ∃ L : ℝ≥0,
      HolderOnWith L α (iteratedFDerivWithin 𝕜 k (g ∘ τ) s) (Metric.ball z₀ r) := by
  -- Work on the open set `interior s`, which has unique differentiability.
  have hs' : interior s ∈ 𝓝 z₀ := interior_mem_nhds.mpr hs
  have hus' : UniqueDiffOn 𝕜 (interior s) := isOpen_interior.uniqueDiffOn
  have hτ' : ContDiffOn 𝕜 (k + 1) τ (interior s) := hτ.mono interior_subset
  have hst' : MapsTo τ (interior s) t := hst.mono_left interior_subset
  have hz₀ : z₀ ∈ interior s := mem_of_mem_nhds hs'
  have hτk : ContDiffOn 𝕜 k τ (interior s) := hτ'.of_le (by simp)
  have hτt : τ z₀ ∈ t := hst' hz₀
  have hτ1 : ContDiffAt 𝕜 1 τ z₀ := (hτ'.of_le (by simp) z₀ hz₀).contDiffAt hs'
  have hτK : ∀ᶠ z in 𝓝 z₀, τ z ∈ K :=
    (tendsto_nhdsWithin_iff.mpr ⟨hτ1.continuousAt.tendsto, mem_of_superset hs' hst'⟩).eventually
      hK
  -- The derivatives of `τ` of order at most `k` are `C^1` at `z₀`.
  have hτm (m : ℕ) (hm : m ≤ k) :
      ContDiffAt 𝕜 1 (iteratedFDerivWithin 𝕜 m τ (interior s)) z₀ :=
    (ContDiffWithinAt.iteratedFDerivWithin_right (hτ' z₀ hz₀) hus'
      (by exact_mod_cast (by omega : 1 + m ≤ k + 1)) hz₀).contDiffAt hs'
  -- The derivatives of `g` of order at most `k`, along `τ`, are continuous at `z₀`.
  have hgc (m : ℕ) (hm : m ≤ k) :
      ContinuousAt (fun z ↦ iteratedFDerivWithin 𝕜 m g t (τ z)) z₀ :=
    (((hg.continuousOn_iteratedFDerivWithin (by exact_mod_cast hm) hut) _ hτt).comp
      (ContDiffWithinAt.continuousWithinAt (hτ' z₀ hz₀)) hst').continuousAt hs'
  -- On `interior s`, the derivatives within `s` and within `interior s` agree.
  have hint (z : E) (hz : z ∈ interior s) :
      iteratedFDerivWithin 𝕜 k (g ∘ τ) s z = iteratedFDerivWithin 𝕜 k (g ∘ τ) (interior s) z :=
    iteratedFDerivWithin_congr_set
      ((eventuallyEqSet_univ.mpr (mem_interior_iff_mem_nhds.mp hz)).trans
        (eventuallyEqSet_univ.mpr (isOpen_interior.mem_nhds hz)).symm) k
  have hfor (a : E × E) (ha : a.1 ∈ interior s ∧ a.2 ∈ interior s) :
      iteratedFDerivWithin 𝕜 k (g ∘ τ) s a.1 - iteratedFDerivWithin 𝕜 k (g ∘ τ) s a.2 =
        (ftaylorSeriesWithin 𝕜 g t (τ a.1)).taylorComp
            (ftaylorSeriesWithin 𝕜 τ (interior s) a.1) k -
          (ftaylorSeriesWithin 𝕜 g t (τ a.2)).taylorComp
            (ftaylorSeriesWithin 𝕜 τ (interior s) a.2) k := by
    rw [hint _ ha.1, hint _ ha.2,
      iteratedFDerivWithin_comp (hg _ (hst' ha.1)) (hτk _ ha.1) hut hus' ha.1 hst' le_rfl,
      iteratedFDerivWithin_comp (hg _ (hst' ha.2)) (hτk _ ha.2) hut hus' ha.2 hst' le_rfl]
  have hO := FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO (n := k)
    (p₁ := fun a : E × E ↦ ftaylorSeriesWithin 𝕜 g t (τ a.1))
    (p₂ := fun a : E × E ↦ ftaylorSeriesWithin 𝕜 g t (τ a.2))
    (q₁ := fun a : E × E ↦ ftaylorSeriesWithin 𝕜 τ (interior s) a.1)
    (q₂ := fun a : E × E ↦ ftaylorSeriesWithin 𝕜 τ (interior s) a.2)
    (f := fun a : E × E ↦ dist a.1 a.2 ^ (α : ℝ)) (l := 𝓝 z₀ ×ˢ 𝓝 z₀)
    (fun m hm ↦ ((hgc m hm).tendsto.comp tendsto_fst).norm.isBoundedUnder_le)
    (fun m hm ↦ by
      rcases hm.lt_or_eq with hm | rfl
      · -- Below the top order, the derivatives of `g` along `τ` are `C^1`.
        refine ContDiffAt.isBigO_sub_dist_rpow (𝕜 := 𝕜)
          (φ := fun z ↦ iteratedFDerivWithin 𝕜 m g t (τ z)) ?_ one_ne_zero hα
        exact (ContDiffWithinAt.comp z₀ (ContDiffWithinAt.iteratedFDerivWithin_right (hg _ hτt)
          hut (by exact_mod_cast (by omega : 1 + m ≤ k)) hτt)
          (ContDiffWithinAt.of_le (hτ' z₀ hz₀) (by simp)) hst').contDiffAt hs'
      · exact hH.isBigO_comp_sub_dist_rpow hτ1 hτK)
    (fun m hm ↦ ((hτm m hm).continuousAt.tendsto.comp tendsto_fst).norm.isBoundedUnder_le)
    (fun m hm ↦ ((hτm m hm).continuousAt.tendsto.comp tendsto_snd).norm.isBoundedUnder_le)
    (fun m hm ↦ (hτm m hm).isBigO_sub_dist_rpow one_ne_zero hα)
  refine (hO.congr' ?_ EventuallyEq.rfl).exists_holderOnWith_ball
  filter_upwards [prod_mem_prod hs' hs'] with a ha
  exact (hfor a ha).symm

end TauCeti
