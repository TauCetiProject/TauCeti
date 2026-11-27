/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import TauCeti.Topology.MetricSpace.Holder
import TauCeti.Analysis.Holder.IsBigO
import TauCeti.Analysis.Holder.MeanValue
import TauCeti.Analysis.Normed.Operator.Holder

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

In the other order, a `C²` map `g` after a `C¹` map `p` with `α`-Hölder derivative has
`α`-Hölder derivative on a ball (`TauCeti.exists_ball_contDiffOn_holderOnWith_fderiv_comp`): the
derivative `Dg(p x) ∘ Dp(x)` is a bilinear expression in the factor `Dg ∘ p`, which is `C¹` and
hence Lipschitz on a closed ball, and in the Hölder factor `Dp`. This is how a coefficient field
built from `C^{1,α}` functions by smooth operations stays of class `C^{1,α}`.
-/

public section

open Asymptotics Filter Set Topology
open scoped NNReal

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable {g : F → G} {τ : E → F} {s : Set E} {t : Set F} {k : ℕ} {α : ℝ≥0} {z₀ : E}

/-- The Hölder estimate for the top derivative of a composite on an open set `u`, in the form
`D z - D w = O(dist z w ^ α)` near `(z₀, z₀)`. -/
private theorem isBigO_iteratedFDerivWithin_comp_sub {u : Set E} (hα : α ≤ 1) (hu : IsOpen u)
    (hz₀ : z₀ ∈ u) (hut : UniqueDiffOn 𝕜 t) (hτ : ContDiffOn 𝕜 (k + 1) τ u)
    (hg : ContDiffOn 𝕜 k g t) (hst : MapsTo τ u t) {K : Set F} (hτK : ∀ᶠ z in 𝓝 z₀, τ z ∈ K)
    {C : ℝ≥0} (hH : HolderOnWith C α (iteratedFDerivWithin 𝕜 k g t) K) :
    (fun a : E × E ↦ iteratedFDerivWithin 𝕜 k (g ∘ τ) u a.1 -
      iteratedFDerivWithin 𝕜 k (g ∘ τ) u a.2) =O[𝓝 z₀ ×ˢ 𝓝 z₀]
        fun a ↦ dist a.1 a.2 ^ (α : ℝ) := by
  have hu' : u ∈ 𝓝 z₀ := hu.mem_nhds hz₀
  have hτk : ContDiffOn 𝕜 k τ u := hτ.of_le (by simp)
  have hτt : τ z₀ ∈ t := hst hz₀
  -- The derivatives of `τ` of order at most `k` are `C^1` at `z₀`.
  have hτm (m : ℕ) (hm : m ≤ k) : ContDiffAt 𝕜 1 (iteratedFDerivWithin 𝕜 m τ u) z₀ :=
    (ContDiffWithinAt.iteratedFDerivWithin_right (hτ z₀ hz₀) hu.uniqueDiffOn
      (by exact_mod_cast (by omega : 1 + m ≤ k + 1)) hz₀).contDiffAt hu'
  -- The derivatives of `g` of order at most `k`, along `τ`, are continuous at `z₀`.
  have hgc (m : ℕ) (hm : m ≤ k) :
      ContinuousAt (fun z ↦ iteratedFDerivWithin 𝕜 m g t (τ z)) z₀ :=
    (((hg.continuousOn_iteratedFDerivWithin (by exact_mod_cast hm) hut) _ hτt).comp
      (ContDiffWithinAt.continuousWithinAt (hτ z₀ hz₀)) hst).continuousAt hu'
  have hO := FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO (n := k)
    (p₁ := fun a : E × E ↦ ftaylorSeriesWithin 𝕜 g t (τ a.1))
    (p₂ := fun a : E × E ↦ ftaylorSeriesWithin 𝕜 g t (τ a.2))
    (q₁ := fun a : E × E ↦ ftaylorSeriesWithin 𝕜 τ u a.1)
    (q₂ := fun a : E × E ↦ ftaylorSeriesWithin 𝕜 τ u a.2)
    (f := fun a : E × E ↦ dist a.1 a.2 ^ (α : ℝ)) (l := 𝓝 z₀ ×ˢ 𝓝 z₀)
    (fun m hm ↦ ((hgc m hm).tendsto.comp tendsto_fst).norm.isBoundedUnder_le)
    (fun m hm ↦ by
      rcases hm.lt_or_eq with hm | rfl
      · -- Below the top order, the derivatives of `g` along `τ` are `C^1`.
        refine ContDiffAt.isBigO_sub_dist_rpow (𝕜 := 𝕜)
          (φ := fun z ↦ iteratedFDerivWithin 𝕜 m g t (τ z)) ?_ one_ne_zero hα
        exact (ContDiffWithinAt.comp z₀ (ContDiffWithinAt.iteratedFDerivWithin_right (hg _ hτt)
          hut (by exact_mod_cast (by omega : 1 + m ≤ k)) hτt)
          (ContDiffWithinAt.of_le (hτ z₀ hz₀) (by simp)) hst).contDiffAt hu'
      · exact hH.isBigO_comp_sub_dist_rpow ((hτ.of_le (by simp) z₀ hz₀).contDiffAt hu') hτK)
    (fun m hm ↦ ((hτm m hm).continuousAt.tendsto.comp tendsto_fst).norm.isBoundedUnder_le)
    (fun m hm ↦ ((hτm m hm).continuousAt.tendsto.comp tendsto_snd).norm.isBoundedUnder_le)
    (fun m hm ↦ (hτm m hm).isBigO_sub_dist_rpow one_ne_zero hα)
  refine hO.congr' ?_ EventuallyEq.rfl
  filter_upwards [prod_mem_prod hu' hu'] with a ha
  rw [iteratedFDerivWithin_comp (hg _ (hst ha.1)) (hτk _ ha.1) hut hu.uniqueDiffOn ha.1 hst le_rfl,
    iteratedFDerivWithin_comp (hg _ (hst ha.2)) (hτk _ ha.2) hut hu.uniqueDiffOn ha.2 hst le_rfl]

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
  -- Work on the open set `interior s`, where the derivatives within `s` are unchanged.
  have hs' : interior s ∈ 𝓝 z₀ := interior_mem_nhds.mpr hs
  have hτ' : ContDiffOn 𝕜 (k + 1) τ (interior s) := hτ.mono interior_subset
  have hst' : MapsTo τ (interior s) t := hst.mono_left interior_subset
  have hτK : ∀ᶠ z in 𝓝 z₀, τ z ∈ K :=
    (tendsto_nhdsWithin_iff.mpr ⟨((hτ'.continuousOn _ (mem_of_mem_nhds hs')).continuousAt
      hs').tendsto, mem_of_superset hs' hst'⟩).eventually hK
  refine ((isBigO_iteratedFDerivWithin_comp_sub hα isOpen_interior (mem_of_mem_nhds hs') hut hτ'
    hg hst' hτK hH).congr' ?_ EventuallyEq.rfl).exists_holderOnWith_ball
  have hint (z : E) (hz : z ∈ interior s) :
      iteratedFDerivWithin 𝕜 k (g ∘ τ) (interior s) z = iteratedFDerivWithin 𝕜 k (g ∘ τ) s z :=
    iteratedFDerivWithin_congr_set
      ((eventuallyEqSet_univ.mpr (isOpen_interior.mem_nhds hz)).trans
        (eventuallyEqSet_univ.mpr (mem_interior_iff_mem_nhds.mp hz)).symm) k
  filter_upwards [prod_mem_prod hs' hs'] with a ha
  rw [hint _ ha.1, hint _ ha.2]

/-- **A `C²` map after a `C^{1,α}` map is `C^{1,α}`.** If `p` is `C¹` on a neighbourhood `s` of
`z₀` with `α`-Hölder derivative there, `α ≤ 1`, and `g` is `C²` at `p z₀`, then `g ∘ p` is `C¹`
with `α`-Hölder derivative on a ball around `z₀`. -/
theorem exists_ball_contDiffOn_holderOnWith_fderiv_comp {E V W : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] {g : V → W} {p : E → V} {s : Set E} {z₀ : E} {α C : ℝ≥0} (hα : α ≤ 1)
    (hs : s ∈ 𝓝 z₀) (hp : ContDiffOn ℝ 1 p s) (hpH : HolderOnWith C α (fderiv ℝ p) s)
    (hg : ContDiffAt ℝ 2 g (p z₀)) :
    ∃ r > 0, Metric.ball z₀ r ⊆ s ∧ ContDiffOn ℝ 1 (g ∘ p) (Metric.ball z₀ r) ∧
      ∃ K, HolderOnWith K α (fderiv ℝ (g ∘ p)) (Metric.ball z₀ r) := by
  obtain ⟨t, ht, hgt⟩ := hg.contDiffOn (m := 2) le_rfl (by simp)
  have hgt' : ContDiffOn ℝ 2 g (interior t) := hgt.mono interior_subset
  have hps : ContDiffOn ℝ 1 p (interior s) := hp.mono interior_subset
  -- The open set `U` on which `p` is `C¹` and `g` is `C²` near the values of `p`.
  set U := interior s ∩ p ⁻¹' interior t
  have hU : U ∈ 𝓝 z₀ :=
    inter_mem (interior_mem_nhds.mpr hs) ((hp.continuousOn.continuousAt hs).preimage_mem_nhds
      (interior_mem_nhds.mpr ht))
  have hmaps : MapsTo p U (interior t) := fun _ hx ↦ hx.2
  -- The factor `x ↦ Dg (p x)` is `C¹`, so Lipschitz near `z₀`; both factors are bounded there.
  have hDg : ContDiffOn ℝ 1 (fun x ↦ fderiv ℝ g (p x)) U :=
    (hgt'.fderiv_of_isOpen isOpen_interior (by norm_num)).comp
      (hps.mono inter_subset_left) hmaps
  have hDp : ContinuousOn (fderiv ℝ p) U :=
    (hps.continuousOn_fderiv_of_isOpen isOpen_interior le_rfl).mono inter_subset_left
  obtain ⟨L, t', ht', hL⟩ := (hDg.contDiffAt hU).exists_lipschitzOnWith
  obtain ⟨r, hr, hrU⟩ := Metric.eventually_nhds_iff_ball.mp <|
    (Filter.Eventually.and (eventually_mem_set.2 hU) (eventually_mem_set.2 ht')).and <|
    ((hDg.continuousOn.continuousAt hU).norm.eventually_lt_const (lt_add_one _)).and
      ((hDp.continuousAt hU).norm.eventually_lt_const (lt_add_one _))
  have hball : Metric.ball z₀ r ⊆ U := fun x hx ↦ (hrU x hx).1.1
  have hK₁ := (hL.mono fun x hx ↦ (hrU x hx).1.2).holderOnWith_of_norm_le
    (M := (‖fderiv ℝ g (p z₀)‖ + 1).toNNReal)
    (fun x hx ↦ (hrU x hx).2.1.le.trans (Real.le_coe_toNNReal _)) hα
  have hprod := (ContinuousLinearMap.compL ℝ E V W).holderOnWith_comp₂ hK₁
    (hpH.mono (hball.trans (inter_subset_left.trans interior_subset)))
    (Mf := (‖fderiv ℝ g (p z₀)‖ + 1).toNNReal) (Mg := (‖fderiv ℝ p z₀‖ + 1).toNNReal)
    (fun x hx ↦ (hrU x hx).2.1.le.trans (Real.le_coe_toNNReal _))
    (fun x hx ↦ (hrU x hx).2.2.le.trans (Real.le_coe_toNNReal _))
  refine ⟨r, hr, hball.trans (inter_subset_left.trans interior_subset),
    ((hgt'.of_le (by norm_num)).comp (hps.mono inter_subset_left) hmaps).mono hball, _,
    hprod.congr fun x hx ↦ ?_⟩
  -- The chain rule at points of the ball.
  have hpx : DifferentiableAt ℝ p x :=
    (hps.contDiffAt (isOpen_interior.mem_nhds (hball hx).1)).differentiableAt one_ne_zero
  have hgx : DifferentiableAt ℝ g (p x) :=
    (hgt'.contDiffAt (isOpen_interior.mem_nhds (hball hx).2)).differentiableAt two_ne_zero
  simp [fderiv_comp x hgx hpx]

end TauCeti
