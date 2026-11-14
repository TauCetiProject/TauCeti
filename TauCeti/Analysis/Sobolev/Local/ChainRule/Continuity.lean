/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Norm
import TauCeti.Analysis.Sobolev.WeakDeriv.ChainRule
import TauCeti.MeasureTheory.Function.LpSeminorm.Tendsto
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# The `W^{1,p}` bound and continuity of composition with `C¹` maps

Let `g : F → G` be `C¹` on an open set `W`. For a continuous map `u : ℂ → F` sending a set `K` into
`W`, the weak chain rule `TauCeti.HasWeakFDerivOn.contDiffOn_comp` gives the weak derivative
`z ↦ Dg(u z) ∘ Du z` of `g ∘ u` on `interior K`. This file turns it into estimates in the
`W^{1,p}` size `TauCeti.eLpNormWkp p K 1`.

* **Composition bound.** If `‖g ∘ u‖ ≤ C₀` and `‖Dg ∘ u‖ ≤ C₁` on `K`, then
  `‖g ∘ u‖_{W^{1,p}(K)} ≤ C₀ vol(K)^{1/p} + C₁ ‖u‖_{W^{1,p}(K)}`. For a compact `L ⊆ W` the
  constants can be chosen depending only on `g` and `L`, uniformly over all `u` with `u(K) ⊆ L`.
* **Continuity of composition.** Let `K` be compact, let `u` have finite `W^{1,p}(K)` size with
  `u(K) ⊆ W`, and let `uₙ` be eventually continuous on `K`. If `uₙ → u` uniformly on `K` and
  `‖uₙ - u‖_{W^{1,p}(K)} → 0`, then `‖g ∘ uₙ - g ∘ u‖_{W^{1,p}(K)} → 0`. The weak derivative of the
  difference splits as `(Dg(uₙ) - Dg(u)) ∘ Du + Dg(uₙ) ∘ D(uₙ - u)`. The first term tends to `0`
  because `Dg` is uniformly continuous near the compact set `u(K)` inside `W`, and the second
  because `Dg(uₙ)` is eventually bounded on `K`. Only the first derivative of `g` is used.

The uniform convergence hypothesis is not implied by `W^{1,p}(K)` convergence on an arbitrary
compact set `K`, nor for `p ≤ 2`. For `p > 2` and continuous maps on an open planar domain,
Morrey's embedding turns `W^{1,p}_loc` convergence into locally uniform convergence; that
consequence is not proved here.

## Main declarations

* `TauCeti.eLpNormWkp_one_comp_le`: the `W^{1,p}(K)` bound for `g ∘ u` with explicit constants.
* `TauCeti.exists_eLpNormWkp_one_comp_le`: the same with constants depending only on `g` on a
  compact subset of `W` containing `u(K)`.
* `TauCeti.eLpNormWkp_one_comp_sub_le`: the `W^{1,p}(K)` bound for `g ∘ v - g ∘ u` behind the
  continuity statement.
* `TauCeti.tendsto_eLpNormWkp_one_comp_sub`: continuity of `u ↦ g ∘ u` in `W^{1,p}(K)` along
  sequences converging uniformly on the compact set `K`.
* `TauCeti.MemWkpLoc.tendsto_eLpNormWkp_one_comp_sub`: the same for `W^{1,p}_loc(U)` and locally
  uniform convergence on `U`, on every compact subset of `U`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (composition in local Sobolev spaces).
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {p : ℝ≥0∞} {U K : Set ℂ}

variable [CompleteSpace G]

/-- **The `W^{1,p}` bound for composition with a `C¹` map.** Let `g` be `C¹` on an open set `W`
and let `u` be continuous on a measurable set `K`, with `u(K) ⊆ W`. If `‖g ∘ u‖ ≤ C₀` and
`‖Dg ∘ u‖ ≤ C₁` on `K`, then `‖g ∘ u‖_{W^{1,p}(K)} ≤ C₀ vol(K)^{1/p} + C₁ ‖u‖_{W^{1,p}(K)}`,
provided `u` has finite `W^{1,p}(K)` size in the case `C₁ = 0`. -/
theorem eLpNormWkp_one_comp_le {u : ℂ → F} {g : F → G} {W : Set F} {C₀ C₁ : ℝ≥0}
    (hK : MeasurableSet K) (hu : C₁ = 0 → eLpNormWkp p K 1 u ≠ ∞) (huc : ContinuousOn u K)
    (hW : IsOpen W) (hg : ContDiffOn ℝ 1 g W) (huW : MapsTo u K W)
    (hC₀ : ∀ z ∈ K, ‖g (u z)‖₊ ≤ C₀) (hC₁ : ∀ z ∈ K, ‖fderiv ℝ g (u z)‖₊ ≤ C₁) :
    eLpNormWkp p K 1 (fun z => g (u z)) ≤
      C₀ * volume K ^ p.toReal⁻¹ + C₁ * eLpNormWkp p K 1 u := by
  -- The weak derivative of `g ∘ u` on `interior K` is `Dg(u) ∘ Du`.
  refine le_add_mul_eLpNormWkp_succ_of_forall_hasWeakFDerivOn ENNReal.coe_ne_top
    (fun h => hu (ENNReal.coe_eq_zero.1 h)) fun D hD hDp => ?_
  rw [eLpNormWkp_zero] at hDp
  refine (eLpNormWkp_succ_le (hD.contDiffOn_comp (huc.mono interior_subset) hW hg
    (huW.mono_left interior_subset))).trans ?_
  simp only [eLpNormWkp_zero]
  gcongr ?_ + ?_
  · have := eLpNorm_le_of_ae_nnNorm_bound (p := p) (μ := volume.restrict K)
      ((hg.continuousOn.comp huc huW).aestronglyMeasurable hK)
      ((ae_restrict_mem hK).mono fun z hz => hC₀ z hz)
    simpa [Measure.restrict_apply_univ, ENNReal.smul_def, smul_eq_mul, Function.comp_def] using this
  · refine (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
      ((ContinuousLinearMap.compL ℝ ℂ F G).aestronglyMeasurable_comp₂
        (((hg.continuousOn_fderiv_of_isOpen hW le_rfl).comp huc huW).aestronglyMeasurable hK)
        (aestronglyMeasurable_of_eLpNorm_ne_top hDp))
      ((ae_restrict_mem hK).mono fun z hz => ?_) p).trans (mul_le_mul_right le_add_self _)
    exact (ContinuousLinearMap.opNNNorm_comp_le _ _).trans (by gcongr; exact hC₁ z hz)

/-- **A uniform `W^{1,p}` bound for composition with a `C¹` map.** Let `g` be `C¹` on an open set
`W` and let `L ⊆ W` be compact. There are constants `C₀`, `C₁`, depending only on `g` on `L`
(bounds for `‖g‖` and `‖Dg‖` there), such that
`‖g ∘ u‖_{W^{1,p}(K)} ≤ C₀ vol(K)^{1/p} + C₁ ‖u‖_{W^{1,p}(K)}` for every exponent `p`, every
measurable `K`, and every continuous `u` on `K` with `u(K) ⊆ L`. -/
theorem exists_eLpNormWkp_one_comp_le {g : F → G} {W L : Set F} (hW : IsOpen W)
    (hg : ContDiffOn ℝ 1 g W) (hL : IsCompact L) (hLW : L ⊆ W) :
    ∃ C₀ C₁ : ℝ≥0, ∀ (p : ℝ≥0∞) (K : Set ℂ) (u : ℂ → F), MeasurableSet K →
      ContinuousOn u K → MapsTo u K L →
        eLpNormWkp p K 1 (fun z => g (u z)) ≤
          C₀ * volume K ^ p.toReal⁻¹ + C₁ * eLpNormWkp p K 1 u := by
  obtain ⟨M₀, hM₀⟩ := hL.exists_bound_of_continuousOn (hg.continuousOn.mono hLW)
  obtain ⟨M₁, hM₁⟩ := hL.exists_bound_of_continuousOn
    ((hg.continuousOn_fderiv_of_isOpen hW le_rfl).mono hLW)
  refine ⟨M₀.toNNReal, M₁.toNNReal + 1, fun p K u hK huc huL =>
    eLpNormWkp_one_comp_le hK (fun h => absurd h (by positivity)) huc hW hg (huL.mono_right hLW)
      (fun z hz => ?_) fun z hz => ?_⟩
  · rw [← NNReal.coe_le_coe, coe_nnNorm]
    exact (hM₀ _ (huL hz)).trans (Real.le_coe_toNNReal M₀)
  · rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_add, NNReal.coe_one]
    exact (hM₁ _ (huL hz)).trans
      ((Real.le_coe_toNNReal M₁).trans (le_add_of_nonneg_right zero_le_one))

/-- **The `W^{1,p}` bound for a difference of compositions with a `C¹` map.** Let `g` be `C¹` on an
open set `W`, let `v` and `u` be continuous on a measurable set `K` with `v(K), u(K) ⊆ W`, and let
`Du` be a weak derivative of `u` on `interior K`. If `‖Dg ∘ v‖ ≤ C` on `K`, then, with
`A = ENNReal.LpAddConst p`,
`‖g ∘ v - g ∘ u‖_{W^{1,p}(K)} ≤ ‖g ∘ v - g ∘ u‖_{Lᵖ(K)} + A ‖(Dg(v) - Dg(u)) ∘ Du‖_{Lᵖ(K)}
+ A C ‖v - u‖_{W^{1,p}(K)}`, provided `‖v - u‖_{W^{1,p}(K)}` is finite in the case `C = 0`. -/
theorem eLpNormWkp_one_comp_sub_le {v u : ℂ → F} {g : F → G} {W : Set F} {C : ℝ≥0}
    {Du : ℂ → ℂ →L[ℝ] F} (hK : MeasurableSet K) (hW : IsOpen W) (hg : ContDiffOn ℝ 1 g W)
    (hvc : ContinuousOn v K) (hvW : MapsTo v K W) (huc : ContinuousOn u K) (huW : MapsTo u K W)
    (hDu : HasWeakFDerivOn volume (Opens.interior K) u Du)
    (hfin : C = 0 → eLpNormWkp p K 1 (v - u) ≠ ∞) (hC : ∀ z ∈ K, ‖fderiv ℝ g (v z)‖₊ ≤ C) :
    eLpNormWkp p K 1 (g ∘ v - g ∘ u) ≤
      eLpNorm (g ∘ v - g ∘ u) p (volume.restrict K) +
        ENNReal.LpAddConst p *
          eLpNorm (fun z => (fderiv ℝ g (v z) - fderiv ℝ g (u z)).comp (Du z))
            p (volume.restrict K) +
        ENNReal.LpAddConst p * C * eLpNormWkp p K 1 (v - u) := by
  refine le_add_mul_eLpNormWkp_succ_of_forall_hasWeakFDerivOn
    (ENNReal.mul_ne_top (ENNReal.LpAddConst_lt_top p).ne ENNReal.coe_ne_top)
    (fun h => hfin (ENNReal.coe_eq_zero.1 ((mul_eq_zero.1 h).resolve_left
      (ENNReal.LpAddConst_ne_zero p))))
    fun D hD hDp => ?_
  rw [eLpNormWkp_zero] at hDp
  -- The weak derivative of `g ∘ v - g ∘ u` is `(Dg(v) - Dg(u)) ∘ Du + Dg(v) ∘ D`.
  have hDv : HasWeakFDerivOn volume (Opens.interior K) v (D + Du) := by
    simpa using hD.add hDu
  refine (eLpNormWkp_succ_le ((hDv.contDiffOn_comp (hvc.mono interior_subset) hW hg
    (hvW.mono_left interior_subset)).sub (hDu.contDiffOn_comp (huc.mono interior_subset) hW hg
      (huW.mono_left interior_subset)))).trans ?_
  rw [eLpNormWkp_zero, add_assoc, mul_assoc, ← mul_add]
  refine add_le_add le_rfl ?_
  have hsplit : ((fun z => (fderiv ℝ g (v z)).comp ((D + Du) z)) -
      fun z => (fderiv ℝ g (u z)).comp (Du z)) =
      (fun z => (fderiv ℝ g (v z) - fderiv ℝ g (u z)).comp (Du z)) +
        fun z => (fderiv ℝ g (v z)).comp (D z) := by
    ext1 z
    simp only [Pi.sub_apply, Pi.add_apply, ContinuousLinearMap.comp_add,
      ContinuousLinearMap.sub_comp]
    abel
  rw [hsplit, eLpNormWkp_zero]
  refine (eLpNorm_add_le' p).trans (mul_le_mul' le_rfl (add_le_add le_rfl ?_))
  refine (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    ((ContinuousLinearMap.compL ℝ ℂ F G).aestronglyMeasurable_comp₂
      (((hg.continuousOn_fderiv_of_isOpen hW le_rfl).comp hvc hvW).aestronglyMeasurable hK)
      (aestronglyMeasurable_of_eLpNorm_ne_top hDp))
    ((ae_restrict_mem hK).mono fun z hz => ?_) p).trans (mul_le_mul_right le_add_self _)
  exact (ContinuousLinearMap.opNNNorm_comp_le _ _).trans (by gcongr; exact hC z hz)

/-- **Continuity of composition with a `C¹` map in `W^{1,p}`.** Let `g` be `C¹` on an open set `W`
and let `K` be compact. Let `u` satisfy `u(K) ⊆ W` and have finite `W^{1,p}(K)` size, and let `uₙ`
be continuous on `K`, converge to `u` uniformly on `K`, and satisfy
`‖uₙ - u‖_{W^{1,p}(K)} → 0`. Then `‖g ∘ uₙ - g ∘ u‖_{W^{1,p}(K)} → 0`.

This holds for every exponent `p`, including `p < 1` and `p = ∞`. -/
theorem tendsto_eLpNormWkp_one_comp_sub {ι : Type*} {l : Filter ι} {u : ι → ℂ → F}
    {u₀ : ℂ → F} {g : F → G} {W : Set F} (hK : IsCompact K) (hW : IsOpen W)
    (hg : ContDiffOn ℝ 1 g W) (hu₀ : eLpNormWkp p K 1 u₀ ≠ ∞) (hu₀W : MapsTo u₀ K W)
    (huc : ∀ᶠ n in l, ContinuousOn (u n) K) (hunif : TendstoUniformlyOn u u₀ l K)
    (hlim : Tendsto (fun n => eLpNormWkp p K 1 (u n - u₀)) l (𝓝 0)) :
    Tendsto (fun n => eLpNormWkp p K 1 (g ∘ u n - g ∘ u₀)) l (𝓝 0) := by
  rcases l.eq_or_neBot with rfl | _
  · exact tendsto_bot
  -- The uniform limit `u₀` is continuous on `K`.
  have hu₀c : ContinuousOn u₀ K := hunif.continuousOn huc.frequently
  have hKm := hK.measurableSet
  have hDgc : ContinuousOn (fderiv ℝ g) W := hg.continuousOn_fderiv_of_isOpen hW le_rfl
  have hcpt : IsCompact (u₀ '' K) := hK.image_of_continuousOn hu₀c
  have hu₀KW : u₀ '' K ⊆ W := image_subset_iff.2 hu₀W
  have hmaps := hunif.eventually_mapsTo (mapsTo_image u₀ K) hcpt (hW.mem_nhdsSet.2 hu₀KW)
  -- `g ∘ u n` and `Dg ∘ u n` converge uniformly on `K`.
  have hgu := hcpt.comp_tendstoUniformlyOn
    (fun y hy => hg.continuousOn.continuousAt (hW.mem_nhds (hu₀KW hy))) hunif
  have hDgu := hcpt.comp_tendstoUniformlyOn
    (fun y hy => hDgc.continuousAt (hW.mem_nhds (hu₀KW hy))) hunif
  -- `Dg ∘ u n` is eventually bounded on `K`.
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hDgc.comp hu₀c hu₀W)
  have hbound : ∀ᶠ n in l, ∀ z ∈ K, ‖fderiv ℝ g (u n z)‖₊ ≤ M.toNNReal + 1 := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hDgu 1 one_pos] with n hn z hz
    rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_add, NNReal.coe_one]
    have h1 : dist (fderiv ℝ g (u n z)) (fderiv ℝ g (u₀ z)) ≤ 1 := by
      rw [dist_comm]; exact (hn z hz).le
    exact (norm_le_norm_add_const_of_dist_le h1).trans
      (by gcongr; exact (hM z hz).trans (Real.le_coe_toNNReal M))
  -- A weak derivative of `u₀` with finite `Lᵖ(K)` norm.
  obtain ⟨Du, hDu, hDup⟩ := exists_hasWeakFDerivOn_of_eLpNormWkp_succ_ne_top hu₀
  rw [eLpNormWkp_zero] at hDup
  have key : ∀ᶠ n in l, eLpNormWkp p K 1 (g ∘ u n - g ∘ u₀) ≤
      eLpNorm (g ∘ u n - g ∘ u₀) p (volume.restrict K) +
        ENNReal.LpAddConst p *
          eLpNorm (fun z => (fderiv ℝ g (u n z) - fderiv ℝ g (u₀ z)).comp (Du z))
            p (volume.restrict K) +
        ENNReal.LpAddConst p * (M.toNNReal + 1 : ℝ≥0) * eLpNormWkp p K 1 (u n - u₀) := by
    filter_upwards [huc, hmaps, hbound] with n hnc hnW hnC
    exact eLpNormWkp_one_comp_sub_le hKm hW hg hnc hnW hu₀c hu₀W hDu
      (fun h => absurd h (by positivity)) hnC
  -- The three terms tend to `0`.
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have h1 : Tendsto (fun n => eLpNorm (g ∘ u n - g ∘ u₀) p (volume.restrict K)) l (𝓝 0) := by
    refine tendsto_eLpNorm_zero_of_eventually_ae_le ?_ fun ε hε => ?_
    · filter_upwards [huc, hmaps] with n hnc hnW
      exact ((hg.continuousOn.comp hnc hnW).sub
        (hg.continuousOn.comp hu₀c hu₀W)).aestronglyMeasurable hKm
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hgu ε hε] with n hn
    filter_upwards [ae_restrict_mem hKm] with z hz
    rw [eNorm_le_coe, ← NNReal.coe_le_coe, coe_nnNorm, Pi.sub_apply, Function.comp_apply,
      Function.comp_apply, ← dist_eq_norm, dist_comm]
    exact (hn z hz).le
  have h2 : Tendsto (fun n => eLpNorm (fun z => (fderiv ℝ g (u n z) - fderiv ℝ g (u₀ z)).comp
      (Du z)) p (volume.restrict K)) l (𝓝 0) := by
    refine tendsto_eLpNorm_zero_of_eventually_le_mul hDup ?_ fun ε hε => ?_
    · filter_upwards [huc, hmaps] with n hnc hnW
      exact (ContinuousLinearMap.compL ℝ ℂ F G).aestronglyMeasurable_comp₂
        (((hDgc.comp hnc hnW).sub (hDgc.comp hu₀c hu₀W)).aestronglyMeasurable hKm)
        (aestronglyMeasurable_of_eLpNorm_ne_top hDup)
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hDgu ε hε] with n hn
    filter_upwards [ae_restrict_mem hKm] with z hz
    rw [eNorm_eq_nnNorm, eNorm_eq_nnNorm, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    refine (ContinuousLinearMap.opNNNorm_comp_le _ _).trans ?_
    gcongr
    rw [← NNReal.coe_le_coe, coe_nnNorm, ← dist_eq_norm, dist_comm]
    exact (hn z hz).le
  have hA := (ENNReal.LpAddConst_lt_top p).ne
  have hsum := (h1.add (ENNReal.Tendsto.const_mul h2 (Or.inr hA))).add
    (ENNReal.Tendsto.const_mul (a := ENNReal.LpAddConst p * (M.toNNReal + 1 : ℝ≥0)) hlim
      (Or.inr (ENNReal.mul_ne_top hA ENNReal.coe_ne_top)))
  simp only [mul_zero, add_zero] at hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (.of_forall fun _ => zero_le) key

/-- **Continuity of composition with a `C¹` map in `W^{1,p}_loc`.** Let `g` be `C¹` on an open set
`W`, and let `u` be in `W^{1,p}_loc(U)` with `u(U) ⊆ W`. Let maps `uₙ` converge to `u` locally
uniformly on `U`, and for every compact `K ⊆ U` let `uₙ` be eventually continuous on `K` with
`‖uₙ - u‖_{W^{1,p}(K)} → 0`. Then `‖g ∘ uₙ - g ∘ u‖_{W^{1,p}(K)} → 0` for every compact
`K ⊆ U`. -/
theorem MemWkpLoc.tendsto_eLpNormWkp_one_comp_sub {ι : Type*} {l : Filter ι} {u : ι → ℂ → F}
    {u₀ : ℂ → F} {g : F → G} {W : Set F} (hu₀ : MemWkpLoc p U 1 u₀)
    (hW : IsOpen W) (hg : ContDiffOn ℝ 1 g W) (hu₀W : MapsTo u₀ U W)
    (huc : ∀ K ⊆ U, IsCompact K → ∀ᶠ n in l, ContinuousOn (u n) K)
    (hunif : TendstoLocallyUniformlyOn u u₀ l U)
    (hlim : ∀ K ⊆ U, IsCompact K → Tendsto (fun n => eLpNormWkp p K 1 (u n - u₀)) l (𝓝 0)) :
    ∀ K ⊆ U, IsCompact K → Tendsto (fun n => eLpNormWkp p K 1 (g ∘ u n - g ∘ u₀)) l (𝓝 0) :=
  fun K hKU hK => TauCeti.tendsto_eLpNormWkp_one_comp_sub hK hW hg
    (hu₀.eLpNormWkp_ne_top_of_isCompact hKU hK) (hu₀W.mono_left hKU)
    (huc K hKU hK)
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1 (hunif.mono hKU))
    (hlim K hKU hK)

/-! ### Checks -/

/-- Translating by constants `cₙ → 0` meets the hypotheses of
`TauCeti.tendsto_eLpNormWkp_one_comp_sub`, so `g ∘ (u + cₙ) → g ∘ u` in `W^{1,p}(K)`. -/
example [CompleteSpace F] {u₀ : ℂ → F} {g : F → G} {W : Set F} {c : ℕ → F} (hK : IsCompact K)
    (hW : IsOpen W) (hg : ContDiffOn ℝ 1 g W) (hu₀ : eLpNormWkp p K 1 u₀ ≠ ∞)
    (hu₀c : ContinuousOn u₀ K) (hu₀W : MapsTo u₀ K W) (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto (fun n => eLpNormWkp p K 1 (g ∘ (u₀ + fun _ => c n) - g ∘ u₀)) atTop (𝓝 0) := by
  refine tendsto_eLpNormWkp_one_comp_sub (u := fun n => u₀ + fun _ => c n) hK hW hg hu₀ hu₀W
    (.of_forall fun _ => hu₀c.add continuousOn_const) ?_ ?_
  · refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
    filter_upwards [Metric.tendsto_nhds.1 hc ε hε] with n hn z _
    simpa [dist_eq_norm] using hn
  · have : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
    have hconst (n : ℕ) : HasWeakFDerivOn volume (Opens.interior K) (fun _ => c n) 0 :=
      hasWeakFDerivOn_iff.2 fun v => by simpa using hasWeakLineDerivOn_const (v := v) (c n)
    have hle (n : ℕ) : eLpNormWkp p K 1 ((u₀ + fun _ => c n) - u₀) ≤
        eLpNorm (fun _ => c n) p (volume.restrict K) := by
      simpa using eLpNormWkp_succ_le (p := p) (k := 0) (hconst n)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le) hle
    refine tendsto_eLpNorm_zero_of_eventually_ae_le
      (.of_forall fun _ => aestronglyMeasurable_const) fun ε hε => ?_
    filter_upwards [Metric.tendsto_nhds.1 hc ε hε] with n hn
    refine .of_forall fun _ => ?_
    rw [eNorm_le_coe, ← NNReal.coe_le_coe, coe_nnNorm]
    simpa [dist_eq_norm] using hn.le

end TauCeti
