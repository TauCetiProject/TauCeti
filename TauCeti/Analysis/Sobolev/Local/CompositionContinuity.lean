/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Norm
import TauCeti.Analysis.Sobolev.WeakDeriv.ChainRule
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp
import Mathlib.Topology.MetricSpace.Thickening
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
* **Continuity of composition.** If `uₙ → u` uniformly on a compact set `K` and
  `‖uₙ - u‖_{W^{1,p}(K)} → 0`, then `‖g ∘ uₙ - g ∘ u‖_{W^{1,p}(K)} → 0`. The weak derivative of the
  difference splits as `(Dg(uₙ) - Dg(u)) ∘ Du + Dg(uₙ) ∘ D(uₙ - u)`. The first term tends to `0`
  because `Dg` is uniformly continuous near the compact set `u(K)` inside `W`, and the second
  because `Dg(uₙ)` is eventually bounded on `K`. Only `ℓ = 1` derivatives of `g` are used.

The uniform convergence hypothesis is not implied by `W^{1,p}` convergence for `p ≤ 2`; for
`p > 2` it follows from Morrey's embedding, and that consequence is not proved here.

## Main declarations

* `TauCeti.eLpNormWkp_one_comp_le`: the `W^{1,p}(K)` bound for `g ∘ u` with explicit constants.
* `TauCeti.exists_eLpNormWkp_one_comp_le`: the same with constants depending only on `g` on a
  compact subset of `W` containing `u(K)`.
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

section Helpers

variable {α E E' : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [NormedAddCommGroup E'] {p : ℝ≥0∞}

/-- If `f i` is eventually bounded by `δ ‖b‖` for every `δ > 0`, and `b` has finite `Lᵖ` norm, then
the `Lᵖ` norm of `f i` tends to `0`. -/
private theorem tendsto_eLpNorm_zero_of_eventually_le_mul {ι : Type*} {l : Filter ι}
    {f : ι → α → E} {b : α → E'} (hb : eLpNorm b p μ ≠ ∞)
    (hf : ∀ᶠ i in l, AEStronglyMeasurable (f i) μ)
    (h : ∀ δ : ℝ≥0, 0 < δ → ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖f i x‖₊ ≤ δ * ‖b x‖₊) :
    Tendsto (fun i => eLpNorm (f i) p μ) l (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt hb hε.ne'
  filter_upwards [hf, h δ hδ] with i hfi hi
  exact (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul hfi hi p).trans hδε.le

end Helpers

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {p : ℝ≥0∞} {U K : Set ℂ}

/-- A finite `W^{1,p}(K)` size supplies a weak derivative on `interior K` of finite `Lᵖ(K)` norm. -/
private theorem exists_hasWeakFDerivOn_of_eLpNormWkp_one_ne_top {f : ℂ → F}
    (h : eLpNormWkp p K 1 f ≠ ∞) : ∃ D : ℂ → ℂ →L[ℝ] F,
      HasWeakFDerivOn volume (Opens.interior K) f D ∧ eLpNorm D p (volume.restrict K) ≠ ∞ := by
  rw [eLpNormWkp_succ (k := 0)] at h
  obtain ⟨D, hD⟩ := iInf_lt_iff.1 (lt_top_iff_ne_top.2 (ENNReal.add_ne_top.1 h).2)
  obtain ⟨hD, hlt⟩ := iInf_lt_iff.1 hD
  exact ⟨D, hD, by simpa using hlt.ne⟩

/-- To bound `‖f‖_{W^{1,p}(K)}` by `a + c ‖h‖_{W^{1,p}(K)}` it suffices to bound it by
`a + c ‖D‖_{Lᵖ(K)}` for every weak derivative `D` of `h` on `interior K` that is almost everywhere
strongly measurable on `K`. -/
private theorem eLpNormWkp_one_le_add_mul {f : ℂ → G} {h : ℂ → F} {a c : ℝ≥0∞} (hc : c ≠ ∞)
    (hh : eLpNormWkp p K 1 h ≠ ∞)
    (H : ∀ D : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior K) h D →
      AEStronglyMeasurable D (volume.restrict K) →
        eLpNormWkp p K 1 f ≤ a + c * eLpNorm D p (volume.restrict K)) :
    eLpNormWkp p K 1 f ≤ a + c * eLpNormWkp p K 1 h := by
  rcases eq_or_ne c 0 with rfl | hc0
  · obtain ⟨D, hD, hDp⟩ := exists_hasWeakFDerivOn_of_eLpNormWkp_one_ne_top hh
    simpa using H D hD (aestronglyMeasurable_of_eLpNorm_ne_top hDp)
  calc eLpNormWkp p K 1 f
      ≤ ⨅ (D : ℂ → ℂ →L[ℝ] F) (_ : HasWeakFDerivOn volume (Opens.interior K) h D),
          a + c * eLpNormWkp p K 0 D :=
        le_iInf₂ fun D hD => by
          rw [eLpNormWkp_zero]
          by_cases hDm : AEStronglyMeasurable D (volume.restrict K)
          · exact H D hD hDm
          · rw [eLpNorm_of_not_aestronglyMeasurable hDm, ENNReal.mul_top hc0, add_top]
            exact le_top
    _ = a + c * ⨅ (D : ℂ → ℂ →L[ℝ] F) (_ : HasWeakFDerivOn volume (Opens.interior K) h D),
          eLpNormWkp p K 0 D := by
        simp only [ENNReal.mul_iInf_of_ne hc0 hc, ENNReal.add_iInf]
    _ ≤ a + c * eLpNormWkp p K 1 h := by
        rw [eLpNormWkp_succ (k := 0)]
        gcongr
        exact le_add_self

/-- A member of `W^{1,p}_loc(U)` has finite `W^{1,p}(K)` size on every compact `K ⊆ U`. -/
private theorem MemWkpLoc.eLpNormWkp_one_ne_top_of_isCompact {f : ℂ → F}
    (hf : MemWkpLoc p U 1 f) (hKU : K ⊆ U) (hK : IsCompact K) : eLpNormWkp p K 1 f ≠ ∞ := by
  obtain ⟨D, hD, hDp⟩ := hf.exists_weakFDeriv
  refine ((eLpNormWkp_succ_le (hD.mono (interior_mono hKU))).trans_lt ?_).ne
  rw [eLpNormWkp_zero]
  exact ENNReal.add_lt_top.2 ⟨(memLpLoc_iff.1 (memWkpLoc_succ_iff.1 hf).1 K hKU hK).eLpNorm_lt_top,
    (memLpLoc_iff.1 (memWkpLoc_zero_iff.1 hDp) K hKU hK).eLpNorm_lt_top⟩

variable [CompleteSpace G]

/-- **The `W^{1,p}` bound for composition with a `C¹` map.** Let `g` be `C¹` on an open set `W`
and let `u` be continuous on a measurable set `K`, with `u(K) ⊆ W` and finite `W^{1,p}(K)` size.
If `‖g ∘ u‖ ≤ C₀` and `‖Dg ∘ u‖ ≤ C₁` on `K`, then
`‖g ∘ u‖_{W^{1,p}(K)} ≤ C₀ vol(K)^{1/p} + C₁ ‖u‖_{W^{1,p}(K)}`. The weak derivative of `g ∘ u` on
`interior K` is `Dg(u) ∘ Du`, by `TauCeti.HasWeakFDerivOn.contDiffOn_comp`.

The finiteness hypothesis on `u` is needed only when `C₁ = 0`. -/
theorem eLpNormWkp_one_comp_le {u : ℂ → F} {g : F → G} {W : Set F} {C₀ C₁ : ℝ≥0}
    (hK : MeasurableSet K) (hu : eLpNormWkp p K 1 u ≠ ∞) (huc : ContinuousOn u K)
    (hW : IsOpen W) (hg : ContDiffOn ℝ 1 g W) (huW : MapsTo u K W)
    (hC₀ : ∀ z ∈ K, ‖g (u z)‖₊ ≤ C₀) (hC₁ : ∀ z ∈ K, ‖fderiv ℝ g (u z)‖₊ ≤ C₁) :
    eLpNormWkp p K 1 (fun z => g (u z)) ≤
      C₀ * volume K ^ p.toReal⁻¹ + C₁ * eLpNormWkp p K 1 u := by
  refine eLpNormWkp_one_le_add_mul ENNReal.coe_ne_top hu fun D hD hDm => ?_
  refine (eLpNormWkp_succ_le (hD.contDiffOn_comp (huc.mono interior_subset) hW hg
    (huW.mono_left interior_subset))).trans ?_
  rw [eLpNormWkp_zero]
  gcongr ?_ + ?_
  · have := eLpNorm_le_of_ae_nnnorm_bound (p := p) (μ := volume.restrict K)
      ((hg.continuousOn.comp huc huW).aestronglyMeasurable hK)
      ((ae_restrict_mem hK).mono fun z hz => hC₀ z hz)
    simpa [Measure.restrict_apply_univ, ENNReal.smul_def, smul_eq_mul, Function.comp_def] using this
  · refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
      ((ContinuousLinearMap.compL ℝ ℂ F G).aestronglyMeasurable_comp₂
        (((hg.continuousOn_fderiv_of_isOpen hW le_rfl).comp huc huW).aestronglyMeasurable hK) hDm)
      ((ae_restrict_mem hK).mono fun z hz => ?_) p
    exact (ContinuousLinearMap.opNNNorm_comp_le _ _).trans (by gcongr; exact hC₁ z hz)

/-- **A uniform `W^{1,p}` bound for composition with a `C¹` map.** Let `g` be `C¹` on an open set
`W` and let `L ⊆ W` be compact. There are constants `C₀`, `C₁`, depending only on `g` on `L`
(bounds for `‖g‖` and `‖Dg‖` there), such that
`‖g ∘ u‖_{W^{1,p}(K)} ≤ C₀ vol(K)^{1/p} + C₁ ‖u‖_{W^{1,p}(K)}` for every exponent `p`, every
measurable `K`, and every continuous `u` on `K` with `u(K) ⊆ L` and finite `W^{1,p}(K)` size. -/
theorem exists_eLpNormWkp_one_comp_le {g : F → G} {W L : Set F} (hW : IsOpen W)
    (hg : ContDiffOn ℝ 1 g W) (hL : IsCompact L) (hLW : L ⊆ W) :
    ∃ C₀ C₁ : ℝ≥0, ∀ (p : ℝ≥0∞) (K : Set ℂ) (u : ℂ → F), MeasurableSet K →
      eLpNormWkp p K 1 u ≠ ∞ → ContinuousOn u K → MapsTo u K L →
        eLpNormWkp p K 1 (fun z => g (u z)) ≤
          C₀ * volume K ^ p.toReal⁻¹ + C₁ * eLpNormWkp p K 1 u := by
  obtain ⟨M₀, hM₀⟩ := hL.exists_bound_of_continuousOn (hg.continuousOn.mono hLW)
  obtain ⟨M₁, hM₁⟩ := hL.exists_bound_of_continuousOn
    ((hg.continuousOn_fderiv_of_isOpen hW le_rfl).mono hLW)
  refine ⟨M₀.toNNReal, M₁.toNNReal, fun p K u hK hu huc huL =>
    eLpNormWkp_one_comp_le hK hu huc hW hg (huL.mono_right hLW) (fun z hz => ?_)
      fun z hz => ?_⟩
  · rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact (hM₀ _ (huL hz)).trans (Real.le_coe_toNNReal M₀)
  · rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact (hM₁ _ (huL hz)).trans (Real.le_coe_toNNReal M₁)

/-- **Continuity of composition with a `C¹` map in `W^{1,p}`.** Let `g` be `C¹` on an open set `W`
and let `K` be compact. Let `u` be continuous on `K` with `u(K) ⊆ W` and finite `W^{1,p}(K)` size,
and let `uₙ` be continuous on `K`, converge to `u` uniformly on `K`, and satisfy
`‖uₙ - u‖_{W^{1,p}(K)} → 0`. Then `‖g ∘ uₙ - g ∘ u‖_{W^{1,p}(K)} → 0`.

The weak derivative of `g ∘ uₙ - g ∘ u` on `interior K` is
`(Dg(uₙ) - Dg(u)) ∘ Du + Dg(uₙ) ∘ D(uₙ - u)`. The first term tends to `0` in `Lᵖ(K)` because
`Dg ∘ uₙ → Dg ∘ u` uniformly on `K`, by continuity of `Dg` near the compact set `u(K)`; the second
because `Dg ∘ uₙ` is eventually bounded on `K`. No lower bound on `p` is needed: for `p < 1` the
quasi-triangle inequality with constant `ENNReal.LpAddConst p` replaces the triangle inequality. -/
theorem tendsto_eLpNormWkp_one_comp_sub {ι : Type*} {l : Filter ι} {u : ι → ℂ → F}
    {u₀ : ℂ → F} {g : F → G} {W : Set F} (hK : IsCompact K) (hW : IsOpen W)
    (hg : ContDiffOn ℝ 1 g W) (hu₀ : eLpNormWkp p K 1 u₀ ≠ ∞) (hu₀c : ContinuousOn u₀ K)
    (hu₀W : MapsTo u₀ K W) (huc : ∀ᶠ n in l, ContinuousOn (u n) K)
    (hunif : TendstoUniformlyOn u u₀ l K)
    (hlim : Tendsto (fun n => eLpNormWkp p K 1 (u n - u₀)) l (𝓝 0)) :
    Tendsto (fun n => eLpNormWkp p K 1 (g ∘ u n - g ∘ u₀)) l (𝓝 0) := by
  have hKm := hK.measurableSet
  have hDgc : ContinuousOn (fderiv ℝ g) W := hg.continuousOn_fderiv_of_isOpen hW le_rfl
  have hcpt : IsCompact (u₀ '' K) := hK.image_of_continuousOn hu₀c
  have hu₀KW : u₀ '' K ⊆ W := image_subset_iff.2 hu₀W
  -- Eventually `u n` maps `K` into `W`.
  obtain ⟨δ, hδ, hδW⟩ := hcpt.exists_thickening_subset_open hW hu₀KW
  have hmaps : ∀ᶠ n in l, MapsTo (u n) K W := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif δ hδ] with n hn z hz
    exact hδW (Metric.mem_thickening_iff.2 ⟨u₀ z, mem_image_of_mem _ hz, by
      rw [dist_comm]; exact hn z hz⟩)
  -- `g ∘ u n` and `Dg ∘ u n` converge uniformly on `K`.
  have hgu := hcpt.comp_tendstoUniformlyOn
    (fun y hy => hg.continuousOn.continuousAt (hW.mem_nhds (hu₀KW hy))) hunif
  have hDgu := hcpt.comp_tendstoUniformlyOn
    (fun y hy => hDgc.continuousAt (hW.mem_nhds (hu₀KW hy))) hunif
  -- `Dg ∘ u n` is eventually bounded on `K`.
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hDgc.comp hu₀c hu₀W)
  have hbound : ∀ᶠ n in l, ∀ z ∈ K, ‖fderiv ℝ g (u n z)‖₊ ≤ (M + 1).toNNReal := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hDgu 1 one_pos] with n hn z hz
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    refine le_trans ?_ (Real.le_coe_toNNReal _)
    have h1 := hn z hz
    rw [dist_eq_norm] at h1
    calc ‖fderiv ℝ g (u n z)‖
        ≤ ‖fderiv ℝ g (u₀ z)‖ + ‖fderiv ℝ g (u₀ z) - fderiv ℝ g (u n z)‖ :=
          norm_le_insert _ _
      _ ≤ M + 1 := add_le_add (hM z hz) h1.le
  -- A weak derivative of `u₀` with finite `Lᵖ(K)` norm.
  obtain ⟨Du, hDu, hDup⟩ := exists_hasWeakFDerivOn_of_eLpNormWkp_one_ne_top hu₀
  have hDum := aestronglyMeasurable_of_eLpNorm_ne_top hDup
  have hDu₀ := hDu.contDiffOn_comp (huc := hu₀c.mono interior_subset) hW hg
    (hu₀W.mono_left interior_subset)
  set C : ℝ≥0 := (M + 1).toNNReal
  -- The key estimate.
  have key : ∀ᶠ n in l, eLpNormWkp p K 1 (g ∘ u n - g ∘ u₀) ≤
      eLpNorm (g ∘ u n - g ∘ u₀) p (volume.restrict K) +
        ENNReal.LpAddConst p *
          eLpNorm (fun z => (fderiv ℝ g (u n z) - fderiv ℝ g (u₀ z)).comp (Du z))
            p (volume.restrict K) +
        ENNReal.LpAddConst p * C * eLpNormWkp p K 1 (u n - u₀) := by
    filter_upwards [huc, hmaps, hbound, hlim.eventually (gt_mem_nhds zero_lt_one)]
      with n hnc hnW hnC hfin
    refine eLpNormWkp_one_le_add_mul (ENNReal.mul_ne_top (ENNReal.LpAddConst_lt_top p).ne
      ENNReal.coe_ne_top) hfin.ne_top fun D hD hDm => ?_
    have hDn : HasWeakFDerivOn volume (Opens.interior K) (u n) (D + Du) := by
      simpa using hD.add hDu
    refine (eLpNormWkp_succ_le ((hDn.contDiffOn_comp (hnc.mono interior_subset) hW hg
      (hnW.mono_left interior_subset)).sub hDu₀)).trans ?_
    rw [eLpNormWkp_zero, add_assoc, mul_assoc, ← mul_add]
    refine add_le_add le_rfl ?_
    have hsplit : ((fun z => (fderiv ℝ g (u n z)).comp ((D + Du) z)) -
        fun z => (fderiv ℝ g (u₀ z)).comp (Du z)) =
        (fun z => (fderiv ℝ g (u n z) - fderiv ℝ g (u₀ z)).comp (Du z)) +
          fun z => (fderiv ℝ g (u n z)).comp (D z) := by
      ext1 z
      simp only [Pi.sub_apply, Pi.add_apply, ContinuousLinearMap.comp_add,
        ContinuousLinearMap.sub_comp]
      abel
    rw [hsplit]
    refine (eLpNorm_add_le' p).trans (mul_le_mul' le_rfl (add_le_add le_rfl ?_))
    refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
      ((ContinuousLinearMap.compL ℝ ℂ F G).aestronglyMeasurable_comp₂
        ((hDgc.comp hnc hnW).aestronglyMeasurable hKm) hDm)
      ((ae_restrict_mem hKm).mono fun z hz => ?_) p
    exact (ContinuousLinearMap.opNNNorm_comp_le _ _).trans (by gcongr; exact hnC z hz)
  -- The three terms tend to `0`.
  have h1 : Tendsto (fun n => eLpNorm (g ∘ u n - g ∘ u₀) p (volume.restrict K)) l (𝓝 0) := by
    have : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
    refine tendsto_eLpNorm_zero_of_eventually_le_mul (b := fun _ => (1 : ℝ))
      (memLp_const 1).eLpNorm_ne_top ?_ fun ε hε => ?_
    · filter_upwards [huc, hmaps] with n hnc hnW
      exact ((hg.continuousOn.comp hnc hnW).sub
        (hg.continuousOn.comp hu₀c hu₀W)).aestronglyMeasurable hKm
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hgu ε hε] with n hn
    filter_upwards [ae_restrict_mem hKm] with z hz
    rw [nnnorm_one, mul_one, ← NNReal.coe_le_coe, coe_nnnorm, Pi.sub_apply, Function.comp_apply,
      Function.comp_apply, ← dist_eq_norm, dist_comm]
    exact (hn z hz).le
  have h2 : Tendsto (fun n => eLpNorm (fun z => (fderiv ℝ g (u n z) - fderiv ℝ g (u₀ z)).comp
      (Du z)) p (volume.restrict K)) l (𝓝 0) := by
    refine tendsto_eLpNorm_zero_of_eventually_le_mul hDup ?_ fun ε hε => ?_
    · filter_upwards [huc, hmaps] with n hnc hnW
      exact (ContinuousLinearMap.compL ℝ ℂ F G).aestronglyMeasurable_comp₂
        (((hDgc.comp hnc hnW).sub (hDgc.comp hu₀c hu₀W)).aestronglyMeasurable hKm) hDum
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hDgu ε hε] with n hn
    filter_upwards [ae_restrict_mem hKm] with z hz
    refine (ContinuousLinearMap.opNNNorm_comp_le _ _).trans ?_
    gcongr
    rw [← NNReal.coe_le_coe, coe_nnnorm, ← dist_eq_norm, dist_comm]
    exact (hn z hz).le
  have hA := (ENNReal.LpAddConst_lt_top p).ne
  have hsum := (h1.add (ENNReal.Tendsto.const_mul h2 (Or.inr hA))).add
    (ENNReal.Tendsto.const_mul (a := ENNReal.LpAddConst p * C) hlim
      (Or.inr (ENNReal.mul_ne_top hA ENNReal.coe_ne_top)))
  simp only [mul_zero, add_zero] at hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (.of_forall fun _ => zero_le) key

/-- **Continuity of composition with a `C¹` map in `W^{1,p}_loc`.** Let `g` be `C¹` on an open set
`W`, and let `u` be continuous on `U`, in `W^{1,p}_loc(U)`, with `u(U) ⊆ W`. If continuous maps
`uₙ` converge to `u` locally uniformly on `U`, and `‖uₙ - u‖_{W^{1,p}(K)} → 0` for every compact
`K ⊆ U`, then `‖g ∘ uₙ - g ∘ u‖_{W^{1,p}(K)} → 0` for every compact `K ⊆ U`. This is
`TauCeti.tendsto_eLpNormWkp_one_comp_sub` on each compact subset. -/
theorem MemWkpLoc.tendsto_eLpNormWkp_one_comp_sub {ι : Type*} {l : Filter ι} {u : ι → ℂ → F}
    {u₀ : ℂ → F} {g : F → G} {W : Set F} (hu₀ : MemWkpLoc p U 1 u₀)
    (hu₀c : ContinuousOn u₀ U) (hW : IsOpen W) (hg : ContDiffOn ℝ 1 g W) (hu₀W : MapsTo u₀ U W)
    (huc : ∀ᶠ n in l, ContinuousOn (u n) U) (hunif : TendstoLocallyUniformlyOn u u₀ l U)
    (hlim : ∀ K ⊆ U, IsCompact K → Tendsto (fun n => eLpNormWkp p K 1 (u n - u₀)) l (𝓝 0))
    (hKU : K ⊆ U) (hK : IsCompact K) :
    Tendsto (fun n => eLpNormWkp p K 1 (g ∘ u n - g ∘ u₀)) l (𝓝 0) :=
  TauCeti.tendsto_eLpNormWkp_one_comp_sub hK hW hg (hu₀.eLpNormWkp_one_ne_top_of_isCompact hKU hK)
    (hu₀c.mono hKU) (hu₀W.mono_left hKU) (huc.mono fun _ h => h.mono hKU)
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1 (hunif.mono hKU))
    (hlim K hKU hK)

/-! ### Checks -/

/-- Translating by constants `cₙ → 0` meets the hypotheses of
`TauCeti.tendsto_eLpNormWkp_one_comp_sub`, so `g ∘ (u + cₙ) → g ∘ u` in `W^{1,p}(K)`. -/
example [CompleteSpace F] {u₀ : ℂ → F} {g : F → G} {W : Set F} {c : ℕ → F} (hK : IsCompact K)
    (hW : IsOpen W) (hg : ContDiffOn ℝ 1 g W) (hu₀ : eLpNormWkp p K 1 u₀ ≠ ∞)
    (hu₀c : ContinuousOn u₀ K) (hu₀W : MapsTo u₀ K W) (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto (fun n => eLpNormWkp p K 1 (g ∘ (u₀ + fun _ => c n) - g ∘ u₀)) atTop (𝓝 0) := by
  refine tendsto_eLpNormWkp_one_comp_sub (u := fun n => u₀ + fun _ => c n) hK hW hg hu₀ hu₀c
    hu₀W (.of_forall fun _ => hu₀c.add continuousOn_const) ?_ ?_
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
    refine tendsto_eLpNorm_zero_of_eventually_le_mul (b := fun _ => (1 : ℝ))
      (memLp_const 1).eLpNorm_ne_top (.of_forall fun _ => aestronglyMeasurable_const)
      fun ε hε => ?_
    filter_upwards [Metric.tendsto_nhds.1 hc ε hε] with n hn
    refine .of_forall fun _ => ?_
    rw [nnnorm_one, mul_one, ← NNReal.coe_le_coe, coe_nnnorm]
    simpa [dist_eq_norm] using hn.le

end TauCeti
