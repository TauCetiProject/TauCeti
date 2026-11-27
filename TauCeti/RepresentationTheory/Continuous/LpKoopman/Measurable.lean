/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import TauCeti.RepresentationTheory.Continuous.LpKoopman
public import TauCeti.RepresentationTheory.Continuous.Unitary.Measurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Strong continuity of the pullback representation of a jointly measurable action

Let a locally compact group `G` act on a measurable space `X`, jointly measurably
(`MeasurableSMul₂ G X`, for the Borel σ-algebra of `G`), preserving an s-finite separable
measure `μ` (`MeasureTheory.IsSeparable μ`: countably many measurable sets approximate every
set of finite measure, for instance when the σ-algebra of `X` is countably generated; then
`L²(μ)` is separable). Then for `1 ≤ p < ∞` every orbit `g ↦ π(g) f` of the `Lᵖ` pullback
representation `TauCeti.lpKoopman 𝕜 E p μ hμ` is continuous
(`TauCeti.continuous_lpKoopman_apply_of_measurableSMul₂`). No topology on `X`, no continuity of
the action and no countability of `G` are assumed.

For `p = 2` and a separable Hilbert space `E`
(`TauCeti.continuous_lpKoopman_two_apply_of_measurableSMul₂`): the matrix coefficients are
`⟪π(g) f, h⟫ = ∫ x, ⟪f (g⁻¹ • x), h x⟫ ∂μ` (`TauCeti.inner_lpKoopman_eq_integral`). The map
`(g, x) ↦ g⁻¹ • x` is quasi measure preserving from `ρ × μ` to `μ` for every measure `ρ` on `G`
(`TauCeti.quasiMeasurePreserving_inv_smul_prod`), so by Fubini every matrix coefficient is almost
everywhere strongly measurable on compact sets of `G`; being bounded, it is locally integrable
(`TauCeti.locallyIntegrable_inner_lpKoopman`). The continuity criterion
`ContRepresentation.IsUnitary.continuous_apply_of_locallyIntegrable_inner` then applies with the
Haar measure `MeasureTheory.Measure.haar`.

Applied to the indicator of a measurable set `A` of finite measure, the `L²` case gives
`μ ((g⁻¹ • ·) ⁻¹' A ∆ (g₀⁻¹ • ·) ⁻¹' A) → 0` as `g → g₀`
(`TauCeti.tendsto_measure_preimage_inv_smul_symmDiff`). Since
`‖1_B c - 1_A c‖_p = ‖c‖ μ (B ∆ A) ^ (1 / p)`, this gives continuity of the orbits of indicators
in every `Lᵖ`, `p < ∞`, with values in any normed space, and density of simple functions gives
every orbit, as in the proof of Mathlib's `MeasureTheory.Lp.compMeasurePreserving_continuous`.

This is the strong continuity target of ClassicalErgodicTheory §0.2, for s-finite separable
measures.
-/

public section

namespace TauCeti

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal symmDiff

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X]
  {μ : Measure X}

/-- If every `x ↦ g • x` preserves `μ`, then `(g, x) ↦ g⁻¹ • x` is quasi measure preserving from
`ρ × μ` to `μ`, for any measure `ρ` on `G`. -/
theorem quasiMeasurePreserving_inv_smul_prod [MeasurableSpace G] [MeasurableInv G]
    [MeasurableSMul₂ G X] [SFinite μ]
    (hμ : ∀ g : G, MeasurePreserving (g • ·) μ μ) (ρ : Measure G) :
    QuasiMeasurePreserving (fun q : G × X ↦ q.1⁻¹ • q.2) (ρ.prod μ) μ := by
  have hm : Measurable fun q : G × X ↦ q.1⁻¹ • q.2 := measurable_fst.inv.smul measurable_snd
  refine ⟨hm.aemeasurable, Measure.AbsolutelyContinuous.mk fun s hs hs0 ↦ ?_⟩
  rw [Measure.map_apply hm hs, Measure.prod_apply (hm hs)]
  have hzero (g : G) : μ (Prod.mk g ⁻¹' ((fun q : G × X ↦ q.1⁻¹ • q.2) ⁻¹' s)) = 0 := by
    change μ ((g⁻¹ • ·) ⁻¹' s) = 0
    rw [(hμ g⁻¹).measure_preimage hs.nullMeasurableSet, hs0]
  simp only [hzero, MeasureTheory.lintegral_zero]

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  (hμ : ∀ g : G, MeasurePreserving (g • ·) μ μ)

/-- The matrix coefficients of the `L²` pullback representation:
`⟪π(g) f, h⟫ = ∫ x, ⟪f (g⁻¹ • x), h x⟫ ∂μ`. -/
theorem inner_lpKoopman_eq_integral (g : G) (f h : Lp E 2 μ) :
    ⟪lpKoopman 𝕜 E 2 μ hμ g f, h⟫_𝕜 = ∫ x, ⟪f (g⁻¹ • x), h x⟫_𝕜 ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_lpKoopman (𝕜 := 𝕜) (hμ := hμ) g f] with x hx
  rw [hx]

/-- For a jointly measurable action of a locally compact group preserving an s-finite measure, the
matrix coefficients `g ↦ ⟪π(g) f, h⟫` of the `L²` pullback representation are locally integrable
for every measure on `G` that is finite on compact sets. -/
theorem locallyIntegrable_inner_lpKoopman [TopologicalSpace G] [LocallyCompactSpace G]
    [MeasurableSpace G] [MeasurableInv G] [MeasurableSMul₂ G X] [SFinite μ] (ν : Measure G)
    [IsFiniteMeasureOnCompacts ν] (f h : Lp E 2 μ) :
    LocallyIntegrable (fun g ↦ ⟪lpKoopman 𝕜 E 2 μ hμ g f, h⟫_𝕜) ν := by
  rw [locallyIntegrable_iff]
  intro K hK
  have : IsFiniteMeasure (ν.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  refine Integrable.of_bound ?_ (‖f‖ * ‖h‖) (Eventually.of_forall fun g ↦ ?_)
  · have hF : AEStronglyMeasurable (fun q : G × X ↦ ⟪f (q.1⁻¹ • q.2), h q.2⟫_𝕜)
        ((ν.restrict K).prod μ) :=
      ((Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving
        (quasiMeasurePreserving_inv_smul_prod hμ _)).inner (Lp.aestronglyMeasurable h).comp_snd
    simpa only [inner_lpKoopman_eq_integral] using hF.integral_prod_right'
  · exact (norm_inner_le_norm _ _).trans_eq (by rw [norm_lpKoopman_apply])

/-- **Strong continuity of the `L²` pullback representation of a jointly measurable action.** Let
a locally compact group `G` act jointly measurably on `X`, preserving an s-finite separable measure
`μ`, and let `E` be a separable Hilbert space. Then every orbit `g ↦ π(g) f` of the
`L²` pullback representation on `L²(X, μ; E)` is continuous. -/
theorem continuous_lpKoopman_two_apply_of_measurableSMul₂ [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableSMul₂ G X]
    [SFinite μ] [IsSeparable μ] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (f : Lp E 2 μ) : Continuous fun g ↦ lpKoopman 𝕜 E 2 μ hμ g f := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩
  exact isUnitary_lpKoopman.continuous_apply_of_locallyIntegrable_inner Measure.haar
    (fun f h ↦ locallyIntegrable_inner_lpKoopman hμ Measure.haar f h) f

section Lp

variable [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G]
  [BorelSpace G] [MeasurableSMul₂ G X] [SFinite μ] [IsSeparable μ]

include hμ in
/-- For a jointly measurable action of a locally compact group preserving an s-finite separable
measure `μ`, the measure of the symmetric difference of the translates `(g⁻¹ • ·) ⁻¹' A` and
`(g₀⁻¹ • ·) ⁻¹' A` of a measurable set `A` of finite measure tends to `0` as `g → g₀`. -/
theorem tendsto_measure_preimage_inv_smul_symmDiff {A : Set X} (hA : MeasurableSet A)
    (hμA : μ A ≠ ∞) (g₀ : G) :
    Tendsto (fun g : G ↦ μ (((g⁻¹ • ·) ⁻¹' A) ∆ ((g₀⁻¹ • ·) ⁻¹' A))) (𝓝 g₀) (𝓝 0) := by
  have hfin (g : G) : μ ((g⁻¹ • ·) ⁻¹' A) ≠ ∞ := by
    rwa [(hμ g⁻¹).measure_preimage hA.nullMeasurableSet]
  have hsd (g : G) : μ (((g⁻¹ • ·) ⁻¹' A) ∆ ((g₀⁻¹ • ·) ⁻¹' A)) ≠ ∞ :=
    ((measure_mono Set.symmDiff_subset_union).trans_lt
      (measure_union_lt_top (hfin g).lt_top (hfin g₀).lt_top)).ne
  have hcont := continuous_lpKoopman_two_apply_of_measurableSMul₂ (𝕜 := ℝ) (E := ℝ) hμ
    (indicatorConstLp 2 hA hμA (1 : ℝ))
  have hdist := (tendsto_iff_dist_tendsto_zero.1 (hcont.tendsto g₀))
  have hdist' : Tendsto (fun g : G ↦
      μ.real (((g⁻¹ • ·) ⁻¹' A) ∆ ((g₀⁻¹ • ·) ⁻¹' A)) ^ (1 / (2 : ℝ≥0∞).toReal)) (𝓝 g₀)
      (𝓝 0) := by
    refine hdist.congr fun g ↦ ?_
    rw [lpKoopman_apply, lpKoopman_apply, Lp.indicatorConstLp_compMeasurePreserving,
      Lp.indicatorConstLp_compMeasurePreserving, dist_indicatorConstLp_eq_norm,
      norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, norm_one, one_mul]
  have hsq := hdist'.rpow_const (p := 2) (Or.inr zero_le_two)
  rw [Real.zero_rpow two_ne_zero] at hsq
  rw [← ENNReal.tendsto_toReal_iff hsd ENNReal.zero_ne_top, ENNReal.toReal_zero]
  refine hsq.congr fun g ↦ ?_
  rw [← Real.rpow_mul measureReal_nonneg]
  norm_num [measureReal_def]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Strong continuity of the `Lᵖ` pullback representation of a jointly measurable action.** Let
a locally compact group `G` act jointly measurably on `X`, preserving an s-finite separable measure
`μ`. For `1 ≤ p < ∞` and any normed space `E`, every orbit `g ↦ π(g) f` of the `Lᵖ`
pullback representation on `Lᵖ(X, μ; E)` is continuous. The density argument follows the proof of
Mathlib's `MeasureTheory.Lp.compMeasurePreserving_continuous`. -/
theorem continuous_lpKoopman_apply_of_measurableSMul₂ {𝕜 E : Type*} [NormedRing 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (hp : p ≠ ∞) (f : Lp E p μ) :
    Continuous fun g ↦ lpKoopman 𝕜 E p μ hμ g f := by
  have hp₀ : p ≠ 0 := (one_pos.trans_le Fact.out).ne'
  have H : Continuous fun fg : Lp E p μ × G ↦
      Lp.compMeasurePreserving (fg.2⁻¹ • ·) (hμ fg.2⁻¹) fg.1 := by
    refine continuous_prod_of_dense_continuous_lipschitzWith _ 1 (Lp.simpleFunc.dense hp) ?_
      fun g ↦ (Lp.isometry_compMeasurePreserving (hμ g⁻¹)).lipschitzWith
    intro f hf
    lift f to Lp.simpleFunc E p μ using hf
    induction f using Lp.simpleFunc.induction hp₀ hp with
    | add hfp hgp _ ihf ihg => exact ihf.add ihg
    | @indicatorConst c s hs hμs =>
      dsimp only [Lp.simpleFunc.coe_indicatorConst, Lp.indicatorConstLp_compMeasurePreserving]
      exact continuous_indicatorConstLp_set hp fun g₀ ↦
        tendsto_measure_preimage_inv_smul_symmDiff hμ hs hμs.ne g₀
  refine (H.comp ((continuous_const (y := f)).prodMk continuous_id)).congr fun g ↦ ?_
  exact (lpKoopman_apply g f).symm

end Lp

end TauCeti
