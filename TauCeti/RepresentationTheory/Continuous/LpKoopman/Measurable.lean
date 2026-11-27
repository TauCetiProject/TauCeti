/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import TauCeti.RepresentationTheory.Continuous.LpKoopman
public import TauCeti.RepresentationTheory.Continuous.Unitary.Borel
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreserving.Continuous

/-!
# Strong continuity of the pullback representation of a jointly measurable action

Let a topological group `G` that is a Baire space (for instance a locally compact group, or a
Polish group) act on a measurable space `X`, jointly measurably (`MeasurableSMul₂ G X`, for the
Borel σ-algebra of `G`), preserving an s-finite separable measure `μ`
(`MeasureTheory.IsSeparable μ`: countably many measurable sets approximate every set of finite
measure, for instance when the σ-algebra of `X` is countably generated; then `L²(μ)` is
separable). Then for `1 ≤ p < ∞` every orbit `g ↦ π(g) f` of the `Lᵖ` pullback representation
`TauCeti.lpKoopman 𝕜 E p μ hμ` is continuous
(`TauCeti.continuous_lpKoopman_apply_of_measurableSMul₂`). No topology on `X`, no continuity of
the action and no countability of `G` are assumed.

For `p = 2` and a separable Hilbert space `E`
(`TauCeti.continuous_lpKoopman_two_apply_of_measurableSMul₂`): the matrix coefficients are
`⟪π(g) f, h⟫ = ∫ x, ⟪f (g⁻¹ • x), h x⟫ ∂μ` (`TauCeti.inner_lpKoopman_eq_integral`), which are
measurable in `g` by Fubini (`TauCeti.measurable_inner_lpKoopman`). Automatic strong continuity
of measurable unitary representations,
`ContRepresentation.IsUnitary.continuous_apply_of_measurable_inner`, then applies.

Applied to the indicator of a measurable set `A` of finite measure, the `L²` case gives
`μ ((g⁻¹ • ·) ⁻¹' A ∆ (g₀⁻¹ • ·) ⁻¹' A) → 0` as `g → g₀`
(`TauCeti.tendsto_measure_preimage_inv_smul_symmDiff`), and
`MeasureTheory.Lp.continuous_compMeasurePreserving_of_tendsto_measure_symmDiff` turns this into
continuity of every orbit in every `Lᵖ`, `p < ∞`, with values in any normed space.
-/

public section

namespace TauCeti

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal symmDiff

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X]
  {μ : Measure X}

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

/-- For a jointly measurable action preserving an s-finite measure, the matrix coefficients
`g ↦ ⟪π(g) f, h⟫` of the `L²` pullback representation are measurable. -/
theorem measurable_inner_lpKoopman [MeasurableSpace G] [MeasurableInv G] [MeasurableSMul₂ G X]
    [SFinite μ] (f h : Lp E 2 μ) : Measurable fun g ↦ ⟪lpKoopman 𝕜 E 2 μ hμ g f, h⟫_𝕜 := by
  have hF : StronglyMeasurable fun q : G × X ↦ ⟪f (q.1⁻¹ • q.2), h q.2⟫_𝕜 :=
    ((Lp.stronglyMeasurable f).comp_measurable (measurable_fst.inv.smul measurable_snd)).inner
      ((Lp.stronglyMeasurable h).comp_measurable measurable_snd)
  simpa only [inner_lpKoopman_eq_integral] using hF.integral_prod_right'.measurable

/-- **Strong continuity of the `L²` pullback representation of a jointly measurable action.** Let
a Baire topological group `G` act jointly measurably on `X`, preserving an s-finite separable
measure `μ`, and let `E` be a separable Hilbert space. Then every orbit `g ↦ π(g) f` of the
`L²` pullback representation on `L²(X, μ; E)` is continuous. -/
theorem continuous_lpKoopman_two_apply_of_measurableSMul₂ [TopologicalSpace G]
    [IsTopologicalGroup G] [BaireSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableSMul₂ G X]
    [SFinite μ] [IsSeparable μ] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (f : Lp E 2 μ) : Continuous fun g ↦ lpKoopman 𝕜 E 2 μ hμ g f := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩
  refine isUnitary_lpKoopman.continuous_apply_of_measurable_inner (fun ξ η ↦ ?_) f
  simpa only [Function.comp_def, inner_conj_symm] using
    RCLike.continuous_conj.measurable.comp (measurable_inner_lpKoopman (𝕜 := 𝕜) hμ η ξ)

section Lp

variable [TopologicalSpace G] [IsTopologicalGroup G] [BaireSpace G] [MeasurableSpace G]
  [BorelSpace G] [MeasurableSMul₂ G X] [SFinite μ] [IsSeparable μ]

include hμ in
/-- For a jointly measurable action of a Baire topological group preserving an s-finite separable
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
a Baire topological group `G` act jointly measurably on `X`, preserving an s-finite separable
measure `μ`. For `1 ≤ p < ∞` and any normed space `E`, every orbit `g ↦ π(g) f` of the `Lᵖ`
pullback representation on `Lᵖ(X, μ; E)` is continuous. -/
theorem continuous_lpKoopman_apply_of_measurableSMul₂ {𝕜 E : Type*} [NormedRing 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (hp : p ≠ ∞) (f : Lp E p μ) :
    Continuous fun g ↦ lpKoopman 𝕜 E p μ hμ g f :=
  (Lp.continuous_compMeasurePreserving_of_tendsto_measure_symmDiff (fun g ↦ hμ g⁻¹) hp
    (fun _ hs hμs g₀ ↦ tendsto_measure_preimage_inv_smul_symmDiff hμ hs hμs g₀) f).congr
    fun g ↦ (lpKoopman_apply g f).symm

end Lp

end TauCeti
