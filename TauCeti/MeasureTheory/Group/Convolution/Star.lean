/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.GroupConvolution
public import TauCeti.MeasureTheory.Function.Lp.SMulMeasure

/-!
# Pointwise `star`, modular involution, and measure rescaling for `L¹`–`Lᵖ` group convolution

This file records how the operator group convolution `MeasureTheory.Lp.convolutionL` interacts with
two operations on `Lᵖ(G, μ)`:

1. **Pointwise `star` and the modular involution:** Because pointwise `star` on `Lp E p μ` is a
   continuous ℝ-linear involution (`starL' ℝ`) commuting with left translation
   (`MeasureTheory.Lp.leftTranslation_star`), pushing it through the `Lᵖ`-valued Bochner integral
   defining `Lp.convolutionL` gives `star (h ⋆ f) = star h ⋆ star f`
   (`MeasureTheory.Lp.star_convolutionL`) without any Fubini or σ-finiteness assumption. Combining
   this with `MeasureTheory.Lp.modularInversion_convolutionL` shows immediately that the modular
   involution `f ↦ J (star f)` (`x ↦ c(x) • star (f x⁻¹)`) reverses `L¹` convolution
   (`MeasureTheory.Lp.modularInversion_star_convolutionL`).
2. **Scaling the measure and changing regular Haar normalization:** For `1 ≤ p < ∞`, both
   `MeasureTheory.Lp.smulMeasureₗᵢ` (`c • μ` to `μ` for `c : ℝ≥0`, `c ≠ 0`) and
   `MeasureTheory.Lp.haarMeasureCongrₗᵢ` (between any two regular left Haar measures `μ` and `ν`)
   intertwine `MeasureTheory.Lp.convolutionL` equivariantly.

## Main results

* `MeasureTheory.Lp.star_convolutionL`: `star (h ⋆ f) = star h ⋆ star f`.
* `MeasureTheory.Lp.modularInversion_star_convolutionL`: the modular involution `J ∘ star` reverses
  `L¹` convolution, `J (star (h ⋆ k)) = J (star k) ⋆ J (star h)`.
* `MeasureTheory.Lp.smulMeasureₗᵢ_convolutionL`, `MeasureTheory.Lp.castLpₗᵢ_convolutionL`,
  `MeasureTheory.Lp.haarMeasureCongrₗᵢ_convolutionL`: measure rescaling, measure-equality transport,
  and Haar normalization comparison commute with `Lp.convolutionL`.
-/

public section

noncomputable section

open MeasureTheory.Measure TauCeti
open scoped ENNReal NNReal

namespace MeasureTheory.Lp

/-! ### Pointwise `star` and the modular involution on `Lp.convolutionL` -/

section StarConvolution

variable {G E 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G}

/-- **Pointwise `star` distributes over group convolution**: `star (h ⋆ f) = star h ⋆ star f`
for `h ∈ L¹(G, μ; 𝕜)` and `f ∈ Lᵖ(G, μ; E)` (`1 ≤ p < ∞`). -/
theorem star_convolutionL [μ.IsMulLeftInvariant] [IsLocallyFiniteMeasure μ]
    [μ.InnerRegularCompactLTTop] {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ∞}
    [NontriviallyNormedField 𝕜] [StarAddMonoid 𝕜] [NormedStarGroup 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E]
    [StarAddMonoid E] [NormedStarGroup E] [StarModule ℝ E] [StarModule 𝕜 E]
    (h : Lp 𝕜 1 μ) (f : Lp E p μ) :
    star (convolutionL μ p hp h f) = convolutionL μ p hp (star h) (star f) := by
  have hcomm := (starL' ℝ (A := Lp E p μ)).integral_comp_comm
    (μ := μ) fun y ↦ h y • leftTranslation μ p 𝕜 y f
  rw [convolutionL_apply, convolutionL_apply, ← starL'_apply (R := ℝ), ← hcomm]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_star h] with y hy
  rw [starL'_apply, star_smul, ← leftTranslation_star, hy, Pi.star_apply]

/-- **The modular involution reverses `L¹` convolution**:
`J (star (h ⋆ k)) = J (star k) ⋆ J (star h)` for `h, k ∈ L¹(G, μ; 𝕜)` over an `RCLike` field `𝕜`,
where `(J (star f))(x) = c(x) • star (f x⁻¹)`. -/
theorem modularInversion_star_convolutionL [LocallyCompactSpace G] [μ.IsHaarMeasure] [μ.Regular]
    [RCLike 𝕜] (h k : Lp 𝕜 1 μ) :
    modularInversion μ 1 𝕜 (star (convolutionL μ 1 ENNReal.one_ne_top h k)) =
      convolutionL μ 1 ENNReal.one_ne_top
        (modularInversion μ 1 𝕜 (star k)) (modularInversion μ 1 𝕜 (star h)) := by
  rw [star_convolutionL, modularInversion_convolutionL]

end StarConvolution

/-! ### Measure rescaling and Haar normalization comparison for convolution -/

section SMulMeasure

variable {G E 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [μ.IsMulLeftInvariant] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [NormedSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E]
  [SMulCommClass ℝ 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ∞}

/-- **Measure rescaling commutes with `Lp.convolutionL`.** Rescaling the measure from `c • μ` to
`μ` (`c ≠ 0`) intertwines `convolutionL (c • μ) p hp` with `convolutionL μ p hp` across all
exponents `1 ≤ p < ∞`. -/
theorem smulMeasureₗᵢ_convolutionL {c : ℝ≥0} (hc : c ≠ 0)
    (h : Lp 𝕜 1 (c • μ)) (f : Lp E p (c • μ)) :
    smulMeasureₗᵢ μ p 𝕜 hc (convolutionL (c • μ) p hp h f) =
      convolutionL μ p hp (smulMeasureₗᵢ μ 1 𝕜 hc h) (smulMeasureₗᵢ μ p 𝕜 hc f) := by
  have heq_map : ⇑(smulMeasureₗᵢ μ p ℝ hc) = ⇑(smulMeasureₗᵢ μ p 𝕜 (E := E) hc) :=
    funext fun u ↦ Lp.ext <| (coeFn_smulMeasureₗᵢ (𝕜 := ℝ) hc u).trans
      (coeFn_smulMeasureₗᵢ (𝕜 := 𝕜) hc u).symm
  have hcomm := (smulMeasureₗᵢ (E := E) μ p ℝ hc).toContinuousLinearEquiv.integral_comp_comm
    (μ := c • μ) fun y ↦ h y • leftTranslation (c • μ) p 𝕜 y f
  rw [LinearIsometryEquiv.coe_toContinuousLinearEquiv, heq_map] at hcomm
  rw [convolutionL_apply, ← hcomm, integral_smul_nnreal_measure, NNReal.smul_def,
    ← integral_smul, convolutionL_apply]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_smulMeasureₗᵢ_one (𝕜 := 𝕜) hc h] with y hy
  rw [map_smul, smulMeasureₗᵢ_leftTranslation, hy, smul_assoc]

end SMulMeasure

section HaarNormalization

variable {G E 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ ν : Measure G} [μ.IsHaarMeasure] [μ.Regular] [ν.IsHaarMeasure] [ν.Regular]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
  [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [NormedSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E]
  [SMulCommClass ℝ 𝕜 E] {hp : p ≠ ∞}

omit [LocallyCompactSpace G] [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 E] in
/-- Transporting along an equality of measures commutes with `Lp.convolutionL`. -/
theorem castLpₗᵢ_convolutionL {μ' ν' : Measure G} [μ'.IsMulLeftInvariant]
    [IsLocallyFiniteMeasure μ'] [μ'.InnerRegularCompactLTTop] [ν'.IsMulLeftInvariant]
    [IsLocallyFiniteMeasure ν'] [ν'.InnerRegularCompactLTTop] (heq : μ' = ν')
    (h : Lp 𝕜 1 μ') (f : Lp E p μ') :
    castLpₗᵢ (𝕜 := 𝕜) heq (convolutionL μ' p hp h f) =
      convolutionL ν' p hp (castLpₗᵢ (𝕜 := 𝕜) heq h) (castLpₗᵢ (𝕜 := 𝕜) heq f) := by
  subst heq
  simp

/-- **Changing regular left Haar normalization commutes with `Lp.convolutionL`.** For any two
regular left Haar measures `μ` and `ν` on `G` and `1 ≤ p < ∞`, `Lp.haarMeasureCongrₗᵢ` intertwines
`convolutionL μ p hp` with `convolutionL ν p hp`. -/
theorem haarMeasureCongrₗᵢ_convolutionL (h : Lp 𝕜 1 μ) (f : Lp E p μ) :
    haarMeasureCongrₗᵢ μ ν p 𝕜 (convolutionL μ p hp h f) =
      convolutionL ν p hp (haarMeasureCongrₗᵢ μ ν 1 𝕜 h) (haarMeasureCongrₗᵢ μ ν p 𝕜 f) := by
  simp only [haarMeasureCongrₗᵢ_def, LinearIsometryEquiv.trans_apply, castLpₗᵢ_convolutionL,
    smulMeasureₗᵢ_convolutionL]

end HaarNormalization

end MeasureTheory.Lp
