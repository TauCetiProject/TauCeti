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

1. **Pointwise `star` and the modular involution:** Left translation, right translation, and
   `MeasureTheory.Lp.modularInversion` commute with pointwise `star` on `Lᵖ`. Because pointwise
   `star` on `Lp E p μ` is a continuous ℝ-linear involution (`starL' ℝ`), pushing it through the
   `Lᵖ`-valued Bochner integral defining `Lp.convolutionL` gives
   `star (h ⋆ f) = star h ⋆ star f` (`MeasureTheory.Lp.star_convolutionL`) without any Fubini or
   σ-finiteness assumption. Combining this with `MeasureTheory.Lp.modularInversion_convolutionL`
   shows immediately that the modular involution `f ↦ J (star f)` (`x ↦ c(x) • star (f x⁻¹)`)
   reverses `L¹` convolution (`MeasureTheory.Lp.modularInversion_star_convolutionL`).
2. **Scaling the measure and changing regular Haar normalization:** Under `Lp.smulMeasureₗᵢ`
   (`c • μ` to `μ` for `c : ℝ≥0`, `c ≠ 0`) and `Lp.haarMeasureCongrₗᵢ` (between any two regular
   left Haar measures `μ` and `ν`), left translation, right translation, modular inversion, and
   `Lp.convolutionL` are intertwined equivariantly across all exponents `1 ≤ p < ∞`.

## Main results

* `MeasureTheory.Lp.leftTranslation_star`, `MeasureTheory.Lp.modularInversion_star`,
  `MeasureTheory.Lp.rightTranslation_star`: translations and modular inversion commute with
  pointwise `star`.
* `MeasureTheory.Lp.star_convolutionL`: `star (h ⋆ f) = star h ⋆ star f`.
* `MeasureTheory.Lp.modularInversion_star_convolutionL`: the modular involution `J ∘ star` reverses
  `L¹` convolution, `J (star (h ⋆ k)) = J (star k) ⋆ J (star h)`.
* `MeasureTheory.Lp.smulMeasureₗᵢ_convolutionL`, `MeasureTheory.Lp.haarMeasureCongrₗᵢ_convolutionL`:
  measure rescaling and Haar normalization comparison commute with `Lp.convolutionL`.
-/

public section

noncomputable section

open MeasureTheory.Measure TauCeti
open scoped ENNReal NNReal

namespace MeasureTheory.Lp

/-! ### Translations, modular inversion, and `star` -/

section StarTranslation

variable {G E 𝕜 : Type*} [Group G] [MeasurableSpace G]
  [NormedAddCommGroup E] [StarAddMonoid E] [NormedStarGroup E]
  [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Left translation commutes with pointwise `star` on `Lᵖ`. -/
theorem leftTranslation_star [MeasurableMul G] {μ : Measure G} [μ.IsMulLeftInvariant]
    (g : G) (f : Lp E p μ) :
    leftTranslation μ p 𝕜 g (star f) = star (leftTranslation μ p 𝕜 g f) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_leftTranslation (𝕜 := 𝕜) g (star f),
    (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae (coeFn_star f),
    coeFn_star (leftTranslation μ p 𝕜 g f),
    coeFn_leftTranslation (𝕜 := 𝕜) g f] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, Pi.star_apply, h₃, Pi.star_apply, h₄]

section RegularHaar

variable [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular]
  [NormedSpace ℝ E] [StarModule ℝ E] [SMulCommClass ℝ 𝕜 E]

/-- Modular inversion commutes with pointwise `star` on `Lᵖ`. -/
theorem modularInversion_star (f : Lp E p μ) :
    modularInversion μ p 𝕜 (star f) = star (modularInversion μ p 𝕜 f) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_modularInversion (𝕜 := 𝕜) (star f),
    (quasiMeasurePreserving_inv_of_regular μ).ae (coeFn_star f),
    coeFn_star (modularInversion μ p 𝕜 f),
    coeFn_modularInversion (𝕜 := 𝕜) f] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, Pi.star_apply, h₃, Pi.star_apply, h₄, star_smul, star_trivial (_ : ℝ)]

/-- Right translation commutes with pointwise `star` on `Lᵖ`. -/
theorem rightTranslation_star (g : G) (f : Lp E p μ) :
    rightTranslation μ p 𝕜 g (star f) = star (rightTranslation μ p 𝕜 g f) := by
  rw [rightTranslation_apply, rightTranslation_apply, modularInversion_star, leftTranslation_star,
    modularInversion_star]

end RegularHaar

end StarTranslation

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

/-! ### Measure rescaling and Haar normalization comparison for translations and convolution -/

section SMulMeasure

variable {G E 𝕜 : Type*} [Group G] [MeasurableSpace G] {μ : Measure G}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

section LeftTranslation

variable [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [SMulCommClass ℝ 𝕜 E]

omit [NormedSpace ℝ E] [SMulCommClass ℝ 𝕜 E] in
/-- Transporting along an equality of measures commutes with left translation on `Lᵖ`. -/
theorem castLpₗᵢ_leftTranslation [MeasurableMul G] {ν : Measure G} [μ.IsMulLeftInvariant]
    [ν.IsMulLeftInvariant] (heq : μ = ν) (g : G) (f : Lp E p μ) :
    castLpₗᵢ (𝕜 := 𝕜) heq (leftTranslation μ p 𝕜 g f) =
      leftTranslation ν p 𝕜 g (castLpₗᵢ (𝕜 := 𝕜) heq f) := by
  subst heq
  simp

/-- `Lp.smulMeasureₗᵢ` commutes with left translation on `Lᵖ`. -/
theorem smulMeasureₗᵢ_leftTranslation [MeasurableMul G] [μ.IsMulLeftInvariant]
    {c : ℝ≥0} (hc : c ≠ 0) (g : G) (f : Lp E p (c • μ)) :
    smulMeasureₗᵢ μ p 𝕜 hc (leftTranslation (c • μ) p 𝕜 g f) =
      leftTranslation μ p 𝕜 g (smulMeasureₗᵢ μ p 𝕜 hc f) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_smulMeasureₗᵢ (p := p) (𝕜 := 𝕜) hc (leftTranslation (c • μ) p 𝕜 g f),
    (Measure.ae_smul_measure_iff hc).1 (coeFn_leftTranslation (𝕜 := 𝕜) g f),
    coeFn_leftTranslation (𝕜 := 𝕜) g (smulMeasureₗᵢ μ p 𝕜 hc f),
    (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae
      (coeFn_smulMeasureₗᵢ (p := p) (𝕜 := 𝕜) hc f)] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]

end LeftTranslation

section Convolution

variable [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [μ.IsMulLeftInvariant] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
  [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [NormedSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E]
  [SMulCommClass ℝ 𝕜 E] {hp : p ≠ ∞}

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

end Convolution

end SMulMeasure

section HaarNormalization

variable {G E 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ ν : Measure G} [μ.IsHaarMeasure] [μ.Regular] [ν.IsHaarMeasure] [ν.Regular]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

section NormedRing

variable [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [SMulCommClass ℝ 𝕜 E]

/-- `Lp.haarMeasureCongrₗᵢ` commutes with left translation on `Lᵖ`. -/
theorem haarMeasureCongrₗᵢ_leftTranslation (g : G) (f : Lp E p μ) :
    haarMeasureCongrₗᵢ μ ν p 𝕜 (leftTranslation μ p 𝕜 g f) =
      leftTranslation ν p 𝕜 g (haarMeasureCongrₗᵢ μ ν p 𝕜 f) := by
  simp only [haarMeasureCongrₗᵢ_def, LinearIsometryEquiv.trans_apply, castLpₗᵢ_leftTranslation,
    smulMeasureₗᵢ_leftTranslation]

/-- `Lp.haarMeasureCongrₗᵢ` commutes with `Lp.modularInversion`. -/
theorem haarMeasureCongrₗᵢ_modularInversion (f : Lp E p μ) :
    haarMeasureCongrₗᵢ μ ν p 𝕜 (modularInversion μ p 𝕜 f) =
      modularInversion ν p 𝕜 (haarMeasureCongrₗᵢ μ ν p 𝕜 f) := by
  have hνμ : ν ≪ μ := by
    rw [Measure.isMulLeftInvariant_eq_smul_of_regular ν μ]
    exact Measure.smul_absolutelyContinuous
  refine Lp.ext ?_
  filter_upwards [coeFn_haarMeasureCongrₗᵢ (μ := μ) (ν := ν) (p := p) (𝕜 := 𝕜)
      (modularInversion μ p 𝕜 f),
    hνμ.ae_eq (coeFn_modularInversion (𝕜 := 𝕜) f),
    coeFn_modularInversion (𝕜 := 𝕜) (haarMeasureCongrₗᵢ μ ν p 𝕜 f),
    (quasiMeasurePreserving_inv_of_regular ν).ae
      (coeFn_haarMeasureCongrₗᵢ (μ := μ) (ν := ν) (p := p) (𝕜 := 𝕜) f)] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄, smul_comm]

/-- `Lp.haarMeasureCongrₗᵢ` commutes with right translation on `Lᵖ`. -/
theorem haarMeasureCongrₗᵢ_rightTranslation (g : G) (f : Lp E p μ) :
    haarMeasureCongrₗᵢ μ ν p 𝕜 (rightTranslation μ p 𝕜 g f) =
      rightTranslation ν p 𝕜 g (haarMeasureCongrₗᵢ μ ν p 𝕜 f) := by
  rw [rightTranslation_apply, rightTranslation_apply, haarMeasureCongrₗᵢ_modularInversion,
    haarMeasureCongrₗᵢ_leftTranslation, haarMeasureCongrₗᵢ_modularInversion]

end NormedRing

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [NormedSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E]
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

end NontriviallyNormedField

end HaarNormalization

end MeasureTheory.Lp
