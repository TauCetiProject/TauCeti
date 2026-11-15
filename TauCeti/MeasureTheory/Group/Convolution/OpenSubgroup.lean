/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.GroupConvolution
public import TauCeti.MeasureTheory.Group.Convolution.UCB
public import TauCeti.MeasureTheory.Group.OpenSubgroup.Translation

/-!
# Open-subgroup and coset reduction for group convolutions

On a locally compact group `G` that is not assumed σ-finite, any `L¹` convolution kernel `h` (or any
countable family of `Lᵖ` functions for `p < ∞`) vanishes almost everywhere outside a single
σ-compact open subgroup `H : OpenSubgroup G`
(`MeasureTheory.Lp.exists_openSubgroup_isSigmaCompact_mem_range_extendByZeroComapₗᵢ`). On `H`, the
pullback Haar measure `μ.comap ((↑) : H → G)` *is* σ-finite and inner regular
(`IsSigmaCompact.sigmaFinite_comap`, `OpenSubgroup.innerRegular_comap_of_isSigmaCompact`), so
σ-finite tools such as Tonelli/Fubini apply on `H`.

This file reduces pointwise and operator convolutions on `(G, μ)` to `(H, μ.comap (↑))`, both on `H`
itself and on arbitrary right cosets `H * g`, and proves that the resulting calculations agree with
ambient convolutions and do not depend on the open subgroup chosen:

* **Pointwise convolution integrals:** When `h =ᵐ[μ.restrict Hᶜ] 0` on a measurable subgroup `H`,
  the ambient convolution integral `∫ y, h y • f (y⁻¹ * x) ∂μ` equals the subgroup integral over
  `(H, μ.comap (↑))`, reduces on each right coset `x = u * g` (`u : H`) to subgroup convolution with
  `v ↦ f (v * g)`, and is independent of the subgroup `H` containing the support of `h`.
* **Operator convolution `Lp.convolutionL`:** When the kernel comes from `H` via
  `Lp.extendByZeroComapₗᵢ`, restricting `h ⋆_G f` to `H` gives `h₀ ⋆_H (f|_H)` for any
  `f ∈ Lᵖ(G, μ)` (and on any right coset `H * g` via `Lp.rightTranslation_convolutionL`); when `f`
  also comes from `H`, zero extension commutes with `Lp.convolutionL`, and the result is independent
  of `H`.
* **`L¹`–`L∞` smoothing `Lp.convolutionUCB`:** Combining `Lp.convolutionUCB_rightTranslation_apply`
  with open-subgroup restriction, for a kernel `h₀ ∈ L¹(H, μ.comap (↑))` extended by zero to `G`,
  `(h ⋆_G φ) ((u : G) * g)` equals the subgroup `UCB H` convolution `(h₀ ⋆_H (R_g φ)|_H) u` at every
  `u : H` and `g : G`, agreeing with the ambient convolution and independent of the open subgroup
  containing the support of `h`.

## Main statements

* `MeasureTheory.integral_convolution_eq_comap_of_ae_restrict_compl_eq_zero`,
  `MeasureTheory.integral_convolution_mul_right_eq_comap_of_ae_restrict_compl_eq_zero`,
  `MeasureTheory.integral_convolution_comap_eq_of_ae_restrict_compl_eq_zero`: ambient agreement,
  right-coset reduction, and subgroup independence for pointwise convolution integrals.
* `MeasureTheory.Lp.restrictComapCLM_convolutionL_extendByZeroComapₗᵢ`,
  `MeasureTheory.Lp.extendByZeroComapₗᵢ_convolutionL`,
  `MeasureTheory.Lp.convolutionL_restrictComapCLM_eq_of_ae_restrict_compl_eq_zero`,
  `MeasureTheory.Lp.restrictComapCLM_rightTranslation_convolutionL_extendByZeroComapₗᵢ`:
  open-subgroup and right-coset reduction and subgroup independence for `Lp.convolutionL`.
* `MeasureTheory.Lp.convolutionUCB_extendByZeroComapₗᵢ_coe`,
  `MeasureTheory.Lp.convolutionUCB_extendByZeroComapₗᵢ_mul_right`,
  `MeasureTheory.Lp.convolutionUCB_restrictComapCLM_eq_of_ae_restrict_compl_eq_zero`: open-subgroup
  and right-coset reduction and subgroup independence for `Lp.convolutionUCB`.

## References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016), §§2.4–2.5.
* B. Bekka, P. de la Harpe, and A. Valette, *Kazhdan's Property (T)*, Cambridge University Press
  (2008), proof of Theorem G.3.1.
-/

public section

noncomputable section

open Set
open scoped BoundedContinuousFunction ENNReal

/-! ### Pointwise convolution integrals on measurable subgroups -/

namespace MeasureTheory

section PointwiseConvolution

variable {G 𝕜 E : Type*} [Group G] [MeasurableSpace G] {μ : Measure G}
  [Zero 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [SMulWithZero 𝕜 E]

/-- **Ambient agreement for pointwise convolution integrals.** If `h` vanishes almost everywhere
outside a measurable set or subgroup `H`, the convolution integral `∫ y, h y • f (y⁻¹ * x) ∂μ`
equals the integral over `(H, μ.comap (↑))`. -/
theorem integral_convolution_eq_comap_of_ae_restrict_compl_eq_zero {S : Type*} [SetLike S G]
    {H : S} (hH : MeasurableSet (H : Set G)) {h : G → 𝕜} (hh : h =ᵐ[μ.restrict (H : Set G)ᶜ] 0)
    (f : G → E) (x : G) :
    ∫ y, h y • f (y⁻¹ * x) ∂μ =
      ∫ y : H, h y • f ((y : G)⁻¹ * x) ∂(μ.comap ((↑) : H → G)) := by
  refine (integral_subtype_comap_of_ae_restrict_compl_eq_zero hH ?_).symm
  filter_upwards [hh] with y hy
  simp [hy]

/-- **Right-coset reduction for pointwise convolution integrals.** When `h` vanishes almost
everywhere outside a measurable subgroup `H`, evaluating `∫ y, h y • f (y⁻¹ * x) ∂μ` on a right
coset `x = u * g` (`u : H`) reduces to subgroup convolution on `H` against `v ↦ f (v * g)`. -/
theorem integral_convolution_mul_right_eq_comap_of_ae_restrict_compl_eq_zero {S : Type*}
    [SetLike S G] [SubgroupClass S G] {H : S} (hH : MeasurableSet (H : Set G)) {h : G → 𝕜}
    (hh : h =ᵐ[μ.restrict (H : Set G)ᶜ] 0) (f : G → E) (u : H) (g : G) :
    ∫ y, h y • f (y⁻¹ * ((u : G) * g)) ∂μ =
      ∫ y : H, h y • f ((↑(y⁻¹ * u) : G) * g) ∂(μ.comap ((↑) : H → G)) := by
  rw [integral_convolution_eq_comap_of_ae_restrict_compl_eq_zero hH hh]
  congr 1 with y
  simp [MulMemClass.coe_mul, mul_assoc]

/-- **Subgroup independence for pointwise convolution integrals.** If `h` vanishes almost everywhere
outside each of `H₁` and `H₂`, the subtype convolution integrals over `H₁` and over `H₂` agree at
every `x : G`. -/
theorem integral_convolution_comap_eq_of_ae_restrict_compl_eq_zero {S₁ S₂ : Type*}
    [SetLike S₁ G] [SetLike S₂ G] {H₁ : S₁} {H₂ : S₂}
    (hH₁ : MeasurableSet (H₁ : Set G)) (hH₂ : MeasurableSet (H₂ : Set G)) {h : G → 𝕜}
    (hh₁ : h =ᵐ[μ.restrict (H₁ : Set G)ᶜ] 0) (hh₂ : h =ᵐ[μ.restrict (H₂ : Set G)ᶜ] 0)
    (f : G → E) (x : G) :
    ∫ y : H₁, h y • f ((y : G)⁻¹ * x) ∂(μ.comap ((↑) : H₁ → G)) =
      ∫ y : H₂, h y • f ((y : G)⁻¹ * x) ∂(μ.comap ((↑) : H₂ → G)) :=
  (integral_convolution_eq_comap_of_ae_restrict_compl_eq_zero hH₁ hh₁ f x).symm.trans
    (integral_convolution_eq_comap_of_ae_restrict_compl_eq_zero hH₂ hh₂ f x)

end PointwiseConvolution

end MeasureTheory

/-! ### Open-subgroup and coset reduction for `Lp.convolutionL` -/

namespace MeasureTheory.Lp

section ConvolutionL

variable {G E 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
  [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ∞}
  [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E]

/-- **Open-subgroup reduction of `Lp.convolutionL` for arbitrary `f ∈ Lᵖ(G, μ)`.** When the `L¹`
kernel comes from an open subgroup `H` via `extendByZeroComapₗᵢ`, restricting `h ⋆_G f` to `H`
agrees with convolving `h₀` with `f|_H` on `(H, μ.comap (↑))`. -/
theorem restrictComapCLM_convolutionL_extendByZeroComapₗᵢ [CompleteSpace E] (H : OpenSubgroup G)
    (h₀ : Lp 𝕜 1 (μ.comap ((↑) : H → G))) (f : Lp E p μ) :
    restrictComapCLM 𝕜 μ p H.isOpen.measurableSet
        (convolutionL μ p hp (extendByZeroComapₗᵢ 𝕜 μ H.isOpen.measurableSet h₀) f) =
      convolutionL (μ.comap ((↑) : H → G)) p hp h₀
        (restrictComapCLM 𝕜 μ p H.isOpen.measurableSet f) := by
  have hH : MeasurableSet (H : Set G) := H.isOpen.measurableSet
  set h : Lp 𝕜 1 μ := extendByZeroComapₗᵢ 𝕜 μ hH h₀
  have hscal : ⇑(restrictComapCLM ℝ μ p hH) = ⇑(restrictComapCLM (E := E) 𝕜 μ p hH) :=
    funext (restrictComapCLM_eq_of_scalars 𝕜 hH)
  have hcomm := (restrictComapCLM (E := E) ℝ μ p hH).integral_comp_comm
    (integrable_smul_leftTranslation hp (L1.integrable_coeFn h) f)
  rw [hscal] at hcomm
  rw [convolutionL_apply, ← hcomm, convolutionL_apply]
  have hoff : (fun y ↦ restrictComapCLM 𝕜 μ p hH (h y • leftTranslation μ p 𝕜 y f)) =ᵐ[
      μ.restrict (H : Set G)ᶜ] 0 := by
    filter_upwards [coeFn_extendByZeroComapₗᵢ_restrict_compl (𝕜 := 𝕜) hH h₀] with y hy
    simp [h, hy]
  rw [← integral_subtype_comap_of_ae_restrict_compl_eq_zero hH hoff]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_extendByZeroComapₗᵢ_comp_subtype (𝕜 := 𝕜) hH h₀] with u hu
  simp only [Function.comp_apply] at hu
  rw [map_smul, hu, restrictComapCLM_leftTranslation]

/-- **Extension by zero commutes with `Lp.convolutionL` on an open subgroup.** -/
theorem extendByZeroComapₗᵢ_convolutionL [CompleteSpace E] (H : OpenSubgroup G)
    (h₀ : Lp 𝕜 1 (μ.comap ((↑) : H → G))) (f₀ : Lp E p (μ.comap ((↑) : H → G))) :
    extendByZeroComapₗᵢ 𝕜 μ H.isOpen.measurableSet
        (convolutionL (μ.comap ((↑) : H → G)) p hp h₀ f₀) =
      convolutionL μ p hp (extendByZeroComapₗᵢ 𝕜 μ H.isOpen.measurableSet h₀)
        (extendByZeroComapₗᵢ 𝕜 μ H.isOpen.measurableSet f₀) := by
  have hH : MeasurableSet (H : Set G) := H.isOpen.measurableSet
  set h : Lp 𝕜 1 μ := extendByZeroComapₗᵢ 𝕜 μ hH h₀
  set f : Lp E p μ := extendByZeroComapₗᵢ 𝕜 μ hH f₀
  have hscal : ⇑(extendByZeroComapₗᵢ ℝ μ hH).toContinuousLinearMap =
      ⇑(extendByZeroComapₗᵢ (E := E) (p := p) 𝕜 μ hH) :=
    funext (extendByZeroComapₗᵢ_eq_of_scalars 𝕜 hH)
  have hcomm :=
    (extendByZeroComapₗᵢ (E := E) (p := p) ℝ μ hH).toContinuousLinearMap.integral_comp_comm
      (integrable_smul_leftTranslation hp (L1.integrable_coeFn h₀) f₀)
  rw [hscal] at hcomm
  rw [convolutionL_apply, ← hcomm, convolutionL_apply]
  have hoff : (fun y ↦ h y • leftTranslation μ p 𝕜 y f) =ᵐ[μ.restrict (H : Set G)ᶜ] 0 := by
    filter_upwards [coeFn_extendByZeroComapₗᵢ_restrict_compl (𝕜 := 𝕜) hH h₀] with y hy
    simp [h, hy]
  rw [← integral_subtype_comap_of_ae_restrict_compl_eq_zero hH hoff]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_extendByZeroComapₗᵢ_comp_subtype (𝕜 := 𝕜) hH h₀] with u hu
  simp only [Function.comp_apply] at hu
  rw [map_smul, hu, leftTranslation_extendByZeroComapₗᵢ]

/-- **Subgroup independence of `Lp.convolutionL`.** If `h ∈ L¹(G, μ)` and `f ∈ Lᵖ(G, μ)` vanish
almost everywhere outside each of two open subgroups `H₁` and `H₂`, the zero extensions of their
subgroup convolutions on `H₁` and on `H₂` agree (and both equal `h ⋆_G f`). -/
theorem convolutionL_restrictComapCLM_eq_of_ae_restrict_compl_eq_zero [CompleteSpace E]
    {H₁ H₂ : OpenSubgroup G} {h : Lp 𝕜 1 μ} {f : Lp E p μ}
    (hh₁ : (h : G → 𝕜) =ᵐ[μ.restrict (H₁ : Set G)ᶜ] 0)
    (hh₂ : (h : G → 𝕜) =ᵐ[μ.restrict (H₂ : Set G)ᶜ] 0)
    (hf₁ : (f : G → E) =ᵐ[μ.restrict (H₁ : Set G)ᶜ] 0)
    (hf₂ : (f : G → E) =ᵐ[μ.restrict (H₂ : Set G)ᶜ] 0) :
    extendByZeroComapₗᵢ 𝕜 μ H₁.isOpen.measurableSet
        (convolutionL (μ.comap ((↑) : H₁ → G)) p hp
          (restrictComapCLM 𝕜 μ 1 H₁.isOpen.measurableSet h)
          (restrictComapCLM 𝕜 μ p H₁.isOpen.measurableSet f)) =
      extendByZeroComapₗᵢ 𝕜 μ H₂.isOpen.measurableSet
        (convolutionL (μ.comap ((↑) : H₂ → G)) p hp
          (restrictComapCLM 𝕜 μ 1 H₂.isOpen.measurableSet h)
          (restrictComapCLM 𝕜 μ p H₂.isOpen.measurableSet f)) := by
  rw [extendByZeroComapₗᵢ_convolutionL, extendByZeroComapₗᵢ_convolutionL,
    extendByZeroComapₗᵢ_restrictComapCLM_of_ae_restrict_compl_eq_zero _ hh₁,
    extendByZeroComapₗᵢ_restrictComapCLM_of_ae_restrict_compl_eq_zero _ hf₁,
    extendByZeroComapₗᵢ_restrictComapCLM_of_ae_restrict_compl_eq_zero _ hh₂,
    extendByZeroComapₗᵢ_restrictComapCLM_of_ae_restrict_compl_eq_zero _ hf₂]

end ConvolutionL

section RightTranslationConvolutionL

variable {G E 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [μ.IsHaarMeasure] [μ.Regular] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ∞}
  [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E]

/-- **Right-coset reduction of `Lp.convolutionL`.** For a kernel supported in an open subgroup `H`
and any `f ∈ Lᵖ(G, μ)` and `g : G`, restricting `R_g (h ⋆_G f)` to `H` equals
`h₀ ⋆_H ((R_g f)|_H)`. -/
theorem restrictComapCLM_rightTranslation_convolutionL_extendByZeroComapₗᵢ [CompleteSpace E]
    (H : OpenSubgroup G) (g : G) (h₀ : Lp 𝕜 1 (μ.comap ((↑) : H → G))) (f : Lp E p μ) :
    restrictComapCLM 𝕜 μ p H.isOpen.measurableSet
        (rightTranslation μ p 𝕜 g
          (convolutionL μ p hp (extendByZeroComapₗᵢ 𝕜 μ H.isOpen.measurableSet h₀) f)) =
      convolutionL (μ.comap ((↑) : H → G)) p hp h₀
        (restrictComapCLM 𝕜 μ p H.isOpen.measurableSet (rightTranslation μ p 𝕜 g f)) := by
  rw [rightTranslation_convolutionL, restrictComapCLM_convolutionL_extendByZeroComapₗᵢ]

end RightTranslationConvolutionL

/-! ### Open-subgroup and coset reduction for `Lp.convolutionUCB` -/

section ConvolutionUCB

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [μ.IsHaarMeasure] [μ.Regular]

/-- **Open-subgroup reduction of `Lp.convolutionUCB` on `H`.** When `h₀ ∈ L¹(H, μ.comap (↑))` is
extended by zero to `G`, evaluating `h ⋆_G φ` at `(u : G)` for `u : H` equals evaluating the
subgroup `UCB H` convolution `h₀ ⋆_H (φ|_H)` at `u`. -/
theorem convolutionUCB_extendByZeroComapₗᵢ_coe (H : OpenSubgroup G)
    (h₀ : Lp ℝ 1 (μ.comap ((↑) : H → G))) (φ : Lp ℝ ∞ μ) (u : H) :
    (convolutionUCB (extendByZeroComapₗᵢ ℝ μ H.isOpen.measurableSet h₀) φ : G →ᵇ ℝ) (u : G) =
      (convolutionUCB h₀ (restrictComapCLM ℝ μ ∞ H.isOpen.measurableSet φ) : H →ᵇ ℝ) u := by
  have hH : MeasurableSet (H : Set G) := H.isOpen.measurableSet
  rw [convolutionUCB_apply, convolutionUCB_apply]
  have hred := integral_convolution_eq_comap_of_ae_restrict_compl_eq_zero (𝕜 := ℝ) (E := ℝ) hH
    (coeFn_extendByZeroComapₗᵢ_restrict_compl (𝕜 := ℝ) hH h₀) (⇑φ) (u : G)
  simp only [smul_eq_mul] at hred
  refine hred.trans (integral_congr_ae ?_)
  filter_upwards [coeFn_extendByZeroComapₗᵢ_comp_subtype (𝕜 := ℝ) hH h₀,
    (Measure.quasiMeasurePreserving_inv_mul_of_regular (μ.comap ((↑) : H → G)) u).ae
      (coeFn_restrictComapCLM (𝕜 := ℝ) hH φ)] with y hy hφy
  simp only [Function.comp_apply] at hy hφy
  rw [hy, hφy, MulMemClass.coe_mul, InvMemClass.coe_inv]

/-- **Right-coset reduction of `Lp.convolutionUCB`.** For `h₀ ∈ L¹(H, μ.comap (↑))` extended by
zero to `G`, any `φ ∈ L∞(G, μ)`, `u : H`, and `g : G`, evaluating `h ⋆_G φ` on the right coset
`H * g` at `(u : G) * g` equals evaluating the subgroup `UCB H` convolution
`h₀ ⋆_H ((R_g φ)|_H)` at `u`. -/
theorem convolutionUCB_extendByZeroComapₗᵢ_mul_right (H : OpenSubgroup G)
    (h₀ : Lp ℝ 1 (μ.comap ((↑) : H → G))) (φ : Lp ℝ ∞ μ) (u : H) (g : G) :
    (convolutionUCB (extendByZeroComapₗᵢ ℝ μ H.isOpen.measurableSet h₀) φ : G →ᵇ ℝ)
        ((u : G) * g) =
      (convolutionUCB h₀
        (restrictComapCLM ℝ μ ∞ H.isOpen.measurableSet (rightTranslation μ ∞ ℝ g φ)) :
        H →ᵇ ℝ) u := by
  rw [← convolutionUCB_rightTranslation_apply, convolutionUCB_extendByZeroComapₗᵢ_coe]

/-- **Ambient agreement for `Lp.convolutionUCB` via subgroup right-coset slices.** If `h ∈ L¹(G, μ)`
vanishes almost everywhere outside an open subgroup `H`, then at every `x : G` the ambient
convolution `(h ⋆_G φ) x` equals `(h|_H ⋆_H (R_x φ)|_H) 1`. -/
theorem convolutionUCB_restrictComapCLM_one_eq_of_ae_restrict_compl_eq_zero
    {H : OpenSubgroup G} {h : Lp ℝ 1 μ} (hh : (h : G → ℝ) =ᵐ[μ.restrict (H : Set G)ᶜ] 0)
    (φ : Lp ℝ ∞ μ) (x : G) :
    (convolutionUCB (μ := μ.comap ((↑) : H → G))
        (restrictComapCLM ℝ μ 1 H.isOpen.measurableSet h)
        (restrictComapCLM ℝ μ ∞ H.isOpen.measurableSet (rightTranslation μ ∞ ℝ x φ)) :
        H →ᵇ ℝ) 1 =
      (convolutionUCB h φ : G →ᵇ ℝ) x := by
  have h1 := convolutionUCB_extendByZeroComapₗᵢ_mul_right H
    (restrictComapCLM ℝ μ 1 H.isOpen.measurableSet h) φ 1 x
  rw [extendByZeroComapₗᵢ_restrictComapCLM_of_ae_restrict_compl_eq_zero H.isOpen.measurableSet hh,
    OneMemClass.coe_one, one_mul] at h1
  exact h1.symm

/-- **Subgroup independence for `Lp.convolutionUCB`.** If `h ∈ L¹(G, μ)` vanishes almost everywhere
outside each of two open subgroups `H₁` and `H₂`, the subgroup right-coset formulas on `H₁` and on
`H₂` agree at every `x : G`. -/
theorem convolutionUCB_restrictComapCLM_eq_of_ae_restrict_compl_eq_zero
    {H₁ H₂ : OpenSubgroup G} {h : Lp ℝ 1 μ}
    (hh₁ : (h : G → ℝ) =ᵐ[μ.restrict (H₁ : Set G)ᶜ] 0)
    (hh₂ : (h : G → ℝ) =ᵐ[μ.restrict (H₂ : Set G)ᶜ] 0)
    (φ : Lp ℝ ∞ μ) (x : G) :
    (convolutionUCB (μ := μ.comap ((↑) : H₁ → G))
        (restrictComapCLM ℝ μ 1 H₁.isOpen.measurableSet h)
        (restrictComapCLM ℝ μ ∞ H₁.isOpen.measurableSet (rightTranslation μ ∞ ℝ x φ)) :
        H₁ →ᵇ ℝ) 1 =
      (convolutionUCB (μ := μ.comap ((↑) : H₂ → G))
        (restrictComapCLM ℝ μ 1 H₂.isOpen.measurableSet h)
        (restrictComapCLM ℝ μ ∞ H₂.isOpen.measurableSet (rightTranslation μ ∞ ℝ x φ)) :
        H₂ →ᵇ ℝ) 1 :=
  (convolutionUCB_restrictComapCLM_one_eq_of_ae_restrict_compl_eq_zero hh₁ φ x).trans
    (convolutionUCB_restrictComapCLM_one_eq_of_ae_restrict_compl_eq_zero hh₂ φ x).symm

end ConvolutionUCB

end MeasureTheory.Lp
