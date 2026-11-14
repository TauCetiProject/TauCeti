/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.GroupConvolution
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.PeakFunction

/-!
# Approximate identities for `L¹` convolution on a locally compact group

Let `μ` be a regular left Haar measure on a locally compact group `G`, and let
`h ⋆ f = ∫ y, h(y) • L_y f dμ(y)` be the convolution `MeasureTheory.Lp.convolutionL` of an `L¹`
kernel with an `Lᵖ` function. A **kernel concentrating at the identity** is a family `k i` of
nonnegative `L¹` functions of integral one such that for every neighbourhood `U` of `1`, eventually
every `k i` vanishes almost everywhere outside `U`. Such kernels exist: the `L¹` classes of the
nonnegative compactly supported continuous functions of integral one supported in `U`, given by
`TauCeti.exists_nonneg_tsupport_subset_integral_eq_one`.

Convolving with such kernels on the left approximates the identity on `Lᵖ` for `p < ∞`:
`k ⋆ u = ∫ y, k(y) • L_y u dμ(y)`, and `L_y u` tends to `u` as `y → 1` by strong continuity of left
translation, so the peak-function estimates `TauCeti.norm_integral_smul_sub_le` and
`TauCeti.tendsto_integral_smul_of_tendsto` apply. Convolving on the right approximates the identity
on real `L¹`. Since
convolution is not commutative, this is not a formal consequence of the left-hand statement. It
follows from the fact that the modular inversion `(J f)(x) = c(x) • f x⁻¹` of `L¹`, where `c` is
the modular character, reverses convolution:

```text
J (h ⋆ k) = J k ⋆ J h
```

(`MeasureTheory.Lp.modularInversion_convolutionL`). Indeed `J` is an isometry, so
`‖h ⋆ k - h‖₁ = ‖J k ⋆ J h - J h‖₁`, and `J k` is again a nonnegative kernel of integral one
concentrated near `1`. Neither σ-finiteness of `μ` nor any countability of `G` is assumed.

## Main results

* `MeasureTheory.Lp.norm_convolutionL_sub_le`: if `k ≥ 0`, `∫ k = 1`, `k` vanishes outside `S`,
  and `‖L_y u - u‖ ≤ ε` for `y ∈ S`, then `‖k ⋆ u - u‖ ≤ ε`.
* `MeasureTheory.Lp.tendsto_convolutionL_left`: `k i ⋆ u → u` in `Lᵖ` for kernels concentrating at
  the identity, for `1 ≤ p < ∞`.
* `MeasureTheory.Lp.convolutionL_ofRealCLM_compLp_right_eq_integral_smul_rightTranslation_inv`:
  for `h ∈ L¹(G, μ; 𝕜)` (`[RCLike 𝕜]`) and `k ∈ L¹(G, μ; ℝ)`, right convolution with `k` is the
  Bochner integral `∫ z, k z • R_(z⁻¹) h ∂μ` of weighted right translates.
* `MeasureTheory.Lp.tendsto_convolutionL_right`,
  `MeasureTheory.Lp.tendsto_convolutionL_ofRealCLM_compLp_right`: `h ⋆ k i → h` in real and
  `RCLike`-valued `L¹` for nonnegative kernels concentrating at the identity.

## References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016), §2.5.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, proof of Theorem G.3.1.
-/

public section

noncomputable section

open Filter Function MeasureTheory MeasureTheory.Measure Topology TauCeti
open scoped ENNReal

namespace MeasureTheory.Lp

variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {μ : Measure G} [NormedAddCommGroup E] [NormedSpace ℝ E]

section LeftInvariant

variable [μ.IsMulLeftInvariant] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
  [CompleteSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ∞}

omit [CompleteSpace E] in
/-- Convolving on the left with a real `L¹` kernel coerced into an `RCLike` scalar field `𝕜` agrees
with convolving with the real kernel directly. -/
theorem convolutionL_ofRealCLM_compLp_left {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E]
    [IsScalarTower ℝ 𝕜 E] [SMulCommClass ℝ 𝕜 E] (k : Lp ℝ 1 μ) (u : Lp E p μ) :
    convolutionL μ p hp ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).compLp k) u =
      convolutionL μ p hp k u := by
  rw [convolutionL_apply, convolutionL_apply]
  refine integral_congr_ae ?_
  filter_upwards [(RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).coeFn_compLp k] with y hy
  rw [RCLike.ofRealCLM_apply] at hy
  rw [hy, leftTranslation_apply, leftTranslation_apply]
  refine Lp.ext ?_
  filter_upwards [coeFn_smul (k y : 𝕜) (DomMulAct.mk y⁻¹ • u),
    coeFn_smul (k y) (DomMulAct.mk y⁻¹ • u)] with x h₁ h₂
  rw [h₁, h₂, Pi.smul_apply, Pi.smul_apply, ← RCLike.algebraMap_eq_ofReal, algebraMap_smul]

/-- If `k` is a nonnegative kernel of integral one which vanishes outside `S`, and every left
translate `L_y u` with `y ∈ S` lies within `ε` of `u`, then `‖k ⋆ u - u‖_p ≤ ε`. -/
theorem norm_convolutionL_sub_le {k : Lp ℝ 1 μ} (hk : 0 ≤ k) (hk1 : ∫ y, k y ∂μ = 1)
    {S : Set G} (hkS : ∀ᵐ y ∂μ, y ∉ S → k y = 0) {u : Lp E p μ} {ε : ℝ}
    (hu : ∀ y ∈ S, ‖leftTranslation μ p ℝ y u - u‖ ≤ ε) :
    ‖convolutionL μ p hp k u - u‖ ≤ ε := by
  have h := norm_integral_smul_sub_le hk1 hkS
    (integrable_smul_leftTranslation hp (L1.integrable_coeFn k) u).aestronglyMeasurable
    (ae_of_all _ hu)
  rwa [(L1.norm_eq_integral_of_nonneg hk).trans hk1, mul_one, ← convolutionL_apply] at h

/-- **Left approximate identity.** Convolution on the left with nonnegative kernels of integral
one which concentrate at the identity converges strongly to the identity on `Lᵖ`, for
`1 ≤ p < ∞`. -/
theorem tendsto_convolutionL_left {ι : Type*} {l : Filter ι} {k : ι → Lp ℝ 1 μ}
    (hk : ∀ i, 0 ≤ k i) (hk1 : ∀ i, ∫ y, k i y ∂μ = 1)
    (hkl : ∀ U ∈ 𝓝 (1 : G), ∀ᶠ i in l, ∀ᵐ y ∂μ, y ∉ U → k i y = 0) (u : Lp E p μ) :
    Tendsto (fun i => convolutionL μ p hp (k i) u) l (𝓝 u) := by
  have hcont : Tendsto (fun y : G => leftTranslation μ p ℝ y u) (𝓝 1) (𝓝 u) := by
    have h := (continuous_leftTranslation_apply (𝕜 := ℝ) hp u).tendsto 1
    rwa [map_one, LinearIsometryEquiv.coe_one, id_eq] at h
  simp_rw [convolutionL_apply]
  exact tendsto_integral_smul_of_tendsto (C := 1) (.of_forall hk1)
    (.of_forall fun i => ((L1.norm_eq_integral_of_nonneg (hk i)).trans (hk1 i)).le) hkl
    (.of_forall fun i =>
      (integrable_smul_leftTranslation hp (L1.integrable_coeFn (k i)) u).aestronglyMeasurable)
    hcont

end LeftInvariant

section ModularInversion

variable [LocallyCompactSpace G] [μ.IsHaarMeasure] [μ.Regular]

/-- Modular inversion commutes with coercing a real `Lᵖ` function into an `RCLike` field `𝕜`. -/
theorem modularInversion_ofRealCLM_compLp {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (k : Lp ℝ p μ) :
    modularInversion μ p 𝕜 ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).compLp k) =
      (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).compLp (modularInversion μ p ℝ k) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_modularInversion (𝕜 := 𝕜) ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).compLp k),
    (quasiMeasurePreserving_inv_of_regular μ).ae ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).coeFn_compLp k),
    (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).coeFn_compLp (modularInversion μ p ℝ k),
    coeFn_modularInversion (𝕜 := ℝ) k] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄, ← map_smul]

/-- **Right convolution as a Bochner integral of right translates.** For `h ∈ L¹(G, μ; 𝕜)` over an
`RCLike` field `𝕜` and a real kernel `k ∈ L¹(G, μ; ℝ)`, convolving `h` on the right with `k` equals
`∫ z, k z • R_(z⁻¹) h ∂μ`. -/
theorem convolutionL_ofRealCLM_compLp_right_eq_integral_smul_rightTranslation_inv
    {𝕜 : Type*} [RCLike 𝕜] (h : Lp 𝕜 1 μ) (k : Lp ℝ 1 μ) :
    convolutionL μ 1 ENNReal.one_ne_top h ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).compLp k) =
      ∫ z, k z • rightTranslation μ 1 𝕜 z⁻¹ h ∂μ := by
  apply (modularInversion (E := 𝕜) μ 1 𝕜).injective
  have hJ : ⇑(modularInversion (E := 𝕜) μ 1 ℝ) = ⇑(modularInversion (E := 𝕜) μ 1 𝕜) :=
    funext fun u => Lp.ext <| (coeFn_modularInversion (𝕜 := ℝ) u).trans
      (coeFn_modularInversion (𝕜 := 𝕜) u).symm
  have hcomm := (modularInversion (E := 𝕜) μ 1 ℝ).toContinuousLinearEquiv.integral_comp_comm
    (μ := μ) fun z => k z • rightTranslation μ 1 𝕜 z⁻¹ h
  rw [LinearIsometryEquiv.coe_toContinuousLinearEquiv, hJ] at hcomm
  rw [modularInversion_convolutionL, modularInversion_ofRealCLM_compLp,
    convolutionL_ofRealCLM_compLp_left, convolutionL_apply, ← hcomm]
  have hinner (z : G) :
      modularInversion μ 1 𝕜 (k z • rightTranslation μ 1 𝕜 z⁻¹ h) =
        k z • leftTranslation μ 1 ℝ z⁻¹ (modularInversion μ 1 𝕜 h) := by
    have hJz : modularInversion (E := 𝕜) μ 1 𝕜 = (modularInversion (E := 𝕜) μ 1 ℝ : _ → _) :=
      hJ.symm
    rw [congr_fun hJz _, map_smul, ← congr_fun hJz _, rightTranslation_apply,
      modularInversion_modularInversion, leftTranslation_apply, leftTranslation_apply]
  simp_rw [hinner]
  have hinv := integral_inv_eq_integral_modularCharacter_smul_of_regular (μ := μ)
    fun y => k y⁻¹ • leftTranslation μ 1 ℝ y (modularInversion μ 1 𝕜 h)
  simp only [inv_inv] at hinv
  rw [hinv]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_modularInversion (𝕜 := ℝ) k] with y hy
  rw [ENNReal.toReal_one, inv_one, Real.rpow_one, smul_eq_mul] at hy
  rw [hy, smul_smul]

/-- On real `L¹`, right convolution `h ⋆ k` is the Bochner integral `∫ z, k z • R_(z⁻¹) h ∂μ` of
weighted right translates. -/
theorem convolutionL_right_eq_integral_smul_rightTranslation_inv (h k : Lp ℝ 1 μ) :
    convolutionL μ 1 ENNReal.one_ne_top h k = ∫ z, k z • rightTranslation μ 1 ℝ z⁻¹ h ∂μ := by
  have hk : (RCLike.ofRealCLM : ℝ →L[ℝ] ℝ).compLp k = k := by
    refine Lp.ext ?_
    filter_upwards [(RCLike.ofRealCLM : ℝ →L[ℝ] ℝ).coeFn_compLp k] with x hx
    simpa using hx
  simpa only [hk] using
    convolutionL_ofRealCLM_compLp_right_eq_integral_smul_rightTranslation_inv (𝕜 := ℝ) h k

/-- **Right approximate identity over an `RCLike` field.** Convolution on the right with nonnegative
real kernels of integral one which concentrate at the identity converges strongly to the identity on
`L¹(G, μ; 𝕜)`. -/
theorem tendsto_convolutionL_ofRealCLM_compLp_right {𝕜 : Type*} [RCLike 𝕜] {ι : Type*}
    {l : Filter ι} {k : ι → Lp ℝ 1 μ} (hk : ∀ i, 0 ≤ k i) (hk1 : ∀ i, ∫ y, k i y ∂μ = 1)
    (hkl : ∀ U ∈ 𝓝 (1 : G), ∀ᶠ i in l, ∀ᵐ y ∂μ, y ∉ U → k i y = 0) (h : Lp 𝕜 1 μ) :
    Tendsto (fun i =>
      convolutionL μ 1 ENNReal.one_ne_top h ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).compLp (k i)))
      l (𝓝 h) := by
  rw [(modularInversion (E := 𝕜) μ 1 𝕜).toHomeomorph.isInducing.tendsto_nhds_iff]
  simp only [comp_def, LinearIsometryEquiv.coe_toHomeomorph, modularInversion_convolutionL,
    modularInversion_ofRealCLM_compLp, convolutionL_ofRealCLM_compLp_left]
  refine tendsto_convolutionL_left (fun i => by simpa using modularInversion_mono (hk i))
    (fun i => by rw [integral_modularInversion, hk1]) (fun U hU => ?_) _
  filter_upwards [hkl _ (inv_mem_nhds_one G hU)] with i hi
  filter_upwards [coeFn_modularInversion (𝕜 := ℝ) (k i),
    (quasiMeasurePreserving_inv_of_regular μ).ae hi] with x hx hx' hxU
  rw [hx, hx' (by simpa using hxU), smul_zero]

/-- **Right approximate identity.** Convolution on the right with nonnegative kernels of integral
one which concentrate at the identity converges strongly to the identity on real `L¹`. -/
theorem tendsto_convolutionL_right {ι : Type*} {l : Filter ι} {k : ι → Lp ℝ 1 μ}
    (hk : ∀ i, 0 ≤ k i) (hk1 : ∀ i, ∫ y, k i y ∂μ = 1)
    (hkl : ∀ U ∈ 𝓝 (1 : G), ∀ᶠ i in l, ∀ᵐ y ∂μ, y ∉ U → k i y = 0) (h : Lp ℝ 1 μ) :
    Tendsto (fun i => convolutionL μ 1 ENNReal.one_ne_top h (k i)) l (𝓝 h) := by
  have hk_id (i : ι) : (RCLike.ofRealCLM : ℝ →L[ℝ] ℝ).compLp (k i) = k i := by
    refine Lp.ext ?_
    filter_upwards [(RCLike.ofRealCLM : ℝ →L[ℝ] ℝ).coeFn_compLp (k i)] with x hx
    simpa using hx
  simpa only [hk_id] using tendsto_convolutionL_ofRealCLM_compLp_right (𝕜 := ℝ) hk hk1 hkl h

end ModularInversion

end MeasureTheory.Lp
