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
* `MeasureTheory.Lp.tendsto_convolutionL_right`: `h ⋆ k i → h` in real `L¹` for such kernels.

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

/-- If `k` is a nonnegative kernel of integral one which vanishes outside `S`, and every left
translate `L_y u` with `y ∈ S` lies within `ε` of `u`, then `‖k ⋆ u - u‖_p ≤ ε`. -/
theorem norm_convolutionL_sub_le {k : Lp ℝ 1 μ} (hk : 0 ≤ k) (hk1 : ∫ y, k y ∂μ = 1)
    {S : Set G} (hkS : ∀ᵐ y ∂μ, y ∉ S → k y = 0) {u : Lp E p μ} {ε : ℝ}
    (hu : ∀ y ∈ S, ‖leftTranslation μ p ℝ y u - u‖ ≤ ε) :
    ‖convolutionL μ p hp k u - u‖ ≤ ε := by
  have h := norm_integral_smul_sub_le hk1 hkS
    (integrable_smul_leftTranslation hp (L1.integrable_coeFn k) u).aestronglyMeasurable hu
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

/-- **Right approximate identity.** Convolution on the right with nonnegative kernels of integral
one which concentrate at the identity converges strongly to the identity on real `L¹`. -/
theorem tendsto_convolutionL_right {ι : Type*} {l : Filter ι} {k : ι → Lp ℝ 1 μ}
    (hk : ∀ i, 0 ≤ k i) (hk1 : ∀ i, ∫ y, k i y ∂μ = 1)
    (hkl : ∀ U ∈ 𝓝 (1 : G), ∀ᶠ i in l, ∀ᵐ y ∂μ, y ∉ U → k i y = 0) (h : Lp ℝ 1 μ) :
    Tendsto (fun i => convolutionL μ 1 ENNReal.one_ne_top h (k i)) l (𝓝 h) := by
  -- Apply the isometry `J`, which turns `h ⋆ k i` into `J (k i) ⋆ J h`.
  rw [(modularInversion (E := ℝ) μ 1 ℝ).toHomeomorph.isInducing.tendsto_nhds_iff]
  simp only [comp_def, LinearIsometryEquiv.coe_toHomeomorph, modularInversion_convolutionL]
  refine tendsto_convolutionL_left (fun i => by simpa using modularInversion_mono (hk i))
    (fun i => by rw [integral_modularInversion, hk1]) (fun U hU => ?_) _
  filter_upwards [hkl _ (inv_mem_nhds_one G hU)] with i hi
  filter_upwards [coeFn_modularInversion (𝕜 := ℝ) (k i),
    (quasiMeasurePreserving_inv_of_regular μ).ae hi] with x hx hx' hxU
  rw [hx, hx' (by simpa using hxU), smul_zero]

end ModularInversion

end MeasureTheory.Lp
