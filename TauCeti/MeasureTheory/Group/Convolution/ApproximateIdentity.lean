/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.GroupConvolution
public import TauCeti.MeasureTheory.Function.Lp.RightTranslation
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Function.Lp.LocallyCompact
import TauCeti.MeasureTheory.Group.Convolution.Support
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# Approximate identities for `L¹` convolution on a locally compact group

Let `μ` be a regular left Haar measure on a locally compact group `G`, and let
`h ⋆ f = ∫ y, h(y) • L_y f dμ(y)` be the convolution `MeasureTheory.Lp.convolutionL` of an `L¹`
kernel with an `Lᵖ` function. A **kernel concentrating at the identity** is a family `k i` of
nonnegative `L¹` functions of integral one such that for every neighbourhood `U` of `1`, eventually
every `k i` vanishes almost everywhere outside `U`. Such kernels exist
(`MeasureTheory.Lp.exists_nonneg_integral_eq_one_of_mem_nhds`).

Convolving with such kernels on the left approximates the identity on `Lᵖ` for `p < ∞`:
`k ⋆ u - u = ∫ y, k(y) • (L_y u - u) dμ(y)`, and `L_y u` is close to `u` for `y` near `1` by strong
continuity of left translation. Convolving on the right approximates the identity on `L¹`. Since
convolution is not commutative, this is not a formal consequence of the left-hand statement. It
follows from the fact that the modular inversion `(J f)(x) = c(x) • f x⁻¹` of `L¹`, where `c` is
the modular character, reverses convolution:

```text
J (h ⋆ k) = J k ⋆ J h.
```

Indeed `J` is an isometry, so `‖h ⋆ k - h‖₁ = ‖J k ⋆ J h - J h‖₁`, and `J k` is again a nonnegative
kernel of integral one concentrated near `1`. The reversal identity is checked against set
integrals for compactly supported continuous `h` and `k`, where Fubini's theorem for compactly
supported continuous integrands needs no σ-finiteness, and extended to all of `L¹` by density and
continuity (`MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le_of_locallyCompactSpace`).
Neither σ-finiteness of `μ` nor any countability of `G` is assumed.

## Main results

* `MeasureTheory.Lp.convolutionL_toL1_ae_eq`: for compactly supported continuous `h` and `f`, the
  convolution `h ⋆ f` is represented by `x ↦ ∫ y, h y • f (y⁻¹ * x) dμ`.
* `MeasureTheory.Lp.modularInversion_convolutionL`: the modular inversion reverses convolution,
  `J (h ⋆ k) = J k ⋆ J h`.
* `MeasureTheory.Lp.norm_convolutionL_sub_le`: if `k ≥ 0`, `∫ k = 1`, `k` vanishes outside `S`,
  and `‖L_y u - u‖ ≤ ε` for `y ∈ S`, then `‖k ⋆ u - u‖ ≤ ε`.
* `MeasureTheory.Lp.tendsto_convolutionL_left`: `k i ⋆ u → u` in `Lᵖ` for kernels concentrating at
  the identity, for `1 ≤ p < ∞`.
* `MeasureTheory.Lp.tendsto_convolutionL_right`: `h ⋆ k i → h` in `L¹` for such kernels.

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
  {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E]

/-- For compactly supported continuous `h` and `f`, the convolution `h ⋆ f` is represented almost
everywhere by the pointwise convolution `x ↦ ∫ y, h y • f (y⁻¹ * x) dμ`. -/
theorem convolutionL_toL1_ae_eq {h : G → 𝕜} {f : G → E} (hhc : Continuous h)
    (hhs : HasCompactSupport h) (hfc : Continuous f) (hfs : HasCompactSupport f) :
    convolutionL μ 1 ENNReal.one_ne_top ((hhc.integrable_of_hasCompactSupport hhs).toL1 h)
        ((hfc.integrable_of_hasCompactSupport hfs).toL1 f) =ᵐ[μ]
      fun x => ∫ y, h y • f (y⁻¹ * x) ∂μ := by
  have hhi := hhc.integrable_of_hasCompactSupport (μ := μ) hhs
  have hfi := hfc.integrable_of_hasCompactSupport (μ := μ) hfs
  set F : G → G → E := fun x y => h y • f (y⁻¹ * x)
  have hFc : Continuous (uncurry F) :=
    (hhc.comp continuous_snd).smul (hfc.comp (continuous_snd.inv.mul continuous_fst))
  have hFsupp (x y : G) (hxy : F x y ≠ 0) : y ∈ tsupport h ∧ y⁻¹ * x ∈ tsupport f :=
    ⟨subset_tsupport _ (left_ne_zero_of_smul hxy), subset_tsupport _ (right_ne_zero_of_smul hxy)⟩
  have hFs : HasCompactSupport (uncurry F) :=
    hasCompactSupport_uncurry_of_inv_mul_mem hhs hfs hFsupp
  have hint : Integrable (fun x => ∫ y, F x y ∂μ) μ :=
    (continuous_integral_of_compact_support μ hhs hFc fun x y hxy =>
      (hFsupp x y hxy).1).integrable_of_hasCompactSupport
      (hasCompactSupport_integral_of_inv_mul_mem μ hhs hfs hFsupp)
  refine (L1.integrable_coeFn _).ae_eq_of_forall_setIntegral_eq _ _ hint fun s _ _ => ?_
  -- Integration over `s` is a continuous linear functional on `L¹`.
  let T : Lp E 1 μ →L[𝕜] E :=
    (L1.integralCLM' (μ := μ.restrict s) 𝕜).comp (LpToLpRestrictCLM G E 𝕜 μ 1 s)
  have hT (u : Lp E 1 μ) : T u = ∫ x in s, u x ∂μ := by
    rw [ContinuousLinearMap.comp_apply, ← L1.integral_eq', L1.integral_eq_integral]
    exact integral_congr_ae (LpToLpRestrictCLM_coeFn 𝕜 s u)
  have hL (y : G) : ∫ x in s, leftTranslation μ 1 𝕜 y (hfi.toL1 f) x ∂μ =
      ∫ x in s, f (y⁻¹ * x) ∂μ := by
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [coeFn_leftTranslation (𝕜 := 𝕜) y (hfi.toL1 f),
      (measurePreserving_mul_left μ y⁻¹).quasiMeasurePreserving.ae hfi.coeFn_toL1] with x h₁ h₂
    exact h₁.trans h₂
  rw [← hT, convolutionL_toL1 hhi,
    ← T.integral_comp_comm (integrable_smul_leftTranslation ENNReal.one_ne_top hhi _)]
  simp_rw [map_smul, hT, hL, ← integral_smul]
  -- Fubini's theorem for the compactly supported continuous integrand `(y, x) ↦ F x y`.
  exact integral_integral_swap_of_hasCompactSupport (f := fun y x => F x y)
    (hFc.comp continuous_swap) (hFs.comp_homeomorph (Homeomorph.prodComm G G))

/-- If `k` is a nonnegative kernel of integral one which vanishes outside `S`, and every left
translate `L_y u` with `y ∈ S` lies within `ε` of `u`, then `‖k ⋆ u - u‖_p ≤ ε`. -/
theorem norm_convolutionL_sub_le {k : Lp ℝ 1 μ} (hk : 0 ≤ k) (hk1 : ∫ y, k y ∂μ = 1)
    {S : Set G} (hkS : ∀ᵐ y ∂μ, y ∉ S → k y = 0) {u : Lp E p μ} {ε : ℝ}
    (hu : ∀ y ∈ S, ‖leftTranslation μ p ℝ y u - u‖ ≤ ε) :
    ‖convolutionL μ p hp k u - u‖ ≤ ε := by
  have hki := L1.integrable_coeFn k
  -- Since `∫ k = 1`, `k ⋆ u - u` is the average of `L_y u - u` against `k`.
  have hsub : convolutionL μ p hp k u - u =
      ∫ y, k y • (leftTranslation μ p ℝ y u - u) ∂μ := by
    simp_rw [smul_sub]
    rw [integral_sub (integrable_smul_leftTranslation hp hki u) (hki.smul_const u),
      integral_smul_const, hk1, one_smul, convolutionL_apply]
  rw [hsub]
  refine (norm_integral_le_of_norm_le (hki.mul_const ε) ?_).trans_eq
    (by rw [integral_mul_const, hk1, one_mul])
  filter_upwards [hkS, (coeFn_nonneg k).2 hk] with y hyS hy0
  by_cases hy : y ∈ S
  · rw [norm_smul, Real.norm_of_nonneg hy0]
    exact mul_le_mul_of_nonneg_left (hu y hy) hy0
  · simp [hyS hy]

/-- **Left approximate identity.** Convolution on the left with nonnegative kernels of integral
one which concentrate at the identity converges strongly to the identity on `Lᵖ`, for
`1 ≤ p < ∞`. -/
theorem tendsto_convolutionL_left {ι : Type*} {l : Filter ι} {k : ι → Lp ℝ 1 μ}
    (hk : ∀ i, 0 ≤ k i) (hk1 : ∀ i, ∫ y, k i y ∂μ = 1)
    (hkl : ∀ U ∈ 𝓝 (1 : G), ∀ᶠ i in l, ∀ᵐ y ∂μ, y ∉ U → k i y = 0) (u : Lp E p μ) :
    Tendsto (fun i => convolutionL μ p hp (k i) u) l (𝓝 u) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hcont : Tendsto (fun y : G => leftTranslation μ p ℝ y u) (𝓝 1) (𝓝 u) := by
    have h := (continuous_leftTranslation_apply (𝕜 := ℝ) hp u).tendsto 1
    rwa [map_one, LinearIsometryEquiv.coe_one, id_eq] at h
  set U := {y : G | dist (leftTranslation μ p ℝ y u) u ≤ ε / 2}
  have hU : U ∈ 𝓝 (1 : G) :=
    (Metric.tendsto_nhds.1 hcont (ε / 2) (half_pos hε)).mono fun _ hy => hy.le
  filter_upwards [hkl U hU] with i hi
  have hle : ‖convolutionL μ p hp (k i) u - u‖ ≤ ε / 2 :=
    norm_convolutionL_sub_le (S := U) (hk i) (hk1 i) hi fun y hy => by
      rw [← _root_.dist_eq_norm]
      exact hy
  rw [_root_.dist_eq_norm]
  exact hle.trans_lt (half_lt_self hε)

end LeftInvariant

section ModularInversion

variable [LocallyCompactSpace G] [μ.IsHaarMeasure] [μ.Regular]

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The modular inversion of the `L¹` class of a compactly supported continuous function `f` is the
class of `x ↦ c(x) • f x⁻¹`. -/
private theorem modularInversion_toL1 {f : G → 𝕜} (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hJc : Continuous fun x => (modularCharacter x : ℝ) • f x⁻¹)
    (hJs : HasCompactSupport fun x => (modularCharacter x : ℝ) • f x⁻¹) :
    modularInversion μ 1 𝕜 ((hfc.integrable_of_hasCompactSupport (μ := μ) hfs).toL1 f) =
      (hJc.integrable_of_hasCompactSupport hJs).toL1 _ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_modularInversion (𝕜 := 𝕜)
      ((hfc.integrable_of_hasCompactSupport (μ := μ) hfs).toL1 f),
    (quasiMeasurePreserving_inv_of_regular μ).ae
      (hfc.integrable_of_hasCompactSupport (μ := μ) hfs).coeFn_toL1,
    (hJc.integrable_of_hasCompactSupport (μ := μ) hJs).coeFn_toL1] with x h₁ h₂ h₃
  rw [h₁, h₃, h₂]
  simp

/-- The modular inversion reverses the convolution of compactly supported continuous functions. -/
private theorem modularInversion_convolutionL_toL1 {h k : G → 𝕜} (hhc : Continuous h)
    (hhs : HasCompactSupport h) (hkc : Continuous k) (hks : HasCompactSupport k) :
    modularInversion μ 1 𝕜 (convolutionL μ 1 ENNReal.one_ne_top
        ((hhc.integrable_of_hasCompactSupport hhs).toL1 h)
        ((hkc.integrable_of_hasCompactSupport hks).toL1 k)) =
      convolutionL μ 1 ENNReal.one_ne_top
        (modularInversion μ 1 𝕜 ((hkc.integrable_of_hasCompactSupport hks).toL1 k))
        (modularInversion μ 1 𝕜 ((hhc.integrable_of_hasCompactSupport hhs).toL1 h)) := by
  have hc (f : G → 𝕜) (hf : Continuous f) :
      Continuous fun x => (modularCharacter x : ℝ) • f x⁻¹ :=
    (NNReal.continuous_coe.comp continuous_modularCharacter).smul (hf.comp continuous_inv)
  have hs (f : G → 𝕜) (hf : HasCompactSupport f) :
      HasCompactSupport fun x => (modularCharacter x : ℝ) • f x⁻¹ :=
    (hf.comp_homeomorph (Homeomorph.inv G)).smul_left (f := fun x => (modularCharacter x : ℝ))
  rw [modularInversion_toL1 hkc hks (hc k hkc) (hs k hks),
    modularInversion_toL1 hhc hhs (hc h hhc) (hs h hhs)]
  refine Lp.ext ?_
  filter_upwards [coeFn_modularInversion (𝕜 := 𝕜) (convolutionL μ 1 ENNReal.one_ne_top
      ((hhc.integrable_of_hasCompactSupport (μ := μ) hhs).toL1 h)
      ((hkc.integrable_of_hasCompactSupport (μ := μ) hks).toL1 k)),
    (quasiMeasurePreserving_inv_of_regular μ).ae (convolutionL_toL1_ae_eq hhc hhs hkc hks),
    convolutionL_toL1_ae_eq (μ := μ) (hc k hkc) (hs k hks) (hc h hhc) (hs h hhs)]
    with x h₁ h₂ h₃
  rw [h₁, h₃, h₂]
  -- Substitute `y ↦ x * y` on the right, using left invariance of `μ`.
  conv_rhs => rw [← integral_mul_left_eq_self _ x]
  simp only [ENNReal.toReal_one, inv_one, Real.rpow_one, ← integral_smul]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only [mul_inv_rev, inv_inv, inv_mul_cancel_right, smul_eq_mul]
  rw [smul_mul_smul_comm, ← NNReal.coe_mul, ← map_mul, mul_inv_cancel_right, mul_comm (k _)]

/-- **The modular inversion reverses convolution**: `J (h ⋆ k) = J k ⋆ J h` for `h, k ∈ L¹`,
where `(J f)(x) = c(x) • f x⁻¹` and `c` is the modular character. -/
theorem modularInversion_convolutionL (h k : Lp 𝕜 1 μ) :
    modularInversion μ 1 𝕜 (convolutionL μ 1 ENNReal.one_ne_top h k) =
      convolutionL μ 1 ENNReal.one_ne_top (modularInversion μ 1 𝕜 k)
        (modularInversion μ 1 𝕜 h) := by
  -- Both sides are continuous in `(h, k)` and agree on compactly supported continuous functions.
  have hJ := (modularInversion (E := 𝕜) μ 1 𝕜).continuous
  have hconv := (convolutionL (𝕜 := 𝕜) (E := 𝕜) μ 1 ENNReal.one_ne_top).continuous₂
  have hc₁ : Continuous fun q : Lp 𝕜 1 μ × Lp 𝕜 1 μ =>
      modularInversion μ 1 𝕜 (convolutionL μ 1 ENNReal.one_ne_top q.1 q.2) :=
    hJ.comp hconv
  have hc₂ : Continuous fun q : Lp 𝕜 1 μ × Lp 𝕜 1 μ =>
      convolutionL μ 1 ENNReal.one_ne_top (modularInversion μ 1 𝕜 q.2)
        (modularInversion μ 1 𝕜 q.1) :=
    hconv.comp ((hJ.comp continuous_snd).prodMk (hJ.comp continuous_fst))
  have hD : Dense {u : Lp 𝕜 1 μ | ∃ (f : G → 𝕜) (hfc : Continuous f) (hfs : HasCompactSupport f),
      u = (hfc.integrable_of_hasCompactSupport hfs).toL1 f} := by
    refine Metric.dense_iff.2 fun u r hr => ?_
    obtain ⟨f, hfs, hf, hfc, -⟩ :=
      (Lp.memLp u).exists_hasCompactSupport_eLpNorm_sub_le_of_locallyCompactSpace
        ENNReal.one_ne_top (ENNReal.ofReal_pos.2 (half_pos hr)).ne'
    refine ⟨_, ?_, f, hfc, hfs, rfl⟩
    rw [Metric.mem_ball, dist_comm, Lp.dist_def, eLpNorm_congr_ae (EventuallyEq.rfl.sub
      (hfc.integrable_of_hasCompactSupport (μ := μ) hfs).coeFn_toL1)]
    exact (ENNReal.toReal_le_of_le_ofReal (half_pos hr).le hf).trans_lt (half_lt_self hr)
  refine congrFun (Continuous.ext_on (hD.prod hD) hc₁ hc₂ ?_) (h, k)
  rintro ⟨_, _⟩ ⟨⟨f, hfc, hfs, rfl⟩, ⟨g, hgc, hgs, rfl⟩⟩
  exact modularInversion_convolutionL_toL1 hfc hfs hgc hgs

/-- **Right approximate identity.** Convolution on the right with nonnegative kernels of integral
one which concentrate at the identity converges strongly to the identity on `L¹`. -/
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
