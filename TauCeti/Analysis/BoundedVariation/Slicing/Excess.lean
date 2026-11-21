/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Convolution
public import TauCeti.Analysis.BoundedVariation.Slicing.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.BoundedVariation.Convolution
import TauCeti.Analysis.BoundedVariation.Real
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Distribution.TestFunction.Convolution
import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz

/-!
# Perimeter excess from noninterval line sections

For a finite-volume Lebesgue-measurable set `s` and a unit direction `e`, let `D` be the
set of transverse points whose line sections have positive length. Every such section costs
at least two units of one-dimensional perimeter. A section that does not agree almost
everywhere with an interval costs at least four instead.

Consequently, for any null-measurable family `A` of noninterval sections,

`2 volume D + 2 volume A ≤ perimeter volume ⊤ s`.

The weighted version retains the transverse divergence pairing in the joint slicing inequality.
It localizes the extra cost to `A`. After importing
`TauCeti.Analysis.BoundedVariation.Slicing.Measurability`, the full family of noninterval sections
is null-measurable, so both bounds apply to it by taking
`hA := nullMeasurableSet_noninterval_lineSection hs hfin e he` and `hbad := .of_forall fun _ ↦ id`.

When `s` has finite perimeter, testing the localized joint slicing inequality against mollified
regularized gradient vector fields for a radial smooth bump `ρ` on `(ℝ ∙ e)ᗮ` and applying
Cauchy–Schwarz yields the mollified slicing excess bound
(`MeasureTheory.NullMeasurableSet.mul_integral_sqrt_normed_convolution_add_two_mul_sq_le`): writing
`d = ρ ⋆ (2 · 1_D)`, `w = ρ ⋆ v` (where `v(y) = |s_y|`), `a = ρ ⋆ 1_A`, and `M = 2 |D| + |Dv|`,

`M ∫ √(d² + ‖Dw‖²) + 2 (∫ a √d)² ≤ M P(s)`.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.2 and §3.11, for one-dimensional variation and slicing.
* F. Cagnetti, M. Colombo, G. De Philippis, F. Maggi, *Rigidity of equality cases in Steiner's
  perimeter inequality*, Anal. PDE **7** (2014), §1.2, for the interval-section condition.
-/

public section

open ContinuousLinearMap Filter InnerProductSpace MeasureTheory Metric Set TestFunction
  TopologicalSpace
open scoped Convolution Distributions ENNReal Pointwise RealInnerProductSpace Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The weighted perimeters of line sections pay twice for every positive-length section and
an additional two for each section in a null-measurable family `A` of noninterval sections.
The weight is arbitrary and nonnegative; no measurability assumption on it is needed. -/
theorem two_mul_setLIntegral_add_two_mul_setLIntegral_le_lintegral_mul_perimeter_lineSection
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (e : E) (he : ‖e‖ = 1) {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I)
    (w : (ℝ ∙ e)ᗮ → ℝ≥0∞) :
    2 * (∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}, w y) +
        2 * (∫⁻ y in A, w y) ≤
      ∫⁻ y : (ℝ ∙ e)ᗮ, w y * perimeter volume ⊤ {t : ℝ | (y : E) + t • e ∈ s} := by
  let D := {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}
  have hD : NullMeasurableSet D volume :=
    nullMeasurableSet_lt aemeasurable_const (aemeasurable_volume_lineSection e he hs)
  have hpoint : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume,
      D.indicator (fun _ ↦ (2 : ℝ≥0∞)) y + A.indicator (fun _ ↦ (2 : ℝ≥0∞)) y ≤
        perimeter volume ⊤ {t : ℝ | (y : E) + t • e ∈ s} := by
    filter_upwards [ae_nullMeasurableSet_lineSection e he hs,
      ae_volume_lineSection_lt_top e he hs hfin, hbad] with y hym hyfin hybad
    by_cases hyA : y ∈ A
    · have hfour := Real.four_le_perimeter hym hyfin.ne (hybad hyA)
      have htwo : D.indicator (fun _ ↦ (2 : ℝ≥0∞)) y ≤ 2 := by
        by_cases hyD : y ∈ D <;> simp [hyD]
      calc
        _ ≤ 2 + 2 := add_le_add htwo (by simp [hyA])
        _ = 4 := by norm_num
        _ ≤ _ := hfour
    · by_cases hyD : y ∈ D
      · simpa [hyA, hyD] using Real.two_le_perimeter hym hyD.ne' hyfin.ne
      · simp [hyA, hyD]
  calc
    _ = (∫⁻ y, D.indicator (fun y ↦ 2 * w y) y) +
        ∫⁻ y, A.indicator (fun y ↦ 2 * w y) y := by
      rw [lintegral_indicator₀ hD, lintegral_indicator₀ hA,
        lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
    _ ≤ ∫⁻ y, D.indicator (fun y ↦ 2 * w y) y +
        A.indicator (fun y ↦ 2 * w y) y := le_lintegral_add _ _
    _ ≤ _ := lintegral_mono_ae (hpoint.mono fun y hy ↦ by
      have hm := mul_le_mul_left hy (w y)
      by_cases hyD : y ∈ D <;> by_cases hyA : y ∈ A <;>
        simp_all [mul_add, mul_comm])

/-- A localized strengthening of the joint slicing inequality. The transverse test field
retains the pairing with section lengths, while each noninterval section in `A` contributes
an extra `2 √(1 - ‖φ‖²)` to the lower bound for the ambient perimeter. -/
theorem two_mul_setLIntegral_add_two_mul_setLIntegral_add_ofReal_integral_le_perimeter
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (e : E) (he : ‖e‖ = 1) {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I)
    (φ : 𝓓(⊤, (ℝ ∙ e)ᗮ)) (hφ : ∀ y, ‖φ y‖ ≤ 1) :
    (2 * (∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
        ENNReal.ofReal √(1 - ‖φ y‖ ^ 2)) +
      2 * (∫⁻ y in A, ENNReal.ofReal √(1 - ‖φ y‖ ^ 2))) +
      ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM φ y *
        volume.real {t : ℝ | (y : E) + t • e ∈ s}) ≤ perimeter volume ⊤ s :=
  (add_le_add
    (two_mul_setLIntegral_add_two_mul_setLIntegral_le_lintegral_mul_perimeter_lineSection
      hs hfin e he hA hbad (fun y ↦ ENNReal.ofReal √(1 - ‖φ y‖ ^ 2))) le_rfl).trans
    (lintegral_mul_perimeter_lineSection_add_ofReal_integral_le hs hfin e he φ hφ)

/-- The perimeter bounds twice the transverse measure of positive-length sections plus twice
the measure of any null-measurable family of noninterval sections. This extended inequality
also applies when the ambient perimeter is infinite. -/
theorem two_mul_volume_add_two_mul_volume_le_perimeter_of_noninterval_lineSection
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (e : E) (he : ‖e‖ = 1) {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I) :
    2 * volume {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} +
        2 * volume A ≤ perimeter volume ⊤ s := by
  have h := two_mul_setLIntegral_add_two_mul_setLIntegral_le_lintegral_mul_perimeter_lineSection
    hs hfin e he hA hbad (fun _ ↦ 1)
  simpa using h.trans (by simpa using lintegral_perimeter_lineSection_le hs hfin e he)

end TauCeti

namespace MeasureTheory.NullMeasurableSet

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

section MollifiedExcess

noncomputable section

/-- **Mollified slicing excess inequality.** Let `s` be a Lebesgue-measurable set of finite volume
and finite perimeter, `e` a unit vector with orthogonal hyperplane `H = (ℝ ∙ e)ᗮ`, `A ⊆ H` a
null-measurable family of noninterval line sections of `s`, and `ρ` a radial smooth bump on `H`.
Writing `D = {y ∈ H | 0 < |s_y|}`, `v(y) = |s_y|`, `d = ρ ⋆ (2 · 1_D)`, `w = ρ ⋆ v`,
`a = ρ ⋆ 1_A`, and `M = 2 |D| + |Dv|`, we have

`M ∫ √(d² + ‖Dw‖²) + 2 (∫ a √d)² ≤ M P(s)`. -/
theorem mul_integral_sqrt_normed_convolution_add_two_mul_sq_le
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (hP : perimeter volume ⊤ s ≠ ∞) (e : E) (he : ‖e‖ = 1)
    {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I)
    (ρ : ContDiffBump (0 : (ℝ ∙ e)ᗮ)) :
    (2 * volume.real {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} +
        (totalVariationOn volume ⊤
          (fun y : (ℝ ∙ e)ᗮ ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s})).toReal) *
      (∫ y : (ℝ ∙ e)ᗮ,
        √((ρ.normed volume ⋆[lsmul ℝ ℝ, volume]
            {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}.indicator
              (fun _ ↦ (2 : ℝ))) y ^ 2 +
          ‖fderiv ℝ (ρ.normed volume ⋆[lsmul ℝ ℝ, volume]
            (fun y : (ℝ ∙ e)ᗮ ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s})) y‖ ^ 2)) +
      2 * (∫ y : (ℝ ∙ e)ᗮ,
        (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] A.indicator (fun _ ↦ (1 : ℝ))) y *
          √((ρ.normed volume ⋆[lsmul ℝ ℝ, volume]
            {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}.indicator
              (fun _ ↦ (2 : ℝ))) y)) ^ 2 ≤
    (2 * volume.real {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} +
        (totalVariationOn volume ⊤
          (fun y : (ℝ ∙ e)ᗮ ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s})).toReal) *
      (perimeter volume ⊤ s).toReal := by
  let H := (ℝ ∙ e)ᗮ
  let D : Set H := {y : H | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}
  let v : H → ℝ := fun y ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s}
  let κ : H → ℝ := ρ.normed volume
  let d : H → ℝ := κ ⋆[lsmul ℝ ℝ, volume] D.indicator (fun _ ↦ (2 : ℝ))
  let w : H → ℝ := κ ⋆[lsmul ℝ ℝ, volume] v
  let a : H → ℝ := κ ⋆[lsmul ℝ ℝ, volume] A.indicator (fun _ ↦ (1 : ℝ))
  let M : ℝ := 2 * volume.real D + (totalVariationOn volume ⊤ v).toReal
  have hD : NullMeasurableSet D volume :=
    nullMeasurableSet_lt aemeasurable_const (aemeasurable_volume_lineSection e he hs)
  have hDA_le := two_mul_volume_add_two_mul_volume_le_perimeter_of_noninterval_lineSection
    hs hfin e he hA hbad
  have hDfin : volume D ≠ ∞ := ne_top_of_le_ne_top hP <|
    (le_self_add.trans_eq (two_mul _).symm).trans (le_self_add.trans hDA_le)
  have hAfin : volume A ≠ ∞ := ne_top_of_le_ne_top hP <|
    (le_self_add.trans_eq (two_mul _).symm).trans (le_add_self.trans hDA_le)
  have hv_tv_fin : totalVariationOn volume ⊤ v ≠ ∞ :=
    ne_top_of_le_ne_top hP (totalVariationOn_measureReal_lineSection_le hs hfin e he)
  have hv_int : Integrable v volume :=
    ⟨(aemeasurable_volume_lineSection e he hs).ennreal_toReal.aestronglyMeasurable,
      (lintegral_mono fun y ↦ by
        rw [Real.eNorm_of_nonneg measureReal_nonneg, measureReal_def]
        exact ENNReal.ofReal_toReal_le).trans_lt
        ((volume_eq_lintegral_volume_lineSection e he hs).symm ▸ hfin.lt_top)⟩
  have hD_ind_int : Integrable (D.indicator (fun _ ↦ (2 : ℝ))) volume :=
    (integrableOn_const hDfin).integrable_indicator₀ hD
  have hA_ind_int : Integrable (A.indicator (fun _ ↦ (1 : ℝ))) volume :=
    (integrableOn_const hAfin).integrable_indicator₀ hA
  have hcsmooth {f : H → ℝ} (hf : Integrable f volume) :
      ContDiff ℝ (⊤ : ℕ∞) (κ ⋆[lsmul ℝ ℝ, volume] f) :=
    ρ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) ρ.contDiff_normed
      hf.locallyIntegrable
  have hd_smooth : ContDiff ℝ (⊤ : ℕ∞) d := hcsmooth hD_ind_int
  have hw_smooth : ContDiff ℝ (⊤ : ℕ∞) w := hcsmooth hv_int
  have ha_smooth : ContDiff ℝ (⊤ : ℕ∞) a := hcsmooth hA_ind_int
  have hd_int : Integrable d volume := ρ.integrable_normed.integrable_convolution _ hD_ind_int
  have ha_int : Integrable a volume := ρ.integrable_normed.integrable_convolution _ hA_ind_int
  have hd_mem (y : H) : d y ∈ Icc (0 : ℝ) 2 :=
    ρ.normed_convolution_mem_Icc hD_ind_int.locallyIntegrable
      (fun z ↦ by by_cases hz : z ∈ D <;> simp [hz]) y
  have ha_mem (y : H) : a y ∈ Icc (0 : ℝ) 1 :=
    ρ.normed_convolution_mem_Icc hA_ind_int.locallyIntegrable
      (fun z ↦ by by_cases hz : z ∈ A <;> simp [hz]) y
  have hd_int_eq : ∫ y : H, d y = 2 * volume.real D := by
    rw [integral_convolution (lsmul ℝ ℝ) ρ.integrable_normed hD_ind_int, lsmul_apply,
      ρ.integral_normed, one_smul, integral_indicator₀ hD, setIntegral_const, smul_eq_mul, mul_comm]
  have ha_int_eq : ∫ y : H, a y = volume.real A := by
    rw [integral_convolution (lsmul ℝ ℝ) ρ.integrable_normed hA_ind_int, lsmul_apply,
      ρ.integral_normed, one_smul, integral_indicator₀ hA, setIntegral_const, smul_eq_mul, mul_one]
  let gradW : H → H := fun y ↦ (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ w y)
  have hgradW_smooth : ContDiff ℝ (⊤ : ℕ∞) gradW :=
    (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearMap.contDiff.comp
      (hw_smooth.fderiv_right (by simp))
  have hgradW_norm (y : H) : ‖gradW y‖ = ‖fderiv ℝ w y‖ := LinearIsometryEquiv.norm_map _ _
  have hw1 : ContDiff ℝ 1 w := hw_smooth.of_le (by simp)
  have hgradW_cont : Continuous (fun y : H ↦ ‖fderiv ℝ w y‖) :=
    (hw1.continuous_fderiv one_ne_zero).norm
  have hgradW_int : Integrable (fun y : H ↦ ‖fderiv ℝ w y‖) volume :=
    ρ.integrable_norm_fderiv_normed_convolution hv_int.locallyIntegrable hv_tv_fin
  have hgradW_int_le : ∫ y : H, ‖fderiv ℝ w y‖ ≤ (totalVariationOn volume ⊤ v).toReal :=
    ρ.integral_norm_fderiv_normed_convolution_le hv_int.locallyIntegrable hv_tv_fin
  have hdiv_bound {x y δ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hδ : 0 < δ) :
      (x ^ 2 + y ^ 2) / √(x ^ 2 + y ^ 2 + δ ^ 2) ≤ x + y := by
    have h1 : (x ^ 2 + y ^ 2) / √(x ^ 2 + y ^ 2 + δ ^ 2) ≤ √(x ^ 2 + y ^ 2) := by
      rw [div_le_iff₀ (Real.sqrt_pos.2 (by positivity))]
      calc x ^ 2 + y ^ 2 = √(x ^ 2 + y ^ 2) * √(x ^ 2 + y ^ 2) :=
            (Real.mul_self_sqrt (by positivity)).symm
        _ ≤ √(x ^ 2 + y ^ 2) * √(x ^ 2 + y ^ 2 + δ ^ 2) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith [sq_nonneg δ]))
              (Real.sqrt_nonneg _)
    exact h1.trans (Real.sqrt_le_left (add_nonneg hx hy) |>.2 (by nlinarith [mul_nonneg hx hy]))
  -- For any fixed `δ > 0`, prove the regularized estimate before letting `δ → 0⁺`.
  have hdelta {δ : ℝ} (hδ : 0 < δ) :
      let g : H → ℝ := fun y ↦ √(d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2 + δ ^ 2)
      let Mδ : ℝ := M + δ * volume.real A
      Mδ * (∫ y : H, (d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2) / g y) + 2 * (∫ y : H, a y * √(d y)) ^ 2 ≤
        Mδ * (perimeter volume ⊤ s).toReal := by
    intro g Mδ
    have hg_pos (y : H) : 0 < g y := Real.sqrt_pos.2 (by positivity)
    have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g := by
      have hinner : ContDiff ℝ (⊤ : ℕ∞) fun y : H ↦ d y ^ 2 + ⟪gradW y, gradW y⟫_ℝ + δ ^ 2 :=
        ((hd_smooth.pow 2).add (hgradW_smooth.inner ℝ hgradW_smooth)).add contDiff_const
      have hrad : (fun y : H ↦ d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2 + δ ^ 2) =
          fun y : H ↦ d y ^ 2 + ⟪gradW y, gradW y⟫_ℝ + δ ^ 2 :=
        funext fun y ↦ by rw [real_inner_self_eq_norm_sq, hgradW_norm]
      rw [contDiff_iff_contDiffAt]
      exact fun y ↦ (Real.contDiffAt_sqrt (by positivity)).comp y (hrad ▸ hinner.contDiffAt)
    have hdg_mem (y : H) : d y / g y ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (hd_mem y).1 (hg_pos y).le, (div_le_one (hg_pos y)).2
        (Real.le_sqrt_of_sq_le (by linarith [sq_nonneg ‖fderiv ℝ w y‖, sq_nonneg δ]))⟩
    -- Test the localized slicing bound against compactly supported cutoffs `η`.
    have heta (η : ContDiffBump (0 : H)) :
        (∫ y : H, η y * (d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2) / g y) +
          2 * (∫ y : H, a y * (d y / g y)) ≤ (perimeter volume ⊤ s).toReal := by
      let ψ₀ : H → ℝ := fun y ↦ η y * d y / g y
      let φ₀_fun : H → H := fun y ↦ (-(η y * (g y)⁻¹)) • gradW y
      let φ₀ : 𝓓(⊤, H) := ⟨φ₀_fun,
        ((η.contDiff.mul (hg_smooth.inv fun y ↦ (hg_pos y).ne')).neg).smul hgradW_smooth,
        (η.hasCompactSupport.mul_right.neg).smul_right, subset_univ _⟩
      have hφ₀_apply (y : H) : φ₀ y = (-(η y * (g y)⁻¹)) • gradW y := by
        simp only [φ₀, φ₀_fun, TestFunction.coe_mk]
      let φ : 𝓓(⊤, H) := TestFunction.mollify φ₀ volume ρ (subset_univ _)
      let ψ : H → ℝ := κ ⋆[lsmul ℝ ℝ, volume] ψ₀
      let α : H → ℝ := κ ⋆[lsmul ℝ ℝ, volume] (fun y ↦ d y / g y)
      have hψ₀_cont : Continuous ψ₀ :=
        (η.continuous.mul hd_smooth.continuous).div hg_smooth.continuous fun y ↦ (hg_pos y).ne'
      have hdg_cont : Continuous (fun y : H ↦ d y / g y) :=
        hd_smooth.continuous.div hg_smooth.continuous fun y ↦ (hg_pos y).ne'
      have hψ₀_mem (y : H) : ψ₀ y ∈ Icc (0 : ℝ) 1 := by
        refine ⟨div_nonneg (mul_nonneg η.nonneg (hd_mem y).1) (hg_pos y).le, ?_⟩
        rw [show ψ₀ y = η y * (d y / g y) from mul_div_assoc _ _ _]
        exact (mul_le_mul η.le_one (hdg_mem y).2 (hdg_mem y).1 zero_le_one).trans_eq (one_mul 1)
      have hsq_α (y : H) : (d y / g y) ^ 2 + ‖φ₀ y‖ ^ 2 ≤ 1 := by
        have hnorm : ‖φ₀ y‖ = η y * ‖fderiv ℝ w y‖ / g y := by
          rw [hφ₀_apply, norm_smul, norm_neg,
            Real.norm_of_nonneg (mul_nonneg η.nonneg (inv_nonneg.2 (hg_pos y).le)), hgradW_norm,
            div_eq_mul_inv]
          ring
        rw [hnorm, div_pow, div_pow, mul_pow, ← add_div, div_le_one (sq_pos_of_pos (hg_pos y)),
          Real.sq_sqrt (by positivity)]
        have hη1 : η y ^ 2 ≤ 1 := by nlinarith [η.nonneg (x := y), η.le_one (x := y)]
        nlinarith [sq_nonneg ‖fderiv ℝ w y‖, sq_nonneg δ]
      have hsq_ψ (y : H) : ψ₀ y ^ 2 + ‖φ₀ y‖ ^ 2 ≤ 1 := by
        have hψle : ψ₀ y ^ 2 ≤ (d y / g y) ^ 2 := by
          rw [show ψ₀ y = η y * (d y / g y) from mul_div_assoc _ _ _, mul_pow]
          exact mul_le_of_le_one_left (sq_nonneg _)
            (by nlinarith [η.nonneg (x := y), η.le_one (x := y)])
        exact (add_le_add hψle le_rfl).trans (hsq_α y)
      have hφ_le (y : H) : ‖φ y‖ ≤ 1 := by
        rw [TestFunction.mollify_apply]
        exact ρ.norm_normed_convolution_le (fun z ↦ by
          nlinarith [hsq_α z, sq_nonneg (d z / g z), norm_nonneg (φ₀ z)]) y
      have hpair_D : ∫ y : H, D.indicator (fun _ ↦ (2 : ℝ)) y * ψ y =
          ∫ y : H, η y * d y ^ 2 / g y := by
        rw [ρ.integral_mul_normed_convolution_eq_of_bdd hD_ind_int hψ₀_cont.aestronglyMeasurable
          (C := 1) fun y ↦ by rw [Real.norm_of_nonneg (hψ₀_mem y).1]; exact (hψ₀_mem y).2]
        exact integral_congr_ae (.of_forall fun y ↦ by dsimp [ψ₀]; ring)
      have hpair_A : ∫ y : H, A.indicator (fun _ ↦ (1 : ℝ)) y * α y =
          ∫ y : H, a y * (d y / g y) :=
        ρ.integral_mul_normed_convolution_eq_of_bdd hA_ind_int hdg_cont.aestronglyMeasurable
          (C := 1) fun y ↦ by rw [Real.norm_of_nonneg (hdg_mem y).1]; exact (hdg_mem y).2
      have hpair_div : ∫ y : H, divergenceCLM φ y * v y =
          ∫ y : H, η y * ‖fderiv ℝ w y‖ ^ 2 / g y := by
        obtain ⟨C, hC⟩ := (divergenceCLM φ₀).continuous.bounded_above_of_compact_support
          (divergenceCLM φ₀).hasCompactSupport
        have h1 : ∫ y : H, divergenceCLM φ y * v y =
            ∫ y : H, v y * (κ ⋆[lsmul ℝ ℝ, volume] (divergenceCLM φ₀ : H → ℝ)) y :=
          integral_congr_ae (.of_forall fun y ↦ by
            dsimp only; rw [mul_comm, divergenceCLM_mollify])
        rw [h1, ρ.integral_mul_normed_convolution_eq_of_bdd hv_int
          (divergenceCLM φ₀).continuous.aestronglyMeasurable hC,
          integral_congr_ae (.of_forall fun y ↦ by rw [mul_comm, ← smul_eq_mul]),
          ((hw_smooth.of_le (by simp)).contDiffOn.hasWeakFDerivOn_fderiv
            (μ := volume) (Ω := ⊤)).integral_divergenceCLM_smul_eq_neg_integral φ₀,
          ← integral_neg]
        refine integral_congr_ae (.of_forall fun y ↦ ?_)
        dsimp only
        rw [(InnerProductSpace.toDual_symm_apply (y := fderiv ℝ w y) (x := φ₀ y)).symm, hφ₀_apply]
        dsimp only [gradW]
        rw [inner_smul_right, real_inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map,
          div_eq_mul_inv]
        ring
      have hterm_le {S : Set H} (hS : NullMeasurableSet S volume) {c : ℝ} (hc : 0 ≤ c)
          (hS_int : Integrable (S.indicator (fun _ ↦ c)) volume) {h₀ : H → ℝ} (hh₀ : Continuous h₀)
          (hmem : ∀ y, h₀ y ∈ Icc (0 : ℝ) 1) (hsq : ∀ y, h₀ y ^ 2 + ‖φ₀ y‖ ^ 2 ≤ 1) :
          ENNReal.ofReal (∫ y : H, S.indicator (fun _ ↦ c) y * (κ ⋆[lsmul ℝ ℝ, volume] h₀) y) ≤
            ENNReal.ofReal c * ∫⁻ y in S, ENNReal.ofReal √(1 - ‖φ y‖ ^ 2) := by
        have hm (y : H) := ρ.normed_convolution_mem_Icc (μ := volume) hh₀.locallyIntegrable hmem y
        have hcont : Continuous (κ ⋆[lsmul ℝ ℝ, volume] h₀) :=
          ρ.hasCompactSupport_normed.continuous_convolution_left
            (lsmul ℝ ℝ) ρ.continuous_normed hh₀.locallyIntegrable
        rw [ofReal_integral_eq_lintegral_ofReal (hS_int.mul_bdd (c := 1)
              hcont.aestronglyMeasurable (.of_forall fun y ↦ by
                rw [Real.norm_of_nonneg (hm y).1]; exact (hm y).2))
            (.of_forall fun y ↦ mul_nonneg (by by_cases hy : y ∈ S <;> simp [hy, hc]) (hm y).1),
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator₀ hS]
        refine lintegral_mono fun y ↦ ?_
        by_cases hy : y ∈ S
        · rw [indicator_of_mem hy, indicator_of_mem hy, ENNReal.ofReal_mul hc,
            TestFunction.mollify_apply]
          exact mul_le_mul_right (ENNReal.ofReal_le_ofReal
            (ρ.normed_convolution_le_sqrt_one_sub_sq hh₀ φ₀.continuous hsq y)) _
        · simp [hy]
      have htermD : ENNReal.ofReal (∫ y : H, D.indicator (fun _ ↦ (2 : ℝ)) y * ψ y) ≤
          2 * ∫⁻ y in D, ENNReal.ofReal √(1 - ‖φ y‖ ^ 2) := by
        simpa only [ENNReal.ofReal_ofNat] using
          hterm_le hD zero_le_two hD_ind_int hψ₀_cont hψ₀_mem hsq_ψ
      have htermA : ENNReal.ofReal (2 * ∫ y : H, A.indicator (fun _ ↦ (1 : ℝ)) y * α y) ≤
          2 * ∫⁻ y in A, ENNReal.ofReal √(1 - ‖φ y‖ ^ 2) := by
        rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
        refine mul_le_mul_right ?_ 2
        simpa only [ENNReal.ofReal_one, one_mul] using
          hterm_le hA zero_le_one hA_ind_int hdg_cont hdg_mem hsq_α
      have hI1 : Integrable (fun y : H ↦ η y * d y ^ 2 / g y) volume :=
        hd_int.mono' (((η.continuous.mul (hd_smooth.continuous.pow 2)).div
          hg_smooth.continuous fun y ↦ (hg_pos y).ne').aestronglyMeasurable) (.of_forall fun y ↦ by
            rw [Real.norm_of_nonneg (div_nonneg (mul_nonneg η.nonneg (sq_nonneg _)) (hg_pos y).le),
              show η y * d y ^ 2 / g y = ψ₀ y * d y by dsimp [ψ₀]; ring]
            exact mul_le_of_le_one_left (hd_mem y).1 (hψ₀_mem y).2)
      have hI2 : Integrable (fun y : H ↦ η y * ‖fderiv ℝ w y‖ ^ 2 / g y) volume :=
        hgradW_int.mono' (((η.continuous.mul (hgradW_cont.pow 2)).div
          hg_smooth.continuous fun y ↦ (hg_pos y).ne').aestronglyMeasurable) (.of_forall fun y ↦ by
            rw [Real.norm_of_nonneg (div_nonneg (mul_nonneg η.nonneg (sq_nonneg _)) (hg_pos y).le),
              show η y * ‖fderiv ℝ w y‖ ^ 2 / g y = (η y * (‖fderiv ℝ w y‖ / g y)) *
                ‖fderiv ℝ w y‖ by ring]
            have hle1 : ‖fderiv ℝ w y‖ / g y ≤ 1 := (div_le_one (hg_pos y)).2
              (Real.le_sqrt_of_sq_le (by linarith [sq_nonneg (d y), sq_nonneg δ]))
            exact mul_le_of_le_one_left (opNorm_nonneg _)
              ((mul_le_mul η.le_one hle1 (div_nonneg (opNorm_nonneg _) (hg_pos y).le)
                zero_le_one).trans_eq (one_mul 1)))
      rw [show (∫ y : H, η y * (d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2) / g y) =
            (∫ y : H, η y * d y ^ 2 / g y) + ∫ y : H, η y * ‖fderiv ℝ w y‖ ^ 2 / g y by
          rw [← integral_add hI1 hI2]; exact integral_congr_ae (.of_forall fun _ ↦ by ring)]
      refine (ENNReal.ofReal_le_iff_le_toReal hP).1 ?_
      rw [add_right_comm]
      exact (ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)).trans <| by
        rw [← hpair_D, ← hpair_A, ← hpair_div]
        exact (add_le_add (add_le_add htermD htermA) le_rfl).trans
          (two_mul_setLIntegral_add_two_mul_setLIntegral_add_ofReal_integral_le_perimeter
            hs hfin e he hA hbad φ hφ_le)
    -- Exhaust `H` with bumps `ηseq m ↑ 1` by dominated convergence.
    let ηseq : ℕ → ContDiffBump (0 : H) := fun m ↦
      ⟨(m : ℝ) + 1, (m : ℝ) + 2, by positivity, by linarith⟩
    have hη_lim : Tendsto (fun m ↦ ∫ y : H, ηseq m y * (d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2) / g y)
        atTop (𝓝 (∫ y : H, (d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2) / g y)) := by
      refine tendsto_integral_of_dominated_convergence (fun y ↦ d y + ‖fderiv ℝ w y‖)
        (fun m ↦ (((ηseq m).continuous.mul ((hd_smooth.continuous.pow 2).add
          (hgradW_cont.pow 2))).div hg_smooth.continuous
          fun y ↦ (hg_pos y).ne').aestronglyMeasurable)
        (hd_int.add hgradW_int) (fun m ↦ .of_forall fun y ↦ ?_) (.of_forall fun y ↦ ?_)
      · have hq0 : 0 ≤ (d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2) / g y :=
          div_nonneg (by positivity) (hg_pos y).le
        rw [mul_div_assoc, Real.norm_of_nonneg (mul_nonneg (ηseq m).nonneg hq0)]
        exact (mul_le_of_le_one_left hq0 (ηseq m).le_one).trans
          (hdiv_bound (hd_mem y).1 (opNorm_nonneg _) hδ)
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop (Nat.ceil ‖y‖)] with m hm
        have hball : y ∈ closedBall (0 : H) (ηseq m).rIn := by
          rw [mem_closedBall_zero_iff]
          have h1 : ‖y‖ ≤ (m : ℝ) := (Nat.le_ceil ‖y‖).trans (Nat.cast_le.2 hm)
          dsimp only [ηseq]; linarith
        rw [(ηseq m).one_of_mem_closedBall hball, one_mul]
    have hfull : (∫ y : H, (d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2) / g y) +
        2 * (∫ y : H, a y * (d y / g y)) ≤ (perimeter volume ⊤ s).toReal :=
      le_of_tendsto (hη_lim.add tendsto_const_nhds) (.of_forall fun m ↦ heta (ηseq m))
    -- Apply Cauchy–Schwarz to bound `(∫ a √d)²` by `(∫ a d / g) (∫ a g)`.
    have hag_pt (y : H) : a y * g y ≤ d y + ‖fderiv ℝ w y‖ + δ * a y := by
      have hg_le : g y ≤ d y + ‖fderiv ℝ w y‖ + δ := by
        rw [Real.sqrt_le_left (by linarith [(hd_mem y).1, opNorm_nonneg (fderiv ℝ w y), hδ])]
        nlinarith [(hd_mem y).1, opNorm_nonneg (fderiv ℝ w y), hδ]
      nlinarith [mul_le_mul_of_nonneg_left hg_le (ha_mem y).1, (ha_mem y).2, (hd_mem y).1,
        opNorm_nonneg (fderiv ℝ w y)]
    have hf1_int : Integrable (fun y : H ↦ a y * (d y / g y)) volume :=
      ha_int.mul_bdd (c := 1) (hd_smooth.continuous.div hg_smooth.continuous
        fun y ↦ (hg_pos y).ne').aestronglyMeasurable
        (.of_forall fun y ↦ by rw [Real.norm_of_nonneg (hdg_mem y).1]; exact (hdg_mem y).2)
    have hdg_int : Integrable (fun y : H ↦ d y + ‖fderiv ℝ w y‖) volume := hd_int.add hgradW_int
    have hf2_int : Integrable (fun y : H ↦ a y * g y) volume :=
      (hdg_int.add (ha_int.const_mul δ)).mono'
        (ha_smooth.continuous.mul hg_smooth.continuous).aestronglyMeasurable
        (.of_forall fun y ↦ by
          rw [Real.norm_of_nonneg (mul_nonneg (ha_mem y).1 (hg_pos y).le)]; exact hag_pt y)
    have hmem2 {f : H → ℝ} (hf : Integrable f volume) (h0 : ∀ y, 0 ≤ f y) :
        MemLp (fun y ↦ √(f y)) 2 volume :=
      (memLp_two_iff_integrable_sq
        (Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable)).2
        (hf.congr (.of_forall fun y ↦ (Real.sq_sqrt (h0 y)).symm))
    have hcs := sq_integral_mul_le_integral_sq_mul_integral_sq
      (hmem2 hf1_int fun y ↦ mul_nonneg (ha_mem y).1 (hdg_mem y).1)
      (hmem2 hf2_int fun y ↦ mul_nonneg (ha_mem y).1 (hg_pos y).le)
    rw [show (fun y : H ↦ √(a y * (d y / g y)) * √(a y * g y)) = fun y ↦ a y * √(d y) from
          funext fun y ↦ by
            rw [← Real.sqrt_mul (mul_nonneg (ha_mem y).1 (hdg_mem y).1),
              show a y * (d y / g y) * (a y * g y) = a y ^ 2 * d y by field_simp [(hg_pos y).ne'],
              Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (ha_mem y).1],
      show (fun y : H ↦ √(a y * (d y / g y)) ^ 2) = fun y ↦ a y * (d y / g y) from
        funext fun y ↦ Real.sq_sqrt (mul_nonneg (ha_mem y).1 (hdg_mem y).1),
      show (fun y : H ↦ √(a y * g y) ^ 2) = fun y ↦ a y * g y from
        funext fun y ↦ Real.sq_sqrt (mul_nonneg (ha_mem y).1 (hg_pos y).le)] at hcs
    have hag_le : ∫ y : H, a y * g y ≤ Mδ := by
      calc ∫ y : H, a y * g y
          ≤ ∫ y : H, (d y + ‖fderiv ℝ w y‖ + δ * a y) :=
            integral_mono hf2_int (hdg_int.add (ha_int.const_mul δ)) hag_pt
        _ = (∫ y : H, d y) + (∫ y : H, ‖fderiv ℝ w y‖) + δ * ∫ y : H, a y := by
            rw [integral_add hdg_int (ha_int.const_mul δ), integral_add hd_int hgradW_int,
              integral_const_mul]
        _ ≤ Mδ := by rw [hd_int_eq, ha_int_eq]; dsimp [Mδ, M]; linarith
    have hcs' : (∫ y : H, a y * √(d y)) ^ 2 ≤ (∫ y : H, a y * (d y / g y)) * Mδ :=
      hcs.trans (mul_le_mul_of_nonneg_left hag_le
        (integral_nonneg fun y ↦ mul_nonneg (ha_mem y).1 (hdg_mem y).1))
    nlinarith [mul_le_mul_of_nonneg_left hfull (show 0 ≤ Mδ by dsimp [Mδ, M]; positivity)]
  -- Pass to `δ = 1 / (k + 1) → 0⁺` by dominated convergence.
  let δseq : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have hδpos (k : ℕ) : 0 < δseq k := by positivity
  have hδlim : Tendsto δseq atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hM_lim : Tendsto (fun k ↦ M + δseq k * volume.real A) atTop (𝓝 M) := by
    simpa only [zero_mul, add_zero] using (hδlim.mul_const (volume.real A)).const_add M
  have hint_lim : Tendsto
      (fun k ↦ ∫ y : H, (d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2) /
        √(d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2 + δseq k ^ 2))
      atTop (𝓝 (∫ y : H, √(d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2))) := by
    refine tendsto_integral_of_dominated_convergence (fun y ↦ d y + ‖fderiv ℝ w y‖)
      (fun k ↦ (((hd_smooth.continuous.pow 2).add (hgradW_cont.pow 2)).div
        (Real.continuous_sqrt.comp (((hd_smooth.continuous.pow 2).add (hgradW_cont.pow 2)).add
          continuous_const)) fun y ↦ (Real.sqrt_pos.2 (add_pos_of_nonneg_of_pos
            (add_nonneg (sq_nonneg _) (sq_nonneg _))
            (sq_pos_of_pos (hδpos k)))).ne').aestronglyMeasurable)
      (hd_int.add hgradW_int)
      (fun k ↦ .of_forall fun y ↦ by
        rw [Real.norm_of_nonneg (by positivity)]
        exact hdiv_bound (hd_mem y).1 (opNorm_nonneg _) (hδpos k))
      (.of_forall fun y ↦ ?_)
    set x : ℝ := d y ^ 2 + ‖fderiv ℝ w y‖ ^ 2
    rcases eq_or_lt_of_le (show 0 ≤ x by positivity) with hx0 | hxpos
    · simp [← hx0]
    · have hden : Tendsto (fun k ↦ √(x + δseq k ^ 2)) atTop (𝓝 √x) :=
        (Real.continuous_sqrt.tendsto x).comp <| by
          simpa only [zero_pow two_ne_zero, add_zero] using (hδlim.pow 2).const_add x
      have hq := (tendsto_const_nhds (x := x)).div hden (Real.sqrt_pos.2 hxpos).ne'
      rwa [show x / √x = √x by rw [div_eq_iff (Real.sqrt_pos.2 hxpos).ne',
        Real.mul_self_sqrt hxpos.le]] at hq
  exact le_of_tendsto_of_tendsto ((hM_lim.mul hint_lim).add tendsto_const_nhds)
    (hM_lim.mul_const (perimeter volume ⊤ s).toReal) (.of_forall fun k ↦ hdelta (hδpos k))

end

end MollifiedExcess

end MeasureTheory.NullMeasurableSet
