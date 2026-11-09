/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.LConvolution
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.WithDensity
import TauCeti.MeasureTheory.Integral.MinkowskiIntegral

/-!
# Young's inequality for convolution

This file proves two forms of Young's inequality for convolution with an integrable function.

## `L¹ ⋆ L² ⊆ L²` for the Lebesgue-integral convolution

Let `μ` be a left-invariant measure on a measurable additive group and let
`(f ⋆ₗ[μ] g) x = ∫⁻ y, f y * g (-y + x) ∂μ` be the convolution of extended nonnegative functions
(`MeasureTheory.lconvolution`). Young's inequality in the case `L¹ ⋆ L² ⊆ L²` reads

`∫⁻ (f ⋆ₗ[μ] g) ^ 2 ≤ (∫⁻ f) ^ 2 * ∫⁻ g ^ 2`

(`MeasureTheory.lintegral_lconvolution_sq_le`), that is `‖f ⋆ₗ[μ] g‖₂ ≤ (∫⁻ f) ‖g‖₂`
(`MeasureTheory.eLpNorm_lconvolution_le`). It follows from the pointwise Cauchy–Schwarz
inequality for the measure with density `f`,

`(f ⋆ₗ[μ] g) x ^ 2 ≤ (∫⁻ f) * ∫⁻ y, f y * g (-y + x) ^ 2`

(`MeasureTheory.lconvolution_sq_le`), by integrating in `x`, exchanging the integrals and using
the left invariance of `μ`. Being stated for extended nonnegative functions, neither inequality
needs any integrability hypothesis.

The norm of a convolution of Bochner-integrable functions is bounded pointwise by the convolution
of their norms, so this inequality also bounds the `L²` norm of `f ⋆ g` for `f ∈ L¹` and `g ∈ L²`.

## `L¹ ⋆ Lᵖ ⊆ Lᵖ` for the Bochner convolution

Let `μ` be a σ-finite right-invariant measure on a measurable additive group `G`, and let
`L : E →L[𝕜] E' →L[𝕜] F` be a continuous bilinear map. For `1 ≤ p ≤ ∞`, an integrable `f` and
`g ∈ Lᵖ(μ)`, the convolution `(f ⋆[L] g)(x) = ∫ L (f t) (g (x - t)) dμ(t)` satisfies

`‖f ⋆[L] g‖_p ≤ ‖L‖ ‖f‖₁ ‖g‖_p`.

The statement is in `ℝ≥0∞` (`MeasureTheory.eLpNorm_convolution_le`), so it needs no
integrability hypotheses: it is informative exactly when the right side is finite. For `p < ∞`
it is Minkowski's integral inequality (`TauCeti.lintegral_Lp_lintegral_le`) applied to the
pointwise bound `‖(f ⋆[L] g)(x)‖ ≤ ∫ ‖L‖ ‖f t‖ ‖g (x - t)‖ dμ(t)`, together with the translation
invariance `‖g (· - t)‖_p = ‖g‖_p`. For `p = ∞`, `‖g (x - t)‖ ≤ ‖g‖_∞` for almost every `t`.

The kernel `f` and the bilinear map `L` are arbitrary, so the inequality applies to complex
kernels acting on vector-valued functions through `ContinuousLinearMap.lsmul`, as for the
kernel `𝓕⁻ σ` of a Fourier multiplier with Schwartz symbol `σ`.

## Main declarations

* `MeasureTheory.lconvolution_sq_le`: pointwise Cauchy–Schwarz for `f ⋆ₗ[μ] g`.
* `MeasureTheory.lintegral_lconvolution_sq_le`, `MeasureTheory.eLpNorm_lconvolution_le`: Young's
  inequality `L¹ ⋆ L² ⊆ L²`.
* `MeasureTheory.enorm_convolution_le_lintegral`: the pointwise bound for `f ⋆[L, μ] g`.
* `MeasureTheory.eLpNorm_convolution_le`: Young's inequality `‖f ⋆[L] g‖_p ≤ ‖L‖ ‖f‖₁ ‖g‖_p`.

## References

* E. H. Lieb and M. Loss, *Analysis*, 2nd ed., Graduate Studies in Mathematics 14, AMS, 2001,
  Theorem 4.2.
* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed.,
  Proposition 8.7.
-/

public section

open scoped ENNReal

namespace MeasureTheory

section LConvolution

variable {G : Type*} {mG : MeasurableSpace G} [AddGroup G] [MeasurableAdd₂ G] [MeasurableNeg G]
  {μ : Measure G} [SFinite μ] [μ.IsAddLeftInvariant] {f g : G → ℝ≥0∞}

/-- **Pointwise Cauchy–Schwarz for a convolution.** Cauchy–Schwarz for the measure with density
`f` gives `(f ⋆ₗ[μ] g) x ^ 2 ≤ (∫⁻ f) * ∫⁻ y, f y * g (-y + x) ^ 2`. -/
theorem lconvolution_sq_le (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (x : G) :
    (f ⋆ₗ[μ] g) x ^ 2 ≤ (∫⁻ y, f y ∂μ) * ∫⁻ y, f y * g (-y + x) ^ 2 ∂μ := by
  have hgx : AEMeasurable (fun y => g (-y + x)) μ := by fun_prop
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.withDensity f) Real.HolderConjugate.two_two
    (f := fun _ => 1) aemeasurable_const (hgx.mono_ac (withDensity_absolutelyContinuous _ _))
  simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow] at hcs
  rw [lintegral_withDensity_eq_lintegral_mul₀ hf hgx, lintegral_one, withDensity_apply _
    MeasurableSet.univ, Measure.restrict_univ, lintegral_withDensity_eq_lintegral_mul₀ hf
    (hgx.pow_const 2)] at hcs
  calc (f ⋆ₗ[μ] g) x ^ 2
      ≤ ((∫⁻ y, f y ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ y, f y * g (-y + x) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ))
          ^ 2 := by
        rw [lconvolution_def]
        gcongr
        exact hcs
    _ = (∫⁻ y, f y ∂μ) * ∫⁻ y, f y * g (-y + x) ^ 2 ∂μ := by
      rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
        ← ENNReal.rpow_mul]
      norm_num

/-- **Young's inequality `L¹ ⋆ L² ⊆ L²`.** For extended nonnegative functions on a group with a
left-invariant measure, `∫⁻ (f ⋆ₗ[μ] g) ^ 2 ≤ (∫⁻ f) ^ 2 * ∫⁻ g ^ 2`. -/
theorem lintegral_lconvolution_sq_le (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ x, (f ⋆ₗ[μ] g) x ^ 2 ∂μ ≤ (∫⁻ y, f y ∂μ) ^ 2 * ∫⁻ x, g x ^ 2 ∂μ := by
  calc ∫⁻ x, (f ⋆ₗ[μ] g) x ^ 2 ∂μ
      ≤ ∫⁻ x, (∫⁻ y, f y ∂μ) * ∫⁻ y, f y * g (-y + x) ^ 2 ∂μ ∂μ :=
        lintegral_mono fun x => lconvolution_sq_le hf hg x
    _ = (∫⁻ y, f y ∂μ) * ∫⁻ y, ∫⁻ x, f y * g (-y + x) ^ 2 ∂μ ∂μ := by
      rw [lintegral_const_mul'' _ (by fun_prop), lintegral_lintegral_swap (by fun_prop)]
    _ = (∫⁻ y, f y ∂μ) * ∫⁻ y, f y * ∫⁻ x, g x ^ 2 ∂μ ∂μ := by
      congr 1
      refine lintegral_congr fun y => ?_
      rw [lintegral_add_left_eq_self (fun x => f y * g x ^ 2) (-y),
        lintegral_const_mul'' _ (hg.pow_const 2)]
    _ = (∫⁻ y, f y ∂μ) ^ 2 * ∫⁻ x, g x ^ 2 ∂μ := by
      rw [lintegral_mul_const'' _ hf, sq, mul_assoc]

/-- **Young's inequality `L¹ ⋆ L² ⊆ L²`** in norm form: `‖f ⋆ₗ[μ] g‖₂ ≤ (∫⁻ f) ‖g‖₂`. -/
theorem eLpNorm_lconvolution_le (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    eLpNorm (f ⋆ₗ[μ] g) 2 μ ≤ (∫⁻ y, f y ∂μ) * eLpNorm g 2 μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      (aemeasurable_lconvolution hf hg).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hg.aestronglyMeasurable]
  simp only [enorm_eq_self, ENNReal.toReal_ofNat, ENNReal.rpow_two]
  calc (∫⁻ x, (f ⋆ₗ[μ] g) x ^ 2 ∂μ) ^ (1 / 2 : ℝ)
      ≤ ((∫⁻ y, f y ∂μ) ^ 2 * ∫⁻ x, g x ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
        gcongr
        exact lintegral_lconvolution_sq_le hf hg
    _ = (∫⁻ y, f y ∂μ) * (∫⁻ x, g x ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]
        norm_num

end LConvolution

section Convolution

open Measure
open scoped Convolution

variable {𝕜 G E E' F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
  (L : E →L[𝕜] E' →L[𝕜] F) {f : G → E} {g : G → E'}

/-- The pointwise bound behind Young's inequality:
`‖(f ⋆[L] g)(x)‖ ≤ ∫ ‖L‖ ‖f t‖ ‖g (x - t)‖ dμ(t)`, in extended nonnegative form. -/
theorem enorm_convolution_le_lintegral [Sub G] [MeasurableSpace G] (μ : Measure G) (x : G) :
    ‖(f ⋆[L, μ] g) x‖ₑ ≤ ∫⁻ t, ‖L‖ₑ * ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ :=
  (enorm_integral_le_lintegral_enorm _).trans <| lintegral_mono fun _ ↦ L.le_opENorm₂ _ _

variable [AddGroup G] [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
  {μ : Measure G} [SigmaFinite μ] [IsAddRightInvariant μ]

/-- **Young's inequality** for convolution with an integrable function: for `1 ≤ p ≤ ∞`,
`‖f ⋆[L] g‖_p ≤ ‖L‖ ‖f‖₁ ‖g‖_p`. -/
theorem eLpNorm_convolution_le (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (f ⋆[L, μ] g) p μ ≤ ‖L‖ₑ * eLpNorm f 1 μ * eLpNorm g p μ := by
  rw [eLpNorm_one_eq_lintegral_enorm hf]
  rcases eq_or_ne p ∞ with rfl | hp_top
  · -- For `p = ∞`, `‖g (x - t)‖ ≤ ‖g‖_∞` for almost every `t`, for every `x`.
    rw [eLpNorm_exponent_top hg, eLpNorm_exponent_top (hf.convolution L hg)]
    refine eLpNormEssSup_le_of_ae_enorm_bound <| Filter.Eventually.of_forall fun x ↦
      (enorm_convolution_le_lintegral L μ x).trans ?_
    have hgx : ∀ᵐ t ∂μ, ‖g (x - t)‖ₑ ≤ eLpNormEssSup g μ :=
      (quasiMeasurePreserving_sub_left_of_right_invariant μ x).ae ae_le_eLpNormEssSup
    calc ∫⁻ t, ‖L‖ₑ * ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ
        ≤ ∫⁻ t, ‖L‖ₑ * ‖f t‖ₑ * eLpNormEssSup g μ ∂μ :=
          lintegral_mono_ae <| hgx.mono fun t ht ↦ by gcongr
      _ = ‖L‖ₑ * (∫⁻ t, ‖f t‖ₑ ∂μ) * eLpNormEssSup g μ := by
          rw [lintegral_mul_const'' _ (hf.enorm.const_mul _),
            lintegral_const_mul'' _ hf.enorm]
  -- For `p < ∞`, Minkowski's integral inequality moves the `Lᵖ` norm inside the integral.
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hr : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp_top hp
  have hr0 : 0 < p.toReal := zero_lt_one.trans_le hr
  set r := p.toReal
  have hmeas : AEMeasurable (Function.uncurry fun x t ↦ ‖L‖ₑ * ‖f t‖ₑ * ‖g (x - t)‖ₑ)
      (μ.prod μ) :=
    (aemeasurable_const.mul hf.enorm.comp_snd).mul
      (hg.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant μ μ)).enorm
  have hg_tr (t : G) : ∫⁻ x, ‖g (x - t)‖ₑ ^ r ∂μ = ∫⁻ x, ‖g x‖ₑ ^ r ∂μ :=
    lintegral_sub_right_eq_self (fun x ↦ ‖g x‖ₑ ^ r) t
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top (hf.convolution L hg),
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hg]
  calc (∫⁻ x, ‖(f ⋆[L, μ] g) x‖ₑ ^ r ∂μ) ^ (1 / r)
      ≤ (∫⁻ x, (∫⁻ t, ‖L‖ₑ * ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ) ^ r ∂μ) ^ (1 / r) := by
        gcongr with x
        exact enorm_convolution_le_lintegral L μ x
    _ ≤ ∫⁻ t, (∫⁻ x, (‖L‖ₑ * ‖f t‖ₑ * ‖g (x - t)‖ₑ) ^ r ∂μ) ^ (1 / r) ∂μ :=
        TauCeti.lintegral_Lp_lintegral_le hmeas hr
    _ = ∫⁻ t, ‖L‖ₑ * ‖f t‖ₑ * (∫⁻ x, ‖g x‖ₑ ^ r ∂μ) ^ (1 / r) ∂μ := by
        refine lintegral_congr fun t ↦ ?_
        have hne : (‖L‖ₑ * ‖f t‖ₑ) ^ r ≠ ∞ :=
          ENNReal.rpow_ne_top_of_nonneg hr0.le (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)
        have h : ∫⁻ x, (‖L‖ₑ * ‖f t‖ₑ * ‖g (x - t)‖ₑ) ^ r ∂μ =
            (‖L‖ₑ * ‖f t‖ₑ) ^ r * ∫⁻ x, ‖g x‖ₑ ^ r ∂μ := by
          rw [← hg_tr t, ← lintegral_const_mul' _ _ hne]
          exact lintegral_congr fun x ↦ ENNReal.mul_rpow_of_nonneg _ _ hr0.le
        rw [h, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hr0.ne', ENNReal.rpow_one]
    _ = ‖L‖ₑ * (∫⁻ t, ‖f t‖ₑ ∂μ) * (∫⁻ x, ‖g x‖ₑ ^ r ∂μ) ^ (1 / r) := by
        rw [lintegral_mul_const'' _ (hf.enorm.const_mul _),
          lintegral_const_mul'' _ hf.enorm]

end Convolution

end MeasureTheory
