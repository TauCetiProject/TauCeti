/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.LConvolution
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.WithDensity
import TauCeti.MeasureTheory.Integral.MinkowskiIntegral
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# Young's inequality for convolution

This file proves three forms of Young's inequality for convolution.

## `L¹ ⋆ L² ⊆ L²` for the Lebesgue-integral convolution

Let `μ` be a left-invariant measure on a measurable additive group and let
`(f ⋆ₗ[μ] g) x = ∫⁻ y, f y * g (-y + x) ∂μ` be the convolution of extended nonnegative functions
(`MeasureTheory.lconvolution`). Young's inequality in the case `L¹ ⋆ L² ⊆ L²` reads

`∫⁻ (f ⋆ₗ[μ] g) ^ 2 ≤ (∫⁻ f) ^ 2 * ∫⁻ g ^ 2`

(`MeasureTheory.lintegral_lconvolution_sq_le`). It follows from the pointwise Cauchy–Schwarz
inequality for the measure with density `f`,

`(f ⋆ₗ[μ] g) x ^ 2 ≤ (∫⁻ f) * ∫⁻ y, f y * g (-y + x) ^ 2`

(`MeasureTheory.lconvolution_sq_le`), by integrating in `x`, exchanging the integrals and using
the left invariance of `μ`. Being stated for extended nonnegative functions, neither inequality
needs any integrability hypothesis.

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

## `Lᵖ ⋆ Lʳ ⊆ Lᵠ` on commutative groups

On a commutative group whose measure is also invariant under negation, the general form of
**Young's convolution inequality** holds: for `1 ≤ p, r ≤ ∞` and `1/p + 1/r = 1 + 1/q`,

`‖f ⋆ₗ[μ] g‖_q ≤ ‖f‖_p ‖g‖_r`

(`MeasureTheory.eLpNorm_lconvolution_le`). For `q < ∞` this is Young's inequality for the
integral operator with kernel `(x, y) ↦ g (x - y)`, whose rows and columns all have the same
`Lʳ` norm as `g` (`TauCeti.lintegral_rpow_lintegral_mul_le_of_inv_add_inv_eq`); for `q = ∞` it is
Hölder's inequality at each point.

The norm of a convolution of Bochner-integrable functions is bounded pointwise by the convolution
of their norms, so this inequality also bounds the `Lᵠ` norm of `f ⋆[L] g`
(`MeasureTheory.eLpNorm_convolution_le_of_inv_add_inv_eq`).

## Main declarations

* `MeasureTheory.lconvolution_sq_le`: pointwise Cauchy–Schwarz for `f ⋆ₗ[μ] g`.
* `MeasureTheory.lintegral_lconvolution_sq_le`: Young's inequality `L¹ ⋆ L² ⊆ L²`.
* `MeasureTheory.enorm_convolution_le_lintegral`: the pointwise bound for `f ⋆[L, μ] g`.
* `MeasureTheory.eLpNorm_convolution_le`: Young's inequality `‖f ⋆[L] g‖_p ≤ ‖L‖ ‖f‖₁ ‖g‖_p`.
* `MeasureTheory.eLpNorm_lconvolution_le`: Young's inequality `Lᵖ ⋆ Lʳ ⊆ Lᵠ`.
* `MeasureTheory.eLpNorm_convolution_le_of_inv_add_inv_eq`: the same bound for the convolution
  `f ⋆[L, μ] g` of vector-valued functions along a continuous bilinear map `L`.

## References

* E. H. Lieb and M. Loss, *Analysis*, 2nd ed., Graduate Studies in Mathematics 14, AMS, 2001,
  Theorem 4.2.
* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed.,
  Propositions 8.7 and 8.9.
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

namespace MeasureTheory

variable {G : Type*} {mG : MeasurableSpace G} [AddCommGroup G] [MeasurableAdd₂ G] [MeasurableNeg G]
  {μ : Measure G} [SFinite μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant] {f g : G → ℝ≥0∞}

omit [SFinite μ] in
/-- In the convolution `(f ⋆ₗ[μ] g) x = ∫⁻ y, f y * g (x - y)`, every translate `y ↦ g (x - y)`
of the second factor has the same `Lʳ` norm as `g`. -/
private theorem eLpNorm_comp_sub_left (hg : AEMeasurable g μ) (r : ℝ≥0∞) (x : G) :
    eLpNorm (fun y ↦ g (-y + x)) r μ = eLpNorm g r μ := by
  simp_rw [neg_add_eq_sub]
  exact eLpNorm_comp_measurePreserving hg.aestronglyMeasurable
    (Measure.measurePreserving_sub_left μ x)

/-- Young's inequality with `q = ∞`, which is Hölder's inequality at each point. -/
private theorem eLpNorm_lconvolution_top_le {p r : ℝ≥0∞} (hpr : p⁻¹ + r⁻¹ = 1)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    eLpNorm (f ⋆ₗ[μ] g) ∞ μ ≤ eLpNorm f p μ * eLpNorm g r μ := by
  have : ENNReal.HolderTriple p r 1 := ⟨by rw [hpr, inv_one]⟩
  rw [eLpNorm_exponent_top (aemeasurable_lconvolution hf hg).aestronglyMeasurable]
  refine eLpNormEssSup_le_of_ae_enorm_bound (Filter.Eventually.of_forall fun x ↦ ?_)
  have hgx : AEMeasurable (fun y ↦ g (-y + x)) μ := by
    simp_rw [neg_add_eq_sub]
    exact hg.comp_quasiMeasurePreserving
      (Measure.measurePreserving_sub_left μ x).quasiMeasurePreserving
  calc ‖(f ⋆ₗ[μ] g) x‖ₑ = eLpNorm (fun y ↦ f y * g (-y + x)) 1 μ := by
        rw [eLpNorm_one_eq_lintegral_enorm (f := fun y ↦ f y * g (-y + x))
          (hf.mul hgx).aestronglyMeasurable]
        simp [lconvolution_def]
    _ ≤ 1 * eLpNorm f p μ * eLpNorm (fun y ↦ g (-y + x)) r μ :=
        eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm (· * ·) 1
          (fun hf hg ↦ (hf.aemeasurable.mul hg.aemeasurable).aestronglyMeasurable)
          hf.aestronglyMeasurable hgx.aestronglyMeasurable (Filter.Eventually.of_forall
            fun _ ↦ by simp)
    _ = eLpNorm f p μ * eLpNorm g r μ := by rw [one_mul, eLpNorm_comp_sub_left hg]

/-- Young's inequality with finite exponents, in terms of lower Lebesgue integrals: it is Young's
inequality for the integral operator with kernel `(x, y) ↦ g (x - y)`, whose rows and columns
are translates of `g` and of its reflection, so that all have the `Lʳ` norm of `g`. -/
private theorem lintegral_rpow_lconvolution_le {p q r : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q)
    (hpqr : p⁻¹ + r⁻¹ = 1 + q⁻¹) (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ x, (f ⋆ₗ[μ] g) x ^ q ∂μ) ^ (1 / q) ≤
      (∫⁻ y, f y ^ p ∂μ) ^ (1 / p) * (∫⁻ x, g x ^ r ∂μ) ^ (1 / r) := by
  have hq0 : 0 < q := by linarith
  set N := ∫⁻ x, g x ^ r ∂μ
  have hk : AEMeasurable (Function.uncurry fun x y ↦ g (-y + x)) (μ.prod μ) := by
    have : (Function.uncurry fun x y ↦ g (-y + x)) = g ∘ fun z : G × G ↦ z.1 - z.2 := by
      ext z
      simp [Function.uncurry, neg_add_eq_sub]
    rw [this]
    exact hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub μ μ)
  have hrow : ∀ x, ∫⁻ y, g (-y + x) ^ r ∂μ = N := fun x ↦ by
    simp_rw [neg_add_eq_sub]
    exact lintegral_sub_left_eq_self (fun z ↦ g z ^ r) x
  have hcol : ∀ y, ∫⁻ x, g (-y + x) ^ r ∂μ = N := fun y ↦
    lintegral_add_left_eq_self (fun z ↦ g z ^ r) (-y)
  have hyoung := TauCeti.lintegral_rpow_lintegral_mul_le_of_inv_add_inv_eq hk hf hp hpq hpqr
    (Filter.Eventually.of_forall fun x ↦ (hrow x).le)
    (Filter.Eventually.of_forall fun y ↦ (hcol y).le)
  calc (∫⁻ x, (f ⋆ₗ[μ] g) x ^ q ∂μ) ^ (1 / q)
      ≤ (N ^ (q * (1 - p⁻¹)) * N * (∫⁻ y, f y ^ p ∂μ) ^ (q / p)) ^ (1 / q) := by
        gcongr
        simpa only [lconvolution_def, mul_comm (f _)] using hyoung
    _ = (∫⁻ y, f y ^ p ∂μ) ^ (1 / p) * N ^ (1 / r) := by
        have ha : 0 ≤ q * (1 - p⁻¹) :=
          mul_nonneg hq0.le (sub_nonneg.2 (inv_le_one_of_one_le₀ hp))
        have hN : N ^ (q * (1 - p⁻¹)) * N = N ^ (q * (1 - p⁻¹) + 1) := by
          rw [ENNReal.rpow_add_of_nonneg _ _ ha zero_le_one, ENNReal.rpow_one]
        rw [hN, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul, mul_comm]
        have hr : r⁻¹ = 1 + q⁻¹ - p⁻¹ := by linarith
        congr 2
        · field_simp
        · rw [one_div r, hr]
          field_simp
          ring

/-- **Young's convolution inequality.** On a commutative group whose measure is invariant under
translation and negation, for `1 ≤ p, r ≤ ∞` and `1/p + 1/r = 1 + 1/q`, the convolution of
extended nonnegative functions satisfies `‖f ⋆ₗ[μ] g‖_q ≤ ‖f‖_p ‖g‖_r`. -/
theorem eLpNorm_lconvolution_le {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hpqr : p⁻¹ + r⁻¹ = 1 + q⁻¹) (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    eLpNorm (f ⋆ₗ[μ] g) q μ ≤ eLpNorm f p μ * eLpNorm g r μ := by
  have hp1 : p⁻¹ ≤ 1 := ENNReal.inv_le_one.2 hp
  have hr1 : r⁻¹ ≤ 1 := ENNReal.inv_le_one.2 hr
  rcases eq_or_ne q ∞ with rfl | hq
  · exact eLpNorm_lconvolution_top_le (by simpa using hpqr) hf hg
  have hq0 : q ≠ 0 := by
    rintro rfl
    have : p⁻¹ + r⁻¹ ≤ 2 := by simpa [one_add_one_eq_two] using add_le_add hp1 hr1
    simp [hpqr] at this
  -- All three exponents are finite: `q < ∞` forces `p⁻¹, r⁻¹ ≥ q⁻¹ > 0`.
  have hq1 : ¬ 1 + q⁻¹ ≤ 1 :=
    not_le.2 (ENNReal.lt_add_right ENNReal.one_ne_top (ENNReal.inv_ne_zero.2 hq))
  have hp_top : p ≠ ∞ := by
    rintro rfl
    exact hq1 (by simpa [← hpqr] using hr1)
  have hr_top : r ≠ ∞ := by
    rintro rfl
    exact hq1 (by simpa [← hpqr] using hp1)
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hr0 : r ≠ 0 := (zero_lt_one.trans_le hr).ne'
  have hp' : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp_top hp
  have hr' : 1 ≤ r.toReal := by simpa using ENNReal.toReal_mono hr_top hr
  have hpqr' : p.toReal⁻¹ + r.toReal⁻¹ = 1 + q.toReal⁻¹ := by
    have := congrArg ENNReal.toReal hpqr
    rwa [ENNReal.toReal_add (by simpa using hp0) (by simpa using hr0),
      ENNReal.toReal_add ENNReal.one_ne_top (by simpa using hq0), ENNReal.toReal_inv,
      ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_one] at this
  have hpq' : p.toReal ≤ q.toReal := by
    have : q.toReal⁻¹ ≤ p.toReal⁻¹ := by linarith [inv_le_one_of_one_le₀ hr']
    exact (inv_le_inv₀ (ENNReal.toReal_pos hq0 hq) (by linarith)).1 this
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq
      (aemeasurable_lconvolution hf hg).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hf.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hr_top hg.aestronglyMeasurable]
  simp only [enorm_eq_self]
  exact lintegral_rpow_lconvolution_le hp' hpq' hpqr' hf hg

open scoped Convolution in
/-- **Young's convolution inequality** for the convolution `f ⋆[L, μ] g` along a continuous
bilinear map `L`: for `1 ≤ p, r ≤ ∞` and `1/p + 1/r = 1 + 1/q`,
`‖f ⋆[L, μ] g‖_q ≤ ‖L‖ ‖f‖_p ‖g‖_r`. Where the integral defining the convolution does not
converge, its value is `0`, so no integrability hypothesis is needed. -/
theorem eLpNorm_convolution_le_of_inv_add_inv_eq {𝕜 E E' F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] (L : E →L[𝕜] E' →L[𝕜] F)
    {f : G → E} {g : G → E'} {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hpqr : p⁻¹ + r⁻¹ = 1 + q⁻¹) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    eLpNorm (f ⋆[L, μ] g) q μ ≤ ‖L‖ₑ * eLpNorm f p μ * eLpNorm g r μ := by
  have hpt : ∀ x, ‖(f ⋆[L, μ] g) x‖ₑ ≤
      ‖L‖ₑ * ‖((fun t ↦ ‖f t‖ₑ) ⋆ₗ[μ] fun t ↦ ‖g t‖ₑ) x‖ₑ := fun x ↦ by
    rw [convolution_def, enorm_eq_self, lconvolution_def, ← lintegral_const_mul' _ _ enorm_ne_top]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun t ↦ ?_)
    rw [neg_add_eq_sub, ← mul_assoc]
    exact ContinuousLinearMap.le_opENorm₂ L _ _
  calc eLpNorm (f ⋆[L, μ] g) q μ
      ≤ ‖L‖ₑ * eLpNorm ((fun t ↦ ‖f t‖ₑ) ⋆ₗ[μ] fun t ↦ ‖g t‖ₑ) q μ :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' q (hf.convolution L hg)
          (Filter.Eventually.of_forall hpt)
    _ ≤ ‖L‖ₑ * (eLpNorm (fun t ↦ ‖f t‖ₑ) p μ * eLpNorm (fun t ↦ ‖g t‖ₑ) r μ) := by
        gcongr
        exact eLpNorm_lconvolution_le hp hr hpqr hf.enorm hg.enorm
    _ = ‖L‖ₑ * eLpNorm f p μ * eLpNorm g r μ := by
        rw [eLpNorm_enorm f hf, eLpNorm_enorm g hg, mul_assoc]

end MeasureTheory
