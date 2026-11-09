/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.LConvolution
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Convolution.Young
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Convolution with the Bessel weight `(1 + ‖ξ‖ ^ 2) ^ (s / 2)`

Write `⟨ξ⟩ = (1 + ‖ξ‖ ^ 2) ^ (1 / 2)`. For `0 ≤ s`, the functions `v ∈ L¹` with
`⟨ξ⟩ ^ s v ∈ L²` are closed under convolution
(`TauCeti.memLp_one_add_norm_sq_rpow_mul_convolution`), with the bound

`‖⟨·⟩ ^ s (v₁ ⋆ v₂)‖₂ ≤ 2 ^ s (‖v₂‖₁ ‖⟨·⟩ ^ s v₁‖₂ + ‖v₁‖₁ ‖⟨·⟩ ^ s v₂‖₂)`

(`TauCeti.eLpNorm_one_add_norm_sq_rpow_mul_convolution_le`). Peetre's inequality
`⟨ξ⟩ ^ s ≤ 2 ^ s (⟨η⟩ ^ s + ⟨ξ - η⟩ ^ s)` (`TauCeti.one_add_norm_add_sq_rpow_le`) gives the
pointwise bound

`⟨ξ⟩ ^ s |v₁ ⋆ v₂| ≤ 2 ^ s (|v₂| ⋆ (⟨·⟩ ^ s |v₁|) + |v₁| ⋆ (⟨·⟩ ^ s |v₂|))`

(`TauCeti.enorm_one_add_norm_sq_rpow_mul_convolution_le`), and each convolution on the right is
that of an `L¹` function with an `L²` function, which lies in `L²` by Young's inequality
(`MeasureTheory.eLpNorm_lconvolution_le`).

This is the Fourier-side estimate behind the algebra property of the Sobolev spaces `H^s(ℝⁿ)`,
`s > n / 2`.

## References

* M. E. Taylor, *Partial Differential Equations III: Nonlinear Equations*, 2nd ed., Applied
  Mathematical Sciences 117, Springer, 2011, Chapter 13, proof of Proposition 3.7.
-/

public section

noncomputable section

open MeasureTheory ContinuousLinearMap
open scoped ENNReal Convolution

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

namespace TauCeti

omit [MeasurableSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The norm of the complexified Bessel weight `(1 + ‖x‖ ^ 2) ^ (s / 2)`. -/
@[simp]
theorem enorm_one_add_norm_sq_rpow (s : ℝ) (x : E) :
    ‖(((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)‖ₑ = ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (s / 2)) := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-- The pointwise form of the weighted convolution estimate: Peetre's inequality splits the
weight `(1 + ‖x‖ ^ 2) ^ (s / 2)` of `f ⋆ g` at `x` between the two factors. -/
theorem enorm_one_add_norm_sq_rpow_mul_convolution_le {s : ℝ} (hs : 0 ≤ s)
    {f g : E → ℂ} (hwf : AEStronglyMeasurable (fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * f x))
    (hg : AEStronglyMeasurable g) (x : E) :
    ‖(((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (f ⋆[mul ℂ ℂ] g) x‖ₑ ≤
      ENNReal.ofReal (2 ^ s) *
        (((fun y => ‖g y‖ₑ) ⋆ₗ fun y => ‖(((1 + ‖y‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * f y‖ₑ) x +
          ((fun y => ‖f y‖ₑ) ⋆ₗ fun y => ‖(((1 + ‖y‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * g y‖ₑ) x) := by
  set w : E → ℂ := fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) with hw_def
  set a : E → ℝ≥0∞ := fun y => ‖f y‖ₑ
  set b : E → ℝ≥0∞ := fun y => ‖g y‖ₑ
  set A : E → ℝ≥0∞ := fun y => ‖w y * f y‖ₑ
  set B : E → ℝ≥0∞ := fun y => ‖w y * g y‖ₑ
  set c : ℝ≥0∞ := ENNReal.ofReal (2 ^ s)
  have hcomm : (b ⋆ₗ A) x = ∫⁻ t, A t * b (x - t) := by
    rw [lconvolution_comm, lconvolution_def]
    simp only [neg_add_eq_sub]
  -- Peetre's inequality at `x = t + (x - t)`.
  have hweight : ∀ t, ‖w x‖ₑ * (a t * b (x - t)) ≤ c * (A t * b (x - t) + a t * B (x - t)) := by
    intro t
    have hp := one_add_norm_add_sq_rpow_le hs t (x - t)
    rw [add_sub_cancel] at hp
    have hle : ‖w x‖ₑ ≤ c * (‖w t‖ₑ + ‖w (x - t)‖ₑ) := by
      simp only [hw_def, enorm_one_add_norm_sq_rpow, c]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal hp
    calc ‖w x‖ₑ * (a t * b (x - t))
        ≤ c * (‖w t‖ₑ + ‖w (x - t)‖ₑ) * (a t * b (x - t)) := by gcongr
      _ = c * (A t * b (x - t) + a t * B (x - t)) := by
        simp only [A, B, a, b, enorm_mul]
        ring
  calc ‖w x * (f ⋆[mul ℂ ℂ] g) x‖ₑ
      ≤ ‖w x‖ₑ * ∫⁻ t, a t * b (x - t) := by
        rw [enorm_mul, convolution_def]
        gcongr
        refine (enorm_integral_le_lintegral_enorm _).trans_eq ?_
        simp only [mul_apply', enorm_mul, a, b]
    _ = ∫⁻ t, ‖w x‖ₑ * (a t * b (x - t)) :=
        (lintegral_const_mul' ‖w x‖ₑ (fun t => a t * b (x - t)) enorm_ne_top).symm
    _ ≤ ∫⁻ t, c * (A t * b (x - t) + a t * B (x - t)) := lintegral_mono hweight
    _ = c * ((b ⋆ₗ A) x + (a ⋆ₗ B) x) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left' (f := fun t => A t * b (x - t)) (hwf.enorm.mul
          (hg.enorm.comp_quasiMeasurePreserving
            (quasiMeasurePreserving_sub_left_of_right_invariant volume x))),
        hcomm, lconvolution_def]
      simp only [neg_add_eq_sub, c]

/-- **The weighted convolution estimate.** For `0 ≤ s`, the weight
`w(ξ) = (1 + ‖ξ‖ ^ 2) ^ (s / 2)` satisfies
`‖w (f ⋆ g)‖₂ ≤ 2 ^ s (‖g‖₁ ‖w f‖₂ + ‖f‖₁ ‖w g‖₂)`. -/
theorem eLpNorm_one_add_norm_sq_rpow_mul_convolution_le {s : ℝ} (hs : 0 ≤ s) {f g : E → ℂ}
    (hf : AEStronglyMeasurable f) (hg : AEStronglyMeasurable g) :
    eLpNorm (fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (f ⋆[mul ℂ ℂ] g) x) 2 ≤
      ENNReal.ofReal (2 ^ s) *
        (eLpNorm g 1 * eLpNorm (fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * f x) 2 +
          eLpNorm f 1 * eLpNorm (fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * g x) 2) := by
  have hwc : Continuous fun x : E => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) := by fun_prop
  have hwf : AEStronglyMeasurable fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * f x :=
    hwc.aestronglyMeasurable.mul hf
  have hwg : AEStronglyMeasurable fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * g x :=
    hwc.aestronglyMeasurable.mul hg
  set X := (fun y => ‖g y‖ₑ) ⋆ₗ fun y => ‖(((1 + ‖y‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * f y‖ₑ
  set Y := (fun y => ‖f y‖ₑ) ⋆ₗ fun y => ‖(((1 + ‖y‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * g y‖ₑ
  have hX : AEMeasurable X := aemeasurable_lconvolution hg.enorm hwf.enorm
  have hY : AEMeasurable Y := aemeasurable_lconvolution hf.enorm hwg.enorm
  -- Integrate the pointwise bound, then apply Young's inequality to `X` and `Y`.
  calc eLpNorm (fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (f ⋆[mul ℂ ℂ] g) x) 2
      ≤ eLpNorm (fun x => ENNReal.ofReal (2 ^ s) * (X x + Y x)) 2 :=
        eLpNorm_mono_enorm
          (f := fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (f ⋆[mul ℂ ℂ] g) x)
          (g := fun x => ENNReal.ofReal (2 ^ s) * (X x + Y x))
          (hwc.aestronglyMeasurable.mul (hf.convolution (mul ℂ ℂ) hg)) fun x => by
            rw [enorm_eq_self]
            exact enorm_one_add_norm_sq_rpow_mul_convolution_le hs hwf hg x
    _ = ENNReal.ofReal (2 ^ s) * eLpNorm (X + Y) 2 :=
        eLpNorm_const_mul_ennreal (hX.add hY).aestronglyMeasurable
    _ ≤ ENNReal.ofReal (2 ^ s) * (eLpNorm X 2 + eLpNorm Y 2) := by
        gcongr
        exact eLpNorm_add_le one_le_two
    _ ≤ ENNReal.ofReal (2 ^ s) *
        (eLpNorm g 1 * eLpNorm (fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * f x) 2 +
          eLpNorm f 1 * eLpNorm (fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * g x) 2) := by
        rw [eLpNorm_one_eq_lintegral_enorm hg, eLpNorm_one_eq_lintegral_enorm hf,
          ← eLpNorm_enorm _ hwf, ← eLpNorm_enorm _ hwg]
        gcongr
        · exact eLpNorm_lconvolution_le hg.enorm hwf.enorm
        · exact eLpNorm_lconvolution_le hf.enorm hwg.enorm

/-- For `0 ≤ s`, if `f` and `g` are integrable and `(1 + ‖ξ‖ ^ 2) ^ (s / 2) f` and
`(1 + ‖ξ‖ ^ 2) ^ (s / 2) g` are square integrable, then so is
`(1 + ‖ξ‖ ^ 2) ^ (s / 2) (f ⋆ g)`. -/
theorem memLp_one_add_norm_sq_rpow_mul_convolution {s : ℝ} (hs : 0 ≤ s) {f g : E → ℂ}
    (hf : Integrable f) (hg : Integrable g)
    (hwf : MemLp (fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * f x) 2)
    (hwg : MemLp (fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * g x) 2) :
    MemLp (fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (f ⋆[mul ℂ ℂ] g) x) 2 := by
  refine (eLpNorm_one_add_norm_sq_rpow_mul_convolution_le hs hf.aestronglyMeasurable
    hg.aestronglyMeasurable).trans_lt ?_
  have h1 := (memLp_one_iff_integrable.2 hf).eLpNorm_lt_top
  have h2 := (memLp_one_iff_integrable.2 hg).eLpNorm_lt_top
  have h3 := hwf.eLpNorm_lt_top
  have h4 := hwg.eLpNorm_lt_top
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top h2 h3, ENNReal.mul_lt_top h1 h4⟩)

end TauCeti
