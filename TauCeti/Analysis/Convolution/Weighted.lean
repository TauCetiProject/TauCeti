/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.LConvolution
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Convolution.Young
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Convolution with the Bessel weight `(1 + ‖ξ‖ ^ 2) ^ (s / 2)`

Write `⟨ξ⟩ = (1 + ‖ξ‖ ^ 2) ^ (1 / 2)`. For `0 ≤ s`, the functions `v ∈ L¹` with
`⟨ξ⟩ ^ s v ∈ L²` are closed under convolution
(`TauCeti.memLp_one_add_norm_sq_rpow_mul_convolution`). Peetre's inequality
`⟨ξ⟩ ^ s ≤ 2 ^ s (⟨η⟩ ^ s + ⟨ξ - η⟩ ^ s)` (`TauCeti.one_add_norm_add_sq_rpow_le`) gives the
pointwise bound

`⟨ξ⟩ ^ s |v₁ ⋆ v₂| ≤ 2 ^ s (|v₂| ⋆ (⟨·⟩ ^ s |v₁|) + |v₁| ⋆ (⟨·⟩ ^ s |v₂|))`

(`TauCeti.enorm_one_add_norm_sq_rpow_mul_convolution_le`), and each convolution on the right is
that of an `L¹` function with an `L²` function, which lies in `L²` by Young's inequality
(`MeasureTheory.lintegral_lconvolution_sq_le`).

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

/-- **The weighted convolution estimate.** For `0 ≤ s`, if `f` and `g` are integrable and
`(1 + ‖ξ‖ ^ 2) ^ (s / 2) f` and `(1 + ‖ξ‖ ^ 2) ^ (s / 2) g` are square integrable, then so is
`(1 + ‖ξ‖ ^ 2) ^ (s / 2) (f ⋆ g)`. -/
theorem memLp_one_add_norm_sq_rpow_mul_convolution {s : ℝ} (hs : 0 ≤ s) {f g : E → ℂ}
    (hf : Integrable f) (hg : Integrable g)
    (hwf : MemLp (fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * f x) 2)
    (hwg : MemLp (fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * g x) 2) :
    MemLp (fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (f ⋆[mul ℂ ℂ] g) x) 2 := by
  have hwc : Continuous fun x : E => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) := by fun_prop
  have hmeas : AEStronglyMeasurable
      (fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (f ⋆[mul ℂ ℂ] g) x) volume :=
    hwc.aestronglyMeasurable.mul (hf.integrable_convolution (mul ℂ ℂ) hg).aestronglyMeasurable
  set X := (fun y => ‖g y‖ₑ) ⋆ₗ fun y => ‖(((1 + ‖y‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * f y‖ₑ
  set Y := (fun y => ‖f y‖ₑ) ⋆ₗ fun y => ‖(((1 + ‖y‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * g y‖ₑ
  -- Young's inequality bounds both convolutions in `L²`.
  have hfin : ∀ {F : E → ℂ}, MemLp F 2 → ∫⁻ x, ‖F x‖ₑ ^ 2 < ∞ := fun hF => by
    simpa using (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
      hF.aestronglyMeasurable).1 hF.eLpNorm_lt_top
  have hX : ∫⁻ x, X x ^ 2 < ∞ :=
    (lintegral_lconvolution_sq_le hg.aestronglyMeasurable.enorm
      hwf.aestronglyMeasurable.enorm).trans_lt <| ENNReal.mul_lt_top
        (ENNReal.pow_lt_top (hasFiniteIntegral_iff_enorm.1 hg.hasFiniteIntegral)) (hfin hwf)
  have hY : ∫⁻ x, Y x ^ 2 < ∞ :=
    (lintegral_lconvolution_sq_le hf.aestronglyMeasurable.enorm
      hwg.aestronglyMeasurable.enorm).trans_lt <| ENNReal.mul_lt_top
        (ENNReal.pow_lt_top (hasFiniteIntegral_iff_enorm.1 hf.hasFiniteIntegral)) (hfin hwg)
  -- Integrate the square of the pointwise bound, using `(X + Y) ^ 2 ≤ 2 (X ^ 2 + Y ^ 2)`.
  refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num) hmeas).2 ?_
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  calc ∫⁻ x, ‖(((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (f ⋆[mul ℂ ℂ] g) x‖ₑ ^ 2
      ≤ ∫⁻ x, ENNReal.ofReal (2 ^ s) ^ 2 * (2 * (X x ^ 2 + Y x ^ 2)) := by
        refine lintegral_mono fun x => ?_
        have hsq := ENNReal.rpow_add_le_mul_rpow_add_rpow (X x) (Y x) (p := 2) one_le_two
        norm_num [ENNReal.rpow_two] at hsq
        calc ‖(((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (f ⋆[mul ℂ ℂ] g) x‖ₑ ^ 2
            ≤ (ENNReal.ofReal (2 ^ s) * (X x + Y x)) ^ 2 := by
              gcongr
              exact enorm_one_add_norm_sq_rpow_mul_convolution_le hs hwf.aestronglyMeasurable
                hg.aestronglyMeasurable x
          _ ≤ ENNReal.ofReal (2 ^ s) ^ 2 * (2 * (X x ^ 2 + Y x ^ 2)) := by
              rw [mul_pow]
              gcongr
    _ < ∞ := by
      rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
        lintegral_const_mul' _ _ ENNReal.ofNat_ne_top, lintegral_add_left'
          ((aemeasurable_lconvolution hg.aestronglyMeasurable.enorm
            hwf.aestronglyMeasurable.enorm).pow_const 2)]
      exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
        (ENNReal.mul_lt_top ENNReal.ofNat_lt_top (ENNReal.add_lt_top.2 ⟨hX, hY⟩))

end TauCeti
