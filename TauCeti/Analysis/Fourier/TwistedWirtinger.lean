/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.Fourier.AbsolutelyContinuous
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Wirtinger's inequality for twisted periodic functions

Let `f : ℝ → ℂ` be absolutely continuous on `[a, b]` with square-integrable almost-everywhere
derivative, and suppose that its endpoint values differ by a phase,
`f b = exp (2πiθ) f a` for a real `θ`. Then

`(2π |θ - round θ| / (b - a)) ^ 2 ∫ₐᵇ ‖f‖ ^ 2 ≤ ∫ₐᵇ ‖f'‖ ^ 2`

(`TauCeti.mul_integral_norm_sq_le_integral_norm_sq_of_eq_exp_mul`). Here `|θ - round θ|` is the
distance from `θ` to the nearest integer, so the constant is positive exactly when the phase
`exp (2πiθ)` is not one. For `f t = exp (2πi (θ - round θ) (t - a) / (b - a))` both sides agree.

Such an `f` is a section of the flat line bundle over the circle `ℝ / (b - a) ℤ` with holonomy
`exp (2πiθ)`, and the inequality says that the covariant derivative of this flat connection is
bounded below by `2π |θ - round θ| / (b - a)` in `L²`. For `θ = 1 / 2` it is the Poincaré
inequality for antiperiodic functions.

The proof multiplies `f` by the phase `exp (-2πiθ (t - a) / (b - a))`, which produces a closed curve
`g` whose `n`-th Fourier coefficient is multiplied by `2πi (n + θ) / (b - a)` under the twisted
derivative (`TauCeti.fourierCoeffOn_sub_mul_I_mul`). Parseval's identity
(`hasSum_sq_fourierCoeffOn`) then compares the two sides frequency by frequency, using
`|θ - round θ| ≤ |θ + n|` for every integer `n` (`round_le`).

## References

* G. H. Hardy, J. E. Littlewood and G. Pólya, *Inequalities*, Cambridge University Press, 1934,
  Theorem 258, for the untwisted inequality and its Fourier proof.
-/

public section

open MeasureTheory Set Complex intervalIntegral
open scoped Real Interval

namespace TauCeti

variable {a b : ℝ} {f f' : ℝ → ℂ}

/-- **Untwisting a twisted periodic function.** If `f b = exp (2πiθ) f a`, then
`g t = exp (-2πiθ (t - a) / (b - a)) f t` is an absolutely continuous closed curve with
`‖g‖ = ‖f‖`, and the Fourier coefficients of `exp (-2πiθ (t - a) / (b - a)) f'` are those of `g`
times `2πi (θ + n) / (b - a)`. Parseval's identity for both gives the twisted energy identity: the
Fourier coefficients `c n` of `g` satisfy `∑ ‖c n‖ ^ 2 = (b - a)⁻¹ ∫ ‖f‖ ^ 2` and
`∑ (2π (θ + n) / (b - a)) ^ 2 ‖c n‖ ^ 2 = (b - a)⁻¹ ∫ ‖f'‖ ^ 2`. -/
private theorem exists_hasSum_sq_and_hasSum_sq_mul (hab : a < b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hff' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (f' t) t)
    (hf' : MemLp f' 2 (volume.restrict (Ioc a b))) {θ : ℝ}
    (hfab : f b = exp (2 * π * θ * I) * f a) :
    ∃ c : ℤ → ℂ, HasSum (fun n ↦ ‖c n‖ ^ 2) ((b - a)⁻¹ * ∫ t in a..b, ‖f t‖ ^ 2) ∧
      HasSum (fun n : ℤ ↦ (2 * π * (θ + n) / (b - a)) ^ 2 * ‖c n‖ ^ 2)
        ((b - a)⁻¹ * ∫ t in a..b, ‖f' t‖ ^ 2) := by
  set k : ℝ := 2 * π * θ / (b - a)
  -- The untwisting phase `e t = exp (-i k (t - a))` and the closed curve `g = e f`.
  set e : ℝ → ℂ := fun t ↦ exp ((-(k * (t - a)) : ℝ) * I)
  have hen (t : ℝ) : ‖e t‖ = 1 := norm_exp_ofReal_mul_I _
  have hed (t : ℝ) : HasDerivAt e (e t * ((-k : ℝ) * I)) t := by
    have h : HasDerivAt (fun t : ℝ ↦ ((-(k * (t - a)) : ℝ) : ℂ)) ((-k : ℝ) : ℂ) t := by
      have h₀ : HasDerivAt (fun t : ℝ ↦ -(k * (t - a))) (-(k * 1)) t :=
        (((hasDerivAt_id t).sub_const a).const_mul k).neg
      simpa using h₀.ofReal_comp
    exact (h.mul_const I).cexp
  have hec : Continuous e := by fun_prop
  have he : AbsolutelyContinuousOnInterval e a b := by
    have h₀ : ContDiff ℝ 1 fun t : ℝ ↦ -(k * (t - a)) := by fun_prop
    exact ((ofRealCLM.contDiff.comp h₀).mul contDiff_const).cexp.contDiffOn
      |>.absolutelyContinuousOnInterval
  set g : ℝ → ℂ := fun t ↦ e t * f t
  have hg : AbsolutelyContinuousOnInterval g a b := he.smul hf
  have hgg' : ∀ᵐ t, t ∈ uIoc a b →
      HasDerivAt g (e t * f' t + e t * ((-k : ℝ) * I) * f t) t := by
    filter_upwards [hff'] with t ht hmem
    convert (hed t).mul (ht hmem) using 1
    ring
  have heb : e b * exp (2 * π * θ * I) = 1 := by
    have hk : k * (b - a) = 2 * π * θ := by simp only [k]; field_simp
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    simp only [hk]
    push_cast
    ring
  have hgab : g a = g b := by
    simp only [g, hfab, ← mul_assoc, heb, one_mul, e, sub_self, mul_zero, neg_zero,
      ofReal_zero, zero_mul, Complex.exp_zero]
  have hgL2 : MemLp g 2 (volume.restrict (Ioc a b)) :=
    (by simpa only [uIcc_of_le hab.le] using hg.continuousOn : ContinuousOn g (Icc a b))
      |>.memLp_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self 2
  have hef'L2 : MemLp (fun t ↦ e t * f' t) 2 (volume.restrict (Ioc a b)) :=
    hf'.congr_norm (hec.aestronglyMeasurable.mul hf'.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t ↦ by simp [hen])
  refine ⟨fourierCoeffOn hab g, by simpa [g, hen] using hasSum_sq_fourierCoeffOn hab hgL2, ?_⟩
  convert hasSum_sq_fourierCoeffOn hab hef'L2 using 1
  · -- The twisted derivative `e f' = g' + i k g` multiplies the `n`-th coefficient by
    -- `i (2πn / (b - a) + k) = 2πi (θ + n) / (b - a)`.
    funext n
    have h := fourierCoeffOn_sub_mul_I_mul hab hg hgg' hgab (-k) n
    rw [show (fun t ↦ e t * f' t + e t * ((-k : ℝ) * I) * f t - ((-k : ℝ) * I) * g t) =
      fun t ↦ e t * f' t by funext t; simp only [g]; ring] at h
    rw [h]
    simp only [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    congr 2
    simp only [k]
    field_simp
    ring
  · simp [hen]

/-- **Wirtinger's inequality for twisted periodic functions.** If `f` is absolutely continuous on
`[a, b]` with square-integrable almost-everywhere derivative `f'`, and `f b = exp (2πiθ) f a`, then
`(2π |θ - round θ| / (b - a)) ^ 2 ∫ₐᵇ ‖f‖ ^ 2 ≤ ∫ₐᵇ ‖f'‖ ^ 2`. The constant is positive exactly
when `θ` is not an integer. -/
theorem mul_integral_norm_sq_le_integral_norm_sq_of_eq_exp_mul (hab : a < b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hff' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (f' t) t)
    (hf' : MemLp f' 2 (volume.restrict (Ioc a b))) {θ : ℝ}
    (hfab : f b = exp (2 * π * θ * I) * f a) :
    (2 * π * |θ - round θ| / (b - a)) ^ 2 * ∫ t in a..b, ‖f t‖ ^ 2 ≤
      ∫ t in a..b, ‖f' t‖ ^ 2 := by
  obtain ⟨c, hc, hc'⟩ := exists_hasSum_sq_and_hasSum_sq_mul hab hf hff' hf' hfab
  set C := (2 * π * |θ - round θ| / (b - a)) ^ 2
  -- Compare frequency by frequency, using `|θ - round θ| ≤ |θ + n|`.
  have hterm (n : ℤ) : C * ‖c n‖ ^ 2 ≤ (2 * π * (θ + n) / (b - a)) ^ 2 * ‖c n‖ ^ 2 := by
    gcongr
    have h : |θ - round θ| ^ 2 ≤ (θ + n) ^ 2 := by
      rw [← sq_abs (θ + n)]
      exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using round_le θ (-n)) 2
    calc C = (2 * π / (b - a)) ^ 2 * |θ - round θ| ^ 2 := by simp only [C]; ring
      _ ≤ (2 * π / (b - a)) ^ 2 * (θ + n) ^ 2 := by gcongr
      _ = (2 * π * (θ + n) / (b - a)) ^ 2 := by ring
  have h := hasSum_le hterm (hc.mul_left C) hc'
  rw [← mul_assoc, mul_comm C, mul_assoc] at h
  exact le_of_mul_le_mul_left h (inv_pos.2 (sub_pos.2 hab))

end TauCeti
