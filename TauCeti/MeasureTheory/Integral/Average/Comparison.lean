/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Comparing averages

Two bounds on averages of real functions over a set.

* If `0 ≤ f ≤ k (g₁ + g₂)` almost everywhere on `s`, with `g₁` and `g₂` integrable on `s`, then
  `⨍_s f ≤ k (⨍_s g₁ + ⨍_s g₂)` (`TauCeti.setAverage_le_mul_add_of_ae_le`). No integrability of
  `f` is needed: the bound on `f` makes it integrable when `μ s < ∞`, and every average is `0`
  otherwise.
* For an additive Haar measure on a finite-dimensional space of dimension `n` and a function
  `g ≥ 0` integrable on the ball `B(c, r)`, the average over a concentric ball `B(c, ρ)`,
  `0 < ρ ≤ r`, is at most the ratio `(r / ρ)ⁿ` of the volumes times the average over `B(c, r)`
  (`TauCeti.setAverage_ball_le_div_pow_mul`).

Both are used to pass pointwise and integral estimates to averages over balls, which are invariant
under dilations.
-/

public section

open MeasureTheory Metric Module

namespace TauCeti

/-- An average bounded pointwise by a multiple of a sum: if `0 ≤ f ≤ k (g₁ + g₂)` almost everywhere
on `s`, with `g₁` and `g₂` integrable on `s`, then `⨍_s f ≤ k (⨍_s g₁ + ⨍_s g₂)`. -/
theorem setAverage_le_mul_add_of_ae_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {s : Set X} {f g₁ g₂ : X → ℝ} {k : ℝ} (hg₁ : IntegrableOn g₁ s μ) (hg₂ : IntegrableOn g₂ s μ)
    (hf0 : ∀ᵐ x ∂μ.restrict s, 0 ≤ f x) (h : ∀ᵐ x ∂μ.restrict s, f x ≤ k * (g₁ x + g₂ x)) :
    ⨍ x in s, f x ∂μ ≤ k * ((⨍ x in s, g₁ x ∂μ) + ⨍ x in s, g₂ x ∂μ) := by
  have hI := integral_mono_of_nonneg hf0 ((hg₁.add hg₂).const_mul k) h
  simp only [Pi.add_apply] at hI
  rw [integral_const_mul, integral_add hg₁ hg₂] at hI
  rw [setAverage_eq, setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  calc (μ.real s)⁻¹ * ∫ x in s, f x ∂μ
      ≤ (μ.real s)⁻¹ * (k * ((∫ x in s, g₁ x ∂μ) + ∫ x in s, g₂ x ∂μ)) :=
        mul_le_mul_of_nonneg_left hI (inv_nonneg.2 measureReal_nonneg)
    _ = _ := by ring

/-- The average of a nonnegative function over the ball `B(c, ρ)` is at most `(r / ρ)ⁿ` times its
average over the concentric ball `B(c, r) ⊇ B(c, ρ)`, for an additive Haar measure on a space of
dimension `n`. -/
theorem setAverage_ball_le_div_pow_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {c : E} {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) {g : E → ℝ}
    (hg : IntegrableOn g (ball c r) μ) (hg0 : ∀ x ∈ ball c r, 0 ≤ g x) :
    ⨍ x in ball c ρ, g x ∂μ ≤ (r / ρ) ^ finrank ℝ E * ⨍ x in ball c r, g x ∂μ := by
  have hr : 0 < r := hρ.trans_le hρr
  have hω : 0 < μ.real (ball (0 : E) 1) := measureReal_ball_pos μ 0 one_pos
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul,
    μ.addHaar_real_ball_of_pos c hρ, μ.addHaar_real_ball_of_pos c hr]
  calc (ρ ^ finrank ℝ E * μ.real (ball (0 : E) 1))⁻¹ * ∫ x in ball c ρ, g x ∂μ
      ≤ (ρ ^ finrank ℝ E * μ.real (ball (0 : E) 1))⁻¹ * ∫ x in ball c r, g x ∂μ :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_set hg
          ((ae_restrict_mem measurableSet_ball).mono hg0) (ball_subset_ball hρr).eventuallySubset)
          (by positivity)
    _ = _ := by
        rw [div_pow]
        field_simp

end TauCeti
