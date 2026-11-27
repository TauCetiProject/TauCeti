/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average

/-!
# Comparing averages

If `0 ≤ f ≤ k (g₁ + g₂)` almost everywhere on `s`, with `g₁` and `g₂` integrable on `s`, then
`⨍_s f ≤ k (⨍_s g₁ + ⨍_s g₂)` (`TauCeti.setAverage_le_mul_add_of_ae_le`). No integrability of
`f` is needed: the bound on `f` makes it integrable when `μ s < ∞`, and every average is `0`
otherwise. This passes pointwise estimates to averages.
-/

public section

open MeasureTheory

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

end TauCeti
