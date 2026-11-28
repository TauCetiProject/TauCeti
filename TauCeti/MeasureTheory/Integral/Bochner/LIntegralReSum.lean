/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Lower Lebesgue integral of the real part of a finite linear combination

Let `f : ι → X → 𝕜` be a finite family of integrable functions valued in `𝕜` (with `[RCLike 𝕜]`)
and `c : ι → 𝕜` scalars such that the real part of `∑ i ∈ s, c i * f i x` is almost everywhere
nonnegative. This file proves that the lower Lebesgue integral of
`ENNReal.ofReal (RCLike.re (∑ i ∈ s, c i * f i x))` equals
`ENNReal.ofReal (RCLike.re (∑ i ∈ s, c i * ∫ x, f i x ∂μ))`, together with the double-sum
form for matrix-weighted pairings `∑ a ∈ s, ∑ b ∈ t, c a b * f a b x`.

## Provenance

Extracted and generalized from `grh-lean`
(https://github.com/lsernau/grh-lean at commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
Apache 2.0, Copyright 2026 Anthropic, PBC), file `src/New/Spanning/Frames/TopCorrelation.lean`
(`lintegral_ofReal_re_sum_sum_mul`).
-/

public section

namespace TauCeti

open MeasureTheory

/-- If `f i` is integrable for each `i ∈ s` and `RCLike.re (∑ i ∈ s, c i * f i x)` is almost
everywhere nonnegative, then its lower Lebesgue integral equals `ENNReal.ofReal` of the real part
of `∑ i ∈ s, c i * ∫ x, f i x ∂μ`. -/
theorem lintegral_ofReal_re_sum_mul {X ι 𝕜 : Type*} [MeasurableSpace X] {μ : Measure X}
    [RCLike 𝕜] {s : Finset ι} {c : ι → 𝕜} {f : ι → X → 𝕜}
    (hf : ∀ i ∈ s, Integrable (f i) μ)
    (h_nonneg : ∀ᵐ x ∂μ, 0 ≤ RCLike.re (∑ i ∈ s, c i * f i x)) :
    ∫⁻ x, ENNReal.ofReal (RCLike.re (∑ i ∈ s, c i * f i x)) ∂μ =
      ENNReal.ofReal (RCLike.re (∑ i ∈ s, c i * ∫ x, f i x ∂μ)) := by
  have h_int : Integrable (fun x ↦ ∑ i ∈ s, c i * f i x) μ :=
    integrable_finsetSum s fun i hi ↦ (hf i hi).const_mul (c i)
  have h_sum : ∑ i ∈ s, c i * ∫ x, f i x ∂μ = ∫ x, ∑ i ∈ s, c i * f i x ∂μ := by
    rw [integral_finsetSum s fun i hi ↦ (hf i hi).const_mul (c i)]
    exact Finset.sum_congr rfl fun i _ ↦ (integral_const_mul (c i) (f i)).symm
  have h_re : RCLike.re (∑ i ∈ s, c i * ∫ x, f i x ∂μ) =
      ∫ x, RCLike.re (∑ i ∈ s, c i * f i x) ∂μ := by
    rw [h_sum]
    exact ((RCLike.reCLM (K := 𝕜)).integral_comp_comm h_int).symm
  rw [h_re]
  exact (ofReal_integral_eq_lintegral_ofReal
    ((RCLike.reCLM (K := 𝕜)).integrable_comp h_int) h_nonneg).symm

/-- Double-sum version of `lintegral_ofReal_re_sum_mul` for a matrix-weighted family
`∑ a ∈ s, ∑ b ∈ t, c a b * f a b x` of integrable functions with almost everywhere nonnegative
real part. -/
theorem lintegral_ofReal_re_sum_sum_mul {X ι κ 𝕜 : Type*} [MeasurableSpace X] {μ : Measure X}
    [RCLike 𝕜] {s : Finset ι} {t : Finset κ} {c : ι → κ → 𝕜} {f : ι → κ → X → 𝕜}
    (hf : ∀ a ∈ s, ∀ b ∈ t, Integrable (f a b) μ)
    (h_nonneg : ∀ᵐ x ∂μ, 0 ≤ RCLike.re (∑ a ∈ s, ∑ b ∈ t, c a b * f a b x)) :
    ∫⁻ x, ENNReal.ofReal (RCLike.re (∑ a ∈ s, ∑ b ∈ t, c a b * f a b x)) ∂μ =
      ENNReal.ofReal (RCLike.re (∑ a ∈ s, ∑ b ∈ t, c a b * ∫ x, f a b x ∂μ)) := by
  have h := lintegral_ofReal_re_sum_mul (s := s ×ˢ t)
    (c := Function.uncurry c) (f := Function.uncurry f)
    (fun ⟨a, b⟩ hab ↦ by
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      exact hf a ha b hb)
    (by simpa only [Finset.sum_product, Function.uncurry_apply_pair] using h_nonneg)
  simpa only [Finset.sum_product, Function.uncurry_apply_pair] using h

end TauCeti
