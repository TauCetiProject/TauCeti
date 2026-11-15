/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Nonzero derivatives of nonconstant absolutely continuous curves

Every nonconstant absolutely continuous curve in a finite-dimensional real normed space admits an
interior parameter with nonzero derivative: if the derivative vanished at every interior point of
differentiability, almost-everywhere differentiability
(`BoundedVariationOn.ae_differentiableAt_of_mem_uIcc`) and
`AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero` would force the curve to be constant.
-/

public section

open MeasureTheory Set

namespace AbsolutelyContinuousOnInterval

/-- **Every nonconstant absolutely continuous curve on `[a, b]` has an interior point with nonzero
derivative.** -/
theorem exists_mem_Ioo_hasDerivAt_ne_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {γ : ℝ → F} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hnonconst : ∃ s ∈ Icc a b, ∃ t ∈ Icc a b, γ s ≠ γ t) :
    ∃ t₀ ∈ Ioo a b, ∃ v : F, v ≠ 0 ∧ HasDerivAt γ v t₀ := by
  obtain ⟨s, hs, t, ht, hne⟩ := hnonconst
  have hab : a < b := (hs.1.trans hs.2).lt_of_ne fun hab_eq ↦
    hne (congrArg γ ((le_antisymm hs.2 (hab_eq ▸ hs.1)).trans
      (le_antisymm ht.2 (hab_eq ▸ ht.1)).symm))
  by_contra! hall
  have hzero : ∀ᵐ u : ℝ, u ∈ uIcc a b → HasDerivAt γ 0 u := by
    filter_upwards [hγ.boundedVariationOn.ae_differentiableAt_of_mem_uIcc,
      volume.ae_ne a, volume.ae_ne b] with u hdu hua hub hu
    have hu' : u ∈ Icc a b := uIcc_of_le hab.le ▸ hu
    have hu₀ : u ∈ Ioo a b := ⟨hu'.1.lt_of_ne' hua, hu'.2.lt_of_ne hub⟩
    have hd := (hdu hu).hasDerivAt
    by_cases hv : deriv γ u = 0
    · rwa [hv] at hd
    · exact absurd hd (hall u hu₀ (deriv γ u) hv)
  obtain ⟨C, hC⟩ := hγ.const_of_ae_hasDerivAt_zero hzero
  exact hne ((hC s (uIcc_of_le hab.le ▸ hs)).trans (hC t (uIcc_of_le hab.le ▸ ht)).symm)

end AbsolutelyContinuousOnInterval
