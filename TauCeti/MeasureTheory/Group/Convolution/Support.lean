/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Supports of convolution-type parametric integrals over a group

Convolutions over a group `G` are parametric integrals `s ↦ ∫ r, F s r ∂μ` whose integrand
vanishes unless `r ∈ K` and `r⁻¹ * s ∈ L`, where `K` and `L` are the supports of the two factors.
This file records the resulting support bounds, for any normed-space valued integrand: the
parametric integral is supported in `K * L`, and for compact `K` and `L` both the integrand on
`G × G` and the parametric integral are compactly supported.

## Main statements

* `TauCeti.support_integral_subset_mul`: the parametric integral is supported in `K * L`.
* `TauCeti.hasCompactSupport_uncurry_of_inv_mul_mem`: the integrand is compactly supported on
  `G × G`.
* `TauCeti.hasCompactSupport_integral_of_inv_mul_mem`: the parametric integral is compactly
  supported.
-/

public section

open MeasureTheory Function
open scoped Pointwise

namespace TauCeti

variable {G E : Type*} [Group G] [NormedAddCommGroup E] {F : G → G → E} {K L : Set G}

/-- A two-variable integrand which vanishes unless `r ∈ K` and `r⁻¹ * s ∈ L` has its parametric
integral `s ↦ ∫ r, F s r` supported in `K * L`. -/
theorem support_integral_subset_mul [NormedSpace ℝ E] [MeasurableSpace G] (μ : Measure G)
    (hF : ∀ s r, F s r ≠ 0 → r ∈ K ∧ r⁻¹ * s ∈ L) :
    support (fun s => ∫ r, F s r ∂μ) ⊆ K * L := by
  intro s hs
  by_contra h
  refine hs (integral_eq_zero_of_ae (.of_forall fun r => ?_))
  by_contra hr
  obtain ⟨hrK, hrL⟩ := hF s r hr
  exact h ⟨r, hrK, r⁻¹ * s, hrL, mul_inv_cancel_left r s⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- A two-variable integrand which vanishes unless `r ∈ K` and `r⁻¹ * s ∈ L`, for compact `K`
and `L`, is compactly supported on `G × G`. -/
theorem hasCompactSupport_uncurry_of_inv_mul_mem (hK : IsCompact K) (hL : IsCompact L)
    (hF : ∀ s r, F s r ≠ 0 → r ∈ K ∧ r⁻¹ * s ∈ L) : HasCompactSupport (uncurry F) := by
  refine ((hK.mul hL).prod hK).closure_of_subset fun p hp => ?_
  obtain ⟨hrK, hrL⟩ := hF p.1 p.2 hp
  exact ⟨⟨p.2, hrK, p.2⁻¹ * p.1, hrL, mul_inv_cancel_left p.2 p.1⟩, hrK⟩

/-- The parametric integral `s ↦ ∫ r, F s r` of an integrand which vanishes unless `r ∈ K` and
`r⁻¹ * s ∈ L`, for compact `K` and `L`, is compactly supported. -/
theorem hasCompactSupport_integral_of_inv_mul_mem [NormedSpace ℝ E] [MeasurableSpace G]
    (μ : Measure G) (hK : IsCompact K) (hL : IsCompact L)
    (hF : ∀ s r, F s r ≠ 0 → r ∈ K ∧ r⁻¹ * s ∈ L) :
    HasCompactSupport (fun s => ∫ r, F s r ∂μ) :=
  (hK.mul hL).closure_of_subset (support_integral_subset_mul μ hF)

end TauCeti
