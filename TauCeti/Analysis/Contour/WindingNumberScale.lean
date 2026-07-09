/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.NullHomologous
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Scaling invariance for contour winding numbers

This file records the basic nonzero-scaling API for the generalized winding number. Multiplying
both the curve and the distinguished point by the same nonzero complex number leaves the index
principal value unchanged, so the winding number and null-homology are invariant.

These lemmas are bookkeeping for the roadmap's curve and cycle layer. The geometry of the
generalized winding number is local at a crossing or sector; after translating the crossing point
to the origin, finite-decomposition arguments also rescale the local model before applying the
sector computation.

## Main results

* `Contour.windingNumber_const_mul` — multiplying the curve and base point by the same nonzero
  complex number preserves the generalized winding number, under the principal-value existence
  hypothesis for the original kernel.
* `Contour.IsNullHomologous.const_mul` — null-homology is preserved by nonzero complex scaling of
  both the curve and the ambient set.

## Provenance

This is routine API around the Hungerbühler--Wasem generalized winding number from the contour
integration roadmap; no formal source is vendored.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.Contour

variable {γ : ℝ → ℂ} {a b : ℝ} {z₀ c : ℂ} {Ω : Set ℂ}

/-- The kernel integrand used to define the generalized winding number about `z₀`. This local
abbreviation keeps the scaling statements readable. -/
local notation "κ[" z "]" => (fun w : ℂ => (w - z)⁻¹)

private theorem tendsto_div_nhdsWithin_pos (hc : c ≠ 0) :
    Tendsto (fun ε : ℝ => ε / ‖c‖) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  have hnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hnhds : Tendsto (fun ε : ℝ => ε / ‖c‖) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).div_const ‖c‖
  have hpos : Tendsto (fun ε : ℝ => ε / ‖c‖) (𝓟 (Set.Ioi (0 : ℝ))) (𝓟 (Set.Ioi (0 : ℝ))) := by
    refine tendsto_principal_principal.mpr ?_
    intro ε hε
    exact div_pos hε hnorm
  exact Tendsto.inf hnhds hpos

private theorem windingKernel_const_mul_hasCauchyPVAt
    (h : HasCauchyPVAt γ a b κ[z₀] z₀ L) (hc : c ≠ 0) :
    HasCauchyPVAt (fun t => c * γ t) a b κ[c * z₀] (c * z₀) L := by
  have hscale : Tendsto (fun ε : ℝ => ε / ‖c‖) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_div_nhdsWithin_pos (c := c) hc
  refine HasCauchyPVAt.intro ?_ ?_
  · filter_upwards [hscale.eventually h.eventually_intervalIntegrable] with ε hε
    refine (intervalIntegrable_congr fun t _ => ?_).mpr hε
    by_cases hεt : ‖γ t - z₀‖ > ε / ‖c‖
    · have hscaled : ‖c * γ t - c * z₀‖ > ε := by
        rw [← mul_sub, norm_mul]
        have hmul := mul_lt_mul_of_pos_right hεt (norm_pos_iff.mpr hc)
        have hmul' : ε < ‖γ t - z₀‖ * ‖c‖ := by
          simpa [div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hc)] using hmul
        simpa [mul_comm] using hmul'
      rw [if_pos hscaled, if_pos hεt, deriv_const_mul_field]
      field_simp [hc, sub_eq_add_neg, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]
    · have hscaled : ¬ ‖c * γ t - c * z₀‖ > ε := by
        rw [← mul_sub, norm_mul, not_lt]
        rw [not_lt] at hεt
        have hmul := mul_le_mul_of_nonneg_right hεt (norm_nonneg c)
        rwa [div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hc), mul_comm] at hmul
      rw [if_neg hscaled, if_neg hεt]
  · refine h.tendsto.comp hscale |>.congr' ?_
    filter_upwards with ε
    refine intervalIntegral.integral_congr fun t _ => ?_
    by_cases hεt : ‖γ t - z₀‖ > ε / ‖c‖
    · have hscaled : ‖c * γ t - c * z₀‖ > ε := by
        rw [← mul_sub, norm_mul]
        have hmul := mul_lt_mul_of_pos_right hεt (norm_pos_iff.mpr hc)
        have hmul' : ε < ‖γ t - z₀‖ * ‖c‖ := by
          simpa [div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hc)] using hmul
        simpa [mul_comm] using hmul'
      rw [if_pos hscaled, if_pos hεt, deriv_const_mul_field]
      field_simp [hc, sub_eq_add_neg, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]
    · have hscaled : ¬ ‖c * γ t - c * z₀‖ > ε := by
        rw [← mul_sub, norm_mul, not_lt]
        rw [not_lt] at hεt
        have hmul := mul_le_mul_of_nonneg_right hεt (norm_nonneg c)
        rwa [div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hc), mul_comm] at hmul
      rw [if_neg hscaled, if_neg hεt]

/-- The generalized winding number is invariant under simultaneous multiplication of the curve
and the base point by a nonzero complex number, provided the original principal value exists. -/
theorem windingNumber_const_mul (h : CauchyPVExistsAt γ a b κ[z₀] z₀) (hc : c ≠ 0) :
    windingNumber (fun t => c * γ t) a b (c * z₀) = windingNumber γ a b z₀ := by
  rw [windingNumber_eq_of_hasCauchyPVAt
      (windingKernel_const_mul_hasCauchyPVAt h.hasCauchyPVAt_cauchyPVAt hc),
    windingNumber_eq_of_hasCauchyPVAt h.hasCauchyPVAt_cauchyPVAt]

/-- Pointwise vanishing of a winding number is preserved by simultaneous multiplication of the
curve and base point by a nonzero complex number, under the original principal-value existence
hypothesis. -/
theorem windingNumber_eq_zero_const_mul (hzero : windingNumber γ a b z₀ = 0)
    (hpv : CauchyPVExistsAt γ a b κ[z₀] z₀) (hc : c ≠ 0) :
    windingNumber (fun t => c * γ t) a b (c * z₀) = 0 := by
  rw [windingNumber_const_mul hpv hc, hzero]

/-- Null-homology is preserved by nonzero complex scaling, provided the pointwise principal values
defining the original exterior winding numbers exist. -/
theorem IsNullHomologous.const_mul (h : IsNullHomologous γ a b Ω)
    (hpv : ∀ z ∉ Ω, CauchyPVExistsAt γ a b κ[z] z) (hc : c ≠ 0) :
    IsNullHomologous (fun t => c * γ t) a b ((fun z => c * z) '' Ω) := by
  rw [isNullHomologous_iff] at h ⊢
  intro z hz
  have hpre_not_mem : c⁻¹ * z ∉ Ω := by
    intro hzΩ
    exact hz ⟨c⁻¹ * z, hzΩ, by field_simp [hc]⟩
  have hz_eq : z = c * (c⁻¹ * z) := by field_simp [hc]
  rw [hz_eq]
  exact windingNumber_eq_zero_const_mul (h (c⁻¹ * z) hpre_not_mem)
    (hpv (c⁻¹ * z) hpre_not_mem) hc

/-- Null-homology is preserved by nonzero complex scaling in the ordinary avoided-pole case. If the
curve lies in `Ω`, every exterior point of the scaled ambient set is avoided by the scaled curve, so
the required original principal values are ordinary integrals. -/
theorem IsNullHomologous.const_mul_of_avoidance (h : IsNullHomologous γ a b Ω)
    (hγ : ∀ t ∈ Set.uIcc a b, γ t ∈ Ω)
    (hcont : ContinuousOn γ (Set.uIcc a b))
    (hint : ∀ z ∉ Ω,
      IntervalIntegrable (fun t => (γ t - z)⁻¹ * deriv γ t) MeasureTheory.volume a b)
    (hc : c ≠ 0) :
    IsNullHomologous (fun t => c * γ t) a b ((fun z => c * z) '' Ω) := by
  refine h.const_mul ?_ hc
  intro z hz
  refine cauchyPVExistsAt_of_avoidance hcont ?_ (hint z hz)
  intro t ht htz
  exact hz (htz ▸ hγ t ht)

end TauCeti.Contour

end
