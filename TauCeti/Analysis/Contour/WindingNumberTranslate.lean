/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.NullHomologous
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Translation invariance for contour winding numbers

This file records the basic translation-invariance API for the single-point Cauchy principal value
and the generalized winding number. Translating both the curve and the distinguished point by the
same complex number leaves the excision distance and the contour derivative unchanged, so the
index principal value, the winding number, and null-homology are invariant.

These lemmas are bookkeeping for the roadmap's curve and cycle layer. The geometry of the
generalized winding number is local at a crossing or sector, and finite-decomposition arguments
frequently translate the crossing point to the origin before applying the model computation.

## Main results

* `Contour.HasCauchyPVAt.translate` — simultaneous translation of the curve, point, and
  integrand preserves a single-point principal value.
* `Contour.windingNumber_translate` — translating the curve and base point together preserves
  the generalized winding number.
* `Contour.IsNullHomologous.translate` — null-homology is preserved by translating both the
  curve and the ambient set.

## Provenance

This is routine API around the Hungerbühler--Wasem generalized winding number from the contour
integration roadmap; no formal source is vendored.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.Contour

variable {γ : ℝ → ℂ} {a b : ℝ} {z₀ c L : ℂ} {Ω : Set ℂ}

/-- The kernel integrand used to define the generalized winding number about `z₀`. This local
abbreviation keeps the translation statements readable. -/
local notation "κ[" z "]" => (fun w : ℂ => (w - z)⁻¹)

/-- Simultaneously translating the curve and the excision point preserves a single-point Cauchy
principal value, provided the integrand is translated back by the same amount. -/
theorem HasCauchyPVAt.translate {f : ℂ → ℂ} (h : HasCauchyPVAt γ a b f z₀ L) (c : ℂ) :
    HasCauchyPVAt (fun t => γ t + c) a b (fun z => f (z - c)) (z₀ + c) L := by
  refine HasCauchyPVAt.intro ?_ ?_
  · filter_upwards [h.eventually_intervalIntegrable] with ε hε
    refine (intervalIntegrable_congr fun t _ => ?_).mpr hε
    by_cases hεt : ‖γ t - z₀‖ > ε
    · simp [hεt]
    · simp [hεt]
  · refine h.tendsto.congr fun ε => ?_
    refine intervalIntegral.integral_congr fun t _ => ?_
    by_cases hεt : ‖γ t - z₀‖ > ε
    · simp [hεt]
    · simp [hεt]

/-- Existence form of `HasCauchyPVAt.translate`: simultaneous translation preserves existence of a
single-point Cauchy principal value. -/
theorem CauchyPVExistsAt.translate {f : ℂ → ℂ} (h : CauchyPVExistsAt γ a b f z₀) (c : ℂ) :
    CauchyPVExistsAt (fun t => γ t + c) a b (fun z => f (z - c)) (z₀ + c) :=
  let ⟨_, hL⟩ := cauchyPVExistsAt_iff.mp h
  CauchyPVExistsAt.intro (hL.translate c)

/-- The generalized winding number is invariant under simultaneous translation of the curve and
the base point, provided the principal value defining the original winding number exists. -/
theorem windingNumber_translate (h : CauchyPVExistsAt γ a b κ[z₀] z₀) (c : ℂ) :
    windingNumber (fun t => γ t + c) a b (z₀ + c) = windingNumber γ a b z₀ := by
  have htranslated :
      HasCauchyPVAt (fun t => γ t + c) a b κ[z₀ + c] (z₀ + c) (cauchyPVAt γ a b κ[z₀] z₀) := by
    refine (h.hasCauchyPVAt_cauchyPVAt.translate c).congr_along_curve ?_
    intro t _
    congr 1
    ring
  rw [windingNumber_eq_of_hasCauchyPVAt htranslated,
    windingNumber_eq_of_hasCauchyPVAt h.hasCauchyPVAt_cauchyPVAt]

/-- Pointwise vanishing of a winding number is preserved by simultaneous translation of the curve
and the base point, under the principal-value existence hypothesis that makes the two
winding-number values honest. -/
theorem windingNumber_eq_zero_translate (hzero : windingNumber γ a b z₀ = 0)
    (hpv : CauchyPVExistsAt γ a b κ[z₀] z₀) (c : ℂ) :
    windingNumber (fun t => γ t + c) a b (z₀ + c) = 0 := by
  rw [windingNumber_translate hpv c, hzero]

/-- Null-homology is preserved by translating the curve and the ambient set together, provided the
pointwise principal values defining the exterior winding numbers exist before translation. -/
theorem IsNullHomologous.translate (h : IsNullHomologous γ a b Ω)
    (hpv : ∀ z ∉ Ω, CauchyPVExistsAt γ a b κ[z] z) (c : ℂ) :
    IsNullHomologous (fun t => γ t + c) a b ((fun z => z + c) '' Ω) := by
  rw [isNullHomologous_iff] at h ⊢
  intro z hz
  have hz_sub : z - c ∉ Ω := by
    intro hzΩ
    exact hz ⟨z - c, hzΩ, by ring⟩
  have hpoint : z = (z - c) + c := by ring
  rw [hpoint]
  exact windingNumber_eq_zero_translate (h (z - c) hz_sub) (hpv (z - c) hz_sub) c

end TauCeti.Contour

end
