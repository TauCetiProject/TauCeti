/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.CauchyPrincipalValueOn
public import TauCeti.Analysis.Contour.NullHomologous

/-!
# Orientation reversal for contour principal values and winding numbers

This file records the basic orientation-reversal API for the Cauchy principal values used by the
contour-integration roadmap and for the generalized winding number. Reversing the interval
orientation sends each truncated contour integral to its negative, so both the single-point and
set-level principal values change sign; the same is therefore true for
`Contour.windingNumber`.

These lemmas are bookkeeping for the roadmap's curve and cycle layer. Cycles are oriented formal
combinations of curves, and finite decompositions of curves into avoiding pieces and model sectors
need both concatenation and orientation reversal.

## Main results

* `Contour.HasCauchyPVAt.symm`, `Contour.cauchyPVAt_symm` — reversal for the pointwise principal
  value.
* `Contour.HasCauchyPV.symm`, `Contour.cauchyPV_symm` — reversal for the set-level principal value.
* `Contour.windingNumber_symm` — the generalized winding number changes sign when the interval is
  reversed.
* `Contour.IsNullHomologous.symm`, `Contour.IsNullHomologous.symm_of_avoidance` — null-homology is
  preserved by reversing orientation, under the same honest principal-value existence hypotheses
  used elsewhere in the winding-number API.

## Provenance

This is routine API around the Hungerbühler--Wasem generalized winding number from the contour
integration roadmap; no formal source is vendored.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.Contour

variable {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ L v : ℂ} {Ω : Set ℂ}

/-- Reversing the interval orientation negates a single-point Cauchy principal value. -/
theorem HasCauchyPVAt.symm (h : HasCauchyPVAt γ a b f z₀ L) :
    HasCauchyPVAt γ b a f z₀ (-L) := by
  refine HasCauchyPVAt.intro ?_ ?_
  · filter_upwards [h.eventually_intervalIntegrable] with ε hε
    exact hε.symm
  · refine Filter.Tendsto.congr (fun ε => ?_) h.tendsto.neg
    exact (intervalIntegral.integral_symm (f :=
      fun t => if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) a b).symm

/-- Existence of a single-point Cauchy principal value is invariant under reversing the interval
orientation. -/
theorem CauchyPVExistsAt.symm (h : CauchyPVExistsAt γ a b f z₀) :
    CauchyPVExistsAt γ b a f z₀ :=
  let ⟨_, hL⟩ := cauchyPVExistsAt_iff.mp h
  cauchyPVExistsAt_iff.mpr ⟨_, hL.symm⟩

/-- Value form of `HasCauchyPVAt.symm`: if the single-point principal value exists on `[a, b]`,
then the value on `[b, a]` is its negative. -/
theorem cauchyPVAt_symm (h : CauchyPVExistsAt γ a b f z₀) :
    cauchyPVAt γ b a f z₀ = -cauchyPVAt γ a b f z₀ :=
  h.hasCauchyPVAt_cauchyPVAt.symm.cauchyPVAt_eq

/-- Reversing the interval orientation negates a set-level Cauchy principal value. -/
theorem HasCauchyPV.symm (h : HasCauchyPV γ a b f v) :
    HasCauchyPV γ b a f (-v) := by
  obtain ⟨S, hint, htend⟩ := hasCauchyPV_iff.mp h
  refine HasCauchyPV.intro S ?_ ?_
  · filter_upwards [hint] with ε hε
    exact hε.symm
  · refine Filter.Tendsto.congr (fun ε => ?_) htend.neg
    exact (intervalIntegral.integral_symm (f :=
      fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t) a b).symm

/-- Existence of a set-level Cauchy principal value is invariant under reversing the interval
orientation. -/
theorem CauchyPVExists.symm (h : CauchyPVExists γ a b f) :
    CauchyPVExists γ b a f :=
  let ⟨_, hv⟩ := cauchyPVExists_iff.mp h
  cauchyPVExists_iff.mpr ⟨_, hv.symm⟩

/-- Value form of `HasCauchyPV.symm`: if the set-level principal value exists on `[a, b]`, then
the value on `[b, a]` is its negative. -/
theorem cauchyPV_symm (h : CauchyPVExists γ a b f) :
    cauchyPV γ b a f = -cauchyPV γ a b f :=
  h.hasCauchyPV_cauchyPV.symm.cauchyPV_eq

/-- The kernel integrand used to define the generalized winding number about `z₀`. This local
abbreviation keeps the orientation-reversal statements readable. -/
local notation "κ[" z "]" => (fun w : ℂ => (w - z)⁻¹)

/-- The generalized winding number changes sign when the interval orientation is reversed,
provided the principal value defining the original winding number exists. -/
theorem windingNumber_symm (h : CauchyPVExistsAt γ a b κ[z₀] z₀) :
    windingNumber γ b a z₀ = -windingNumber γ a b z₀ := by
  rw [windingNumber_eq_of_hasCauchyPVAt h.hasCauchyPVAt_cauchyPVAt.symm,
    windingNumber_eq_of_hasCauchyPVAt h.hasCauchyPVAt_cauchyPVAt]
  ring

/-- Pointwise vanishing of a winding number is preserved by reversing the interval orientation,
under the principal-value existence hypothesis that makes the two winding-number values honest. -/
theorem windingNumber_eq_zero_symm (hzero : windingNumber γ a b z₀ = 0)
    (hpv : CauchyPVExistsAt γ a b κ[z₀] z₀) :
    windingNumber γ b a z₀ = 0 := by
  rw [windingNumber_symm hpv, hzero, neg_zero]

/-- Null-homology is preserved by reversing orientation, provided the pointwise principal values
defining the exterior winding numbers exist. -/
theorem IsNullHomologous.symm (h : IsNullHomologous γ a b Ω)
    (hpv : ∀ z ∉ Ω, CauchyPVExistsAt γ a b κ[z] z) :
    IsNullHomologous γ b a Ω := by
  rw [isNullHomologous_iff] at h ⊢
  intro z hz
  exact windingNumber_eq_zero_symm (h z hz) (hpv z hz)

/-- Null-homology is preserved by reversing orientation in the ordinary avoided-pole case. If the
curve lies in `Ω`, every exterior point is avoided, so the required principal values are ordinary
integrals. -/
theorem IsNullHomologous.symm_of_avoidance (h : IsNullHomologous γ a b Ω)
    (hγ : ∀ t ∈ Set.uIcc a b, γ t ∈ Ω)
    (hcont : ContinuousOn γ (Set.uIcc a b))
    (hint : ∀ z ∉ Ω,
      IntervalIntegrable (fun t => (γ t - z)⁻¹ * deriv γ t) MeasureTheory.volume a b) :
    IsNullHomologous γ b a Ω := by
  refine h.symm ?_
  intro z hz
  refine cauchyPVExistsAt_of_avoidance hcont ?_ (hint z hz)
  intro t ht htz
  exact hz (htz ▸ hγ t ht)

end TauCeti.Contour

end
