/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Topology.Order.Compact

/-!
# Finite measure from a finite integral of a positive continuous density

A continuous real density `ρ` has a positive minimum on a nonempty compact set `K` on which it is
positive. So if `∫⁻ x in A ∩ S, ofReal (ρ x) ∂ν` is finite and `K ⊆ S`, then `ν (A ∩ K)` is finite
(`TauCeti.measure_inter_ne_top_of_setLIntegral_ne_top`), for every set `A` and every measure `ν`.
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
  {ν : Measure α} {ρ : α → ℝ} {A S K : Set α}

/-- If a continuous density `ρ`, positive on a compact set `K ⊆ S`, has finite set integral
`∫⁻ x in A ∩ S, ofReal (ρ x) ∂ν`, then `ν (A ∩ K)` is finite. -/
theorem measure_inter_ne_top_of_setLIntegral_ne_top (hρ : Continuous ρ) (hK : IsCompact K)
    (hpos : ∀ x ∈ K, 0 < ρ x) (hKS : K ⊆ S)
    (h : ∫⁻ x in A ∩ S, ENNReal.ofReal (ρ x) ∂ν ≠ ∞) : ν (A ∩ K) ≠ ∞ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨y, hyK, hy⟩ := hK.exists_isMinOn hne hρ.continuousOn
  have hle : ENNReal.ofReal (ρ y) * ν (A ∩ K) ≤ ∫⁻ x in A ∩ S, ENNReal.ofReal (ρ x) ∂ν :=
    calc ENNReal.ofReal (ρ y) * ν (A ∩ K)
        = ∫⁻ _ in A ∩ K, ENNReal.ofReal (ρ y) ∂ν := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in A ∩ K, ENNReal.ofReal (ρ x) ∂ν :=
          setLIntegral_mono hρ.measurable.ennreal_ofReal fun x hx =>
            ENNReal.ofReal_le_ofReal (hy hx.2)
      _ ≤ _ := lintegral_mono_set (inter_subset_inter_right _ hKS)
  intro htop
  rw [htop, ENNReal.mul_top (by simpa using hpos y hyK)] at hle
  exact h (top_le_iff.1 hle)

end TauCeti
