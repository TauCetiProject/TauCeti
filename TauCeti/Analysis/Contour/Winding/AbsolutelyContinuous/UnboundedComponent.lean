/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.LocallyConstant
public import Mathlib.Topology.MetricSpace.Bounded
import TauCeti.Analysis.Contour.Winding.Vanishing

/-!
# Winding numbers of absolutely continuous curves on unbounded components

A closed absolutely continuous curve has winding number zero sufficiently far from its trace.
Local constancy then gives vanishing on every unbounded connected component of the complement.
-/

public section

open Bornology Complex MeasureTheory Set

namespace TauCeti.Contour

/-- The winding number of a closed absolutely continuous curve is zero sufficiently far from the
origin, and such points lie off its trace. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_eventually_zero_cocompact
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) :
    ∀ᶠ z in Filter.cocompact ℂ,
      z ∉ γ '' uIcc a b ∧ windingNumber γ a b z = 0 := by
  have h := ContinuousOn.windingNumber_eventually_zero_cocompact_of_integer hγ.continuousOn
    hγ.intervalIntegrable_deriv_of_finiteDimensional fun z hz ↦
      hγ.exists_int_windingNumber hclosed
        (by rintro ⟨t, ht, heq⟩; exact hz t ht heq)
  filter_upwards [h] with z hz
  exact ⟨by rintro ⟨t, ht, heq⟩; exact hz.1 t ht heq, hz.2⟩

/-- The winding number of a closed absolutely continuous curve vanishes on every unbounded
component of the complement of its trace. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_eq_zero_of_unbounded_component
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) {z : ℂ}
    (hz : ¬IsBounded (connectedComponentIn ((γ '' uIcc a b)ᶜ) z)) :
    windingNumber γ a b z = 0 := by
  obtain ⟨K, hK, hKgood⟩ := Filter.mem_cocompact.mp
    (hγ.windingNumber_eventually_zero_cocompact hclosed)
  have hnotSubset : ¬connectedComponentIn ((γ '' uIcc a b)ᶜ) z ⊆ K :=
    fun hsubset ↦ hz (hK.isBounded.subset hsubset)
  obtain ⟨w, hw, hwK⟩ := Set.not_subset.mp hnotSubset
  exact (AbsolutelyContinuousOnInterval.windingNumber_eq_of_mem_connectedComponentIn
    hγ hclosed hw).symm.trans (hKgood hwK).2

end TauCeti.Contour
