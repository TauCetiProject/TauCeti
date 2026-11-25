/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.LocallyConstant
public import TauCeti.Analysis.Contour.Winding.Vanishing

/-!
# The winding number on the unbounded component

For a closed curve `γ`, the winding number is constant on every connected component of the
complement of the curve. If such a component is unbounded, it contains a point outside the compact
set on which the far-field vanishing theorem gives no information. At that point the winding
number is zero, and componentwise constancy transports the value back to every point of the
component.

This proves the last part of the classical off-curve winding package: the winding number is zero on
the unbounded component.

## Main results

* `ContinuousOn.windingNumber_eq_zero_of_unbounded_component_of_integer` — the winding number of a
  curve with integer indices vanishes on every unbounded component of the curve complement.

The forms for a closed absolutely continuous curve, which cover piecewise-`C¹` curves, are in
`TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.UnboundedComponent`.

## References

* N. Hungerbühler and M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 (2018), Section 2.
-/

public section

open Bornology Complex MeasureTheory Set

open scoped Topology

namespace TauCeti.Contour

/-- A continuous curve with integrable derivative and integer indices has zero winding
number on every unbounded component of its trace complement. -/
theorem _root_.ContinuousOn.windingNumber_eq_zero_of_unbounded_component_of_integer
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : ContinuousOn γ (uIcc a b))
    (hderiv : IntervalIntegrable (deriv γ) volume a b)
    (hint : ∀ z, z ∉ γ '' uIcc a b → ∃ n : ℤ, windingNumber γ a b z = n)
    {z : ℂ} (hz : ¬IsBounded (connectedComponentIn ((γ '' uIcc a b)ᶜ) z)) :
    windingNumber γ a b z = 0 := by
  obtain ⟨K, hK, hKgood⟩ := Filter.mem_cocompact.mp
    (hγ.windingNumber_eventually_zero_cocompact_of_integer hderiv hint)
  have hnot : ¬connectedComponentIn ((γ '' uIcc a b)ᶜ) z ⊆ K :=
    fun hsubset ↦ hz (hK.isBounded.subset hsubset)
  obtain ⟨w, hw, hwK⟩ := Set.not_subset.mp hnot
  exact (hγ.windingNumber_eq_of_mem_connectedComponentIn_of_integer hderiv hint hw).symm.trans
    (hKgood hwK).2

end TauCeti.Contour
