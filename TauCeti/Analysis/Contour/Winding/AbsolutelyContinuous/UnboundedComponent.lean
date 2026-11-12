/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ConstantSpeed
public import Mathlib.Topology.MetricSpace.Bounded
public import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.LocallyConstant
public import TauCeti.Topology.FilledHull
import TauCeti.Analysis.Contour.Winding.UnboundedComponent
import TauCeti.MeasureTheory.Function.MetricDerivative.ConstantSpeed

/-!
# Winding numbers of absolutely continuous curves on unbounded components

A closed absolutely continuous curve has winding number zero sufficiently far from its trace.
Local constancy then gives vanishing on every unbounded connected component of the complement, and
hence outside the filled hull of the trace (both directly for closed AC curves and for the
arclength parametrization of rectifiable closed curves).
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
  exact hγ.continuousOn.windingNumber_eventually_zero_cocompact_of_integer
    hγ.intervalIntegrable_deriv_of_finiteDimensional
    (fun _ hz ↦ hγ.exists_int_windingNumber hclosed hz)

/-- The winding number of a closed absolutely continuous curve vanishes on every unbounded
component of the complement of its trace. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_eq_zero_of_unbounded_component
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) {z : ℂ}
    (hz : ¬IsBounded (connectedComponentIn ((γ '' uIcc a b)ᶜ) z)) :
    windingNumber γ a b z = 0 := by
  exact hγ.continuousOn.windingNumber_eq_zero_of_unbounded_component_of_integer
    hγ.intervalIntegrable_deriv_of_finiteDimensional
    (fun _ hw ↦ hγ.exists_int_windingNumber hclosed hw) hz

/-- **The winding number of a closed absolutely continuous curve vanishes outside its filled
hull.** -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_eq_zero_of_notMem_filledHull
    {γ : ℝ → ℂ} {a b : ℝ} {z : ℂ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) (hz : z ∉ filledHull (γ '' uIcc a b)) :
    windingNumber γ a b z = 0 :=
  hγ.windingNumber_eq_zero_of_unbounded_component hclosed (mt mem_filledHull_iff.mpr hz)

/-- **Outside the filled hull of a continuous closed curve, the winding number of its natural
parametrization vanishes.** Here `naturalParameterization γ (Icc a b) a` runs over
`[0, (eVariationOn γ (Icc a b)).toReal]`. If `γ` has bounded variation and `a ≤ b`, this is the
arclength parametrization; otherwise the parameter interval is `[0, 0]` and the winding number is
`0`. -/
theorem _root_.ContinuousOn.windingNumber_naturalParameterization_eq_zero_of_notMem_filledHull
    {γ : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (hcont : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b)
    (hz : z ∉ filledHull (γ '' Icc a b)) :
    windingNumber (naturalParameterization γ (Icc a b) a) 0
        (eVariationOn γ (Icc a b)).toReal z = 0 := by
  by_cases hγ : BoundedVariationOn γ (Icc a b)
  swap
  · -- infinite variation: the parameter interval is degenerate
    have htop : eVariationOn γ (Icc a b) = ⊤ := by
      by_contra h
      exact hγ h
    rw [htop, ENNReal.toReal_top, windingNumber_same]
  rcases le_or_gt a b with hab | hab
  swap
  · rw [Icc_eq_empty (not_le.mpr hab), eVariationOn.subsingleton _ subsingleton_empty]
    simp
  have hz' : z ∉ filledHull (naturalParameterization γ (Icc a b) a ''
      uIcc 0 (eVariationOn γ (Icc a b)).toReal) := by
    rwa [uIcc_of_le ENNReal.toReal_nonneg, hγ.image_naturalParameterization_Icc hcont hab]
  exact (hγ.absolutelyContinuousOnInterval_naturalParameterization hcont
      hab).windingNumber_eq_zero_of_notMem_filledHull
    (hγ.naturalParameterization_zero_eq_naturalParameterization_toReal_eVariationOn hab hclosed) hz'

end TauCeti.Contour
