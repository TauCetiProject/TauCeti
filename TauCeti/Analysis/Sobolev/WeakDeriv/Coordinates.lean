/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Finite-coordinate characterization of weak derivatives

Weak differentiation of a function with finite-dimensional real normed codomain is equivalent
to weak differentiation of its scalar coordinates in any finite basis. Each direction includes
local integrability and the distributional identity for every scalar coordinate, for any measure
and open set, including a zero-dimensional codomain.

## Main declarations

* `hasWeakLineDerivOn_iff_coordinates`: directional weak derivatives in scalar coordinates.
* `hasWeakFDerivOn_iff_coordinates`: the corresponding Fréchet weak derivative criterion.

## References

* L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.2.
-/

public noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Finite ι] {μ : Measure E} {Ω : Opens E}

/-- Weak directional differentiation with finite-dimensional codomain is equivalent to
weak differentiation of all scalar coordinates. -/
theorem hasWeakLineDerivOn_iff_coordinates (b : Module.Basis ι ℝ F)
    {u u' : E → F} {v : E} :
    HasWeakLineDerivOn μ Ω u u' v ↔
      ∀ i, HasWeakLineDerivOn μ Ω (fun x ↦ b.coord i (u x))
        (fun x ↦ b.coord i (u' x)) v := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  constructor
  · intro h i
    exact h.clm_comp (b.coord i).toContinuousLinearMap
  · intro h
    have hs := HasWeakLineDerivOn.sum Finset.univ (fun i _ ↦
      (h i).clm_comp (ContinuousLinearMap.toSpanSingleton ℝ (b i)))
    have hu : (fun x ↦ ∑ i, b.coord i (u x) • b i) = u := by
      funext x
      exact b.sum_repr (u x)
    have hu' : (fun x ↦ ∑ i, b.coord i (u' x) • b i) = u' := by
      funext x
      exact b.sum_repr (u' x)
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, hu, hu'] using hs

/-- A finite-dimensional weak Fréchet derivative is detected by scalar coordinates in any
finite basis of the codomain. -/
theorem hasWeakFDerivOn_iff_coordinates (b : Module.Basis ι ℝ F)
    {u : E → F} {D : E → E →L[ℝ] F} :
    HasWeakFDerivOn μ Ω u D ↔
      ∀ i, HasWeakFDerivOn μ Ω (fun x ↦ b.coord i (u x))
        (fun x ↦ (b.coord i).toContinuousLinearMap.comp (D x)) := by
  simp only [hasWeakFDerivOn_iff, hasWeakLineDerivOn_iff_coordinates b,
    ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap']
  exact forall_comm

end TauCeti
