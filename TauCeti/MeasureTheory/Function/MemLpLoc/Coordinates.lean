/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.MemLpLoc.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Coordinates of locally `Lᵖ` maps

A map into a finite-dimensional real normed space is locally `Lᵖ` if and only if all its
coordinates in a finite basis are (`Module.Basis.memLpLoc_iff`). No completeness of the codomain
is required.
-/

public noncomputable section

open MeasureTheory TauCeti

namespace Module.Basis

variable {E F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Finite ι]
  {p : ENNReal}

/-- Local `Lᵖ` membership can be tested in any finite basis. No completeness of the
codomain is needed. -/
theorem memLpLoc_iff [TopologicalSpace E] [MeasureSpace E] {U : Set E} {f : E → F}
    (b : Module.Basis ι ℝ F) :
    MemLpLoc p U f ↔ ∀ i, MemLpLoc p U (fun z => b.repr (f z) i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  constructor
  · intro h i
    exact h.clm_comp ((ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap)
  · intro h
    have hs : MemLpLoc p U (fun z => ∑ i, b.repr (f z) i • b i) :=
      MemLpLoc.sum Finset.univ fun i _ =>
        (h i).clm_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight (b i))
    simpa only [b.sum_repr] using hs

end Module.Basis
