/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.ComplexIndex
public import TauCeti.Geometry.Manifold.Morse.Index

/-!
# Complex bounds for the manifold Morse index

The manifold Morse index is the negative inertia of the Hessian in the preferred extended chart.
When that coordinate Hessian satisfies the strict complex positivity condition

`Hess f(v, v) + Hess f(Jv, Jv) > 0`,

its index is at most the complex dimension defined by `J`. The intrinsic critical-point
Levi--Hessian comparison can use this result after identifying its tangent almost complex
structure with the model-space structure.

## Main declaration

* `TauCeti.AlmostComplexStructure.manifoldMorseIndex_le_complexFinrank_of_add_comp_posDef`: the
  preferred-chart manifold Morse index is at most the complex dimension.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.
* R. Hain, *Notes on the Morse theory of complex manifolds*, Section 2.
-/

public section

namespace TauCeti.AlmostComplexStructure

variable {E H M : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable [TopologicalSpace M] [ChartedSpace H M]
variable (J : TauCeti.AlmostComplexStructure E) (f : M → ℝ) (x : M)

/-- If the Hessian in the preferred extended chart is strictly complex-positive, then the
manifold Morse index is at most the complex dimension defined by `J`. -/
theorem manifoldMorseIndex_le_complexFinrank_of_add_comp_posDef
    (h : (TauCeti.hessianQuadraticForm (f ∘ (extChartAt I x).symm) (extChartAt I x x) +
      (TauCeti.hessianQuadraticForm (f ∘ (extChartAt I x).symm) (extChartAt I x x)).comp
        J.toLinearMap).PosDef) :
    TauCeti.manifoldMorseIndex I f x ≤ J.complexFinrank := by
  rw [TauCeti.manifoldMorseIndex_def]
  exact J.morseIndex_le_complexFinrank_of_add_comp_posDef
    (f ∘ (extChartAt I x).symm) (extChartAt I x x) h

end TauCeti.AlmostComplexStructure
