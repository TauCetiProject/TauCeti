/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Geometry.Symplectic.QuadraticForm

/-!
# Morse index bounds from complex positivity

For a real-valued function on a finite-dimensional real normed space with an almost complex
structure `J`, positivity of

`Hess f(v, v) + Hess f(Jv, Jv)`

away from zero bounds the Morse index by the complex dimension. This file states the result using
Tau Ceti's actual Hessian quadratic form and Morse index. The hypothesis is the pointwise
quadratic-form identity supplied by strict Levi positivity at a critical point.

## Main declarations

* `TauCeti.AlmostComplexStructure.morseIndex_le_complexFinrank_of_add_comp_posDef`: the Morse
  index is at most the complex dimension.
* `TauCeti.AlmostComplexStructure.two_mul_morseIndex_le_finrank_of_add_comp_posDef`: the equivalent
  real-dimension bound.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.
* R. Hain, *Notes on the Morse theory of complex manifolds*, Section 2.
-/

public section

open Module

namespace TauCeti.AlmostComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (J : TauCeti.AlmostComplexStructure E) (f : E → ℝ) (x : E)

/-- Positivity of the sum of the Hessian quadratic form and its pullback by `J` bounds the Morse
index by the complex dimension defined by `J`. -/
theorem morseIndex_le_complexFinrank_of_add_comp_posDef
    (h : (TauCeti.hessianQuadraticForm f x +
      (TauCeti.hessianQuadraticForm f x).comp J.toLinearMap).PosDef) :
    TauCeti.morseIndex f x ≤ J.complexFinrank := by
  rw [TauCeti.morseIndex_def]
  exact (TauCeti.hessianQuadraticForm f x).sigNeg_le_complexFinrank_of_add_comp_posDef J h

/-- Positivity of `Hess f(v, v) + Hess f(Jv, Jv)` implies that twice the Morse index is at most
the real dimension of the ambient space. -/
theorem two_mul_morseIndex_le_finrank_of_add_comp_posDef
    (h : (TauCeti.hessianQuadraticForm f x +
      (TauCeti.hessianQuadraticForm f x).comp J.toLinearMap).PosDef) :
    2 * TauCeti.morseIndex f x ≤ finrank ℝ E := by
  rw [TauCeti.morseIndex_def]
  exact (TauCeti.hessianQuadraticForm f x).two_mul_sigNeg_le_finrank_of_add_comp_posDef
    J.toLinearMap h

end TauCeti.AlmostComplexStructure
