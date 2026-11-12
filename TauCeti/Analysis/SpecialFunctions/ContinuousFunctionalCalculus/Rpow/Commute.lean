/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Real powers of commuting elements

The real power `a ^ y = cfc (fun x : ℝ≥0 ↦ x ^ y) a` of the continuous functional calculus is a
continuous function of `a`, so it commutes with every element commuting with `a`. This is the
`CFC.rpow` case of `Commute.cfc_nnreal`.

## Main results

* `Commute.rpow_left`: if `a` commutes with `b`, so does `a ^ y`.
* `Commute.rpow_right`: if `a` commutes with `b`, then `a` commutes with `b ^ y`.
-/

public section

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [TopologicalSpace A]
  [StarOrderedRing A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [IsTopologicalRing A] [T2Space A] {a b : A}

namespace Commute

/-- A real power of `a` commutes with every element commuting with `a`. -/
@[grind ←]
protected theorem rpow_left (h : Commute a b) (y : ℝ) : Commute (a ^ y) b := by
  rw [CFC.rpow_def]
  exact h.cfc_nnreal _

/-- Every element commuting with `b` commutes with a real power of `b`. -/
@[grind ←]
protected theorem rpow_right (h : Commute a b) (y : ℝ) : Commute a (b ^ y) :=
  (h.symm.rpow_left y).symm

end Commute
