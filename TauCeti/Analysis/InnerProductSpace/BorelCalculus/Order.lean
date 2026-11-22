/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.Basic
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Order

/-!
# Self-adjointness and Loewner order bounds in the Borel functional calculus

A bounded measurable real-valued function `g : spectrum ℂ a → ℝ` on the spectrum of a normal
bounded operator `a : H →L[ℂ] H` defines a self-adjoint bounded Borel symbol
`BoundedBorelFunction.ofRealFunction g hg hbound`. Specializing the projection-valued measure
order lemmas (`TauCeti.ProjValMeasure.Order`) to `a.spectralPVM`, pointwise bounds `m ≤ g ≤ M`
on the spectrum become Loewner order inequalities `m • 1 ≤ g(a) ≤ M • 1`.

## Main declarations

* `ContinuousLinearMap.isSelfAdjoint_borelCalculus_ofRealFunction`: real-valued symbols produce
  self-adjoint operators.
* `ContinuousLinearMap.borelCalculus_ofRealFunction_nonneg`,
  `ContinuousLinearMap.smul_one_le_borelCalculus_ofRealFunction`,
  `ContinuousLinearMap.borelCalculus_ofRealFunction_le_smul_one`: Loewner order bounds for real
  Borel symbols.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990), §IX.2.
* W. Rudin, *Functional Analysis*, 2nd ed., McGraw–Hill (1991), Theorem 12.24.
-/

public section

noncomputable section

open MeasureTheory TauCeti
open scoped CStarAlgebra InnerProductSpace

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (a : H →L[ℂ] H) [IsStarNormal a]

/-- The Borel functional calculus sends real-valued symbols to self-adjoint operators. -/
theorem isSelfAdjoint_borelCalculus_ofRealFunction (g : spectrum ℂ a → ℝ) (hg : Measurable g)
    (hbound) :
    IsSelfAdjoint (a.borelCalculus (BoundedBorelFunction.ofRealFunction g hg hbound)) := by
  rw [← a.integral_spectralPVM]
  exact a.spectralPVM.isSelfAdjoint_integral_ofRealFunction g hg hbound

/-- A nonnegative real-valued Borel symbol produces a nonnegative operator in the Loewner order. -/
theorem borelCalculus_ofRealFunction_nonneg {g : spectrum ℂ a → ℝ} (hg : Measurable g) (hbound)
    (h0 : ∀ x, 0 ≤ g x) :
    0 ≤ a.borelCalculus (BoundedBorelFunction.ofRealFunction g hg hbound) := by
  rw [← a.integral_spectralPVM]
  exact a.spectralPVM.integral_ofRealFunction_nonneg hg hbound h0

/-- A lower bound `m ≤ g x` on the spectrum gives the Loewner lower bound `m • 1 ≤ g(a)`. -/
theorem smul_one_le_borelCalculus_ofRealFunction {g : spectrum ℂ a → ℝ} (hg : Measurable g)
    (hbound) {m : ℝ} (hm : ∀ x, m ≤ g x) :
    m • (1 : H →L[ℂ] H) ≤ a.borelCalculus (BoundedBorelFunction.ofRealFunction g hg hbound) := by
  rw [← a.integral_spectralPVM]
  exact a.spectralPVM.smul_one_le_integral_ofRealFunction hg hbound hm

/-- An upper bound `g x ≤ M` on the spectrum gives the Loewner upper bound `g(a) ≤ M • 1`. -/
theorem borelCalculus_ofRealFunction_le_smul_one {g : spectrum ℂ a → ℝ} (hg : Measurable g)
    (hbound) {M : ℝ} (hM : ∀ x, g x ≤ M) :
    a.borelCalculus (BoundedBorelFunction.ofRealFunction g hg hbound) ≤ M • (1 : H →L[ℂ] H) := by
  rw [← a.integral_spectralPVM]
  exact a.spectralPVM.integral_ofRealFunction_le_smul_one hg hbound hM

end ContinuousLinearMap
