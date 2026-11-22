/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.Basic
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Exponential

/-!
# Exponentials in the Borel functional calculus

For a normal bounded operator `a` on a complex Hilbert space `H`, specializing
`TauCeti.ProjValMeasure.integral_exp` to `a.spectralPVM` shows that `a.borelCalculus` commutes
with the Banach-algebra exponential `NormedSpace.exp`: `(exp f)(a) = exp (f(a))`.

## Main declarations

* `ContinuousLinearMap.borelCalculus_exp`: `a.borelCalculus (exp f) = exp (a.borelCalculus f)`.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990), §IX.2.
* W. Rudin, *Functional Analysis*, 2nd ed., McGraw–Hill (1991), Theorem 12.24.
-/

public section

noncomputable section

open TauCeti
open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (a : H →L[ℂ] H) [IsStarNormal a]

/-- **Exponential compatibility of the Borel functional calculus.** For every bounded Borel symbol
`f` on the spectrum of a normal operator `a`, `(exp f)(a) = exp (f(a))`. -/
theorem borelCalculus_exp (f : BoundedBorelFunction (spectrum ℂ a)) :
    a.borelCalculus (NormedSpace.exp f) = NormedSpace.exp (a.borelCalculus f) := by
  rw [← a.integral_spectralPVM]
  exact a.spectralPVM.integral_exp f

end ContinuousLinearMap
