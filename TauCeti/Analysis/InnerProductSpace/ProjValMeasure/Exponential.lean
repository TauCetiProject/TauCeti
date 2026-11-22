/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Integral

/-!
# Exponentials in projection-valued measure integrals

For a projection-valued measure `P : ProjValMeasure X H`, the operator integral `P.integral` is
continuous (`ProjValMeasure.continuous_integral`), so by `NormedSpace.map_exp` it commutes with
the Banach-algebra exponential `NormedSpace.exp`: `∫ exp f dP = exp (∫ f dP)`.

## Main declarations

* `TauCeti.ProjValMeasure.integral_exp`:
  `P.integral (NormedSpace.exp f) = NormedSpace.exp (P.integral f)`.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990), §IX.2.
* W. Rudin, *Functional Analysis*, 2nd ed., McGraw–Hill (1991), Theorem 12.24.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace TauCeti
namespace ProjValMeasure

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Exponential compatibility of projection-valued measure integrals.** For every bounded Borel
symbol `f : BoundedBorelFunction X`, `∫ exp f dP = exp (∫ f dP)`. -/
theorem integral_exp (P : ProjValMeasure X H) (f : BoundedBorelFunction X) :
    P.integral (NormedSpace.exp f) = NormedSpace.exp (P.integral f) := by
  let +nondep : NormedAlgebra ℚ (BoundedBorelFunction X) := .restrictScalars ℚ ℂ _
  let +nondep : NormedAlgebra ℚ (H →L[ℂ] H) := .restrictScalars ℚ ℂ _
  exact NormedSpace.map_exp P.integral P.continuous_integral f

end ProjValMeasure
end TauCeti
