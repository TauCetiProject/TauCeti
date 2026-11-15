/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Poincare.PowerSeries
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.DualNumbers
public import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# An Ext Poincaré series with infinite cohomological support

For the residue field `S` of the dual numbers with the nilpotent generator in degree two,
`Ext^{n,j}(S,S)` has dimension one at `j = 2n` and zero elsewhere. Its full Poincaré series is
therefore the geometric series `∑ n ≥ 0, q²ⁿ tⁿ`, characterized by multiplication with
`1 - q²t`. Every cohomological coefficient is nonzero, and this series is not a polynomial.

The computation reuses the existing graded dual-number Ext dimensions and Mathlib's geometric
power-series identity through `PowerSeries.rescale`. This example has slope two rather than
diagonal support; it defines neither an Euler pairing nor a Koszul Cartan identity.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 2.5 and Chapter 4,
  for the periodic resolution of the residue field of the dual numbers.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial

universe w u

attribute [local instance] dualNumberIntegerGradedAlgebra

variable (k : Type u) [Field k] [HasExt.{w} (GradedModuleCat.{u} (dualNumberIntegerGrade k))]

/-- Every cohomological coefficient of the dual-number residue field's full Poincaré series
is the nonzero Laurent monomial `q²ⁿ`. -/
theorem coeff_bigradedExtPoincarePowerSeries_dualNumberGradedResidue (n : ℕ) :
    PowerSeries.coeff n
      (bigradedExtPoincarePowerSeries k (GradedModuleCat.shift (dualNumberIntegerGrade k))
        (isGradedExtInternallyFinite_dualNumberGradedResidue.{w} k)) = T (2 * n : ℤ) := by
  ext j
  rw [coeff_coeff_bigradedExtPoincarePowerSeries, finrank_gradedExt_dualNumberGradedResidue]
  simp only [T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs <;> simp_all

/-- The full dual-number Poincaré series is the geometric series obtained by rescaling the
cohomological variable by `q²`. -/
theorem bigradedExtPoincarePowerSeries_dualNumberGradedResidue_eq_rescale :
    bigradedExtPoincarePowerSeries k (GradedModuleCat.shift (dualNumberIntegerGrade k))
      (isGradedExtInternallyFinite_dualNumberGradedResidue.{w} k) =
        PowerSeries.rescale (T 2) (PowerSeries.mk 1) := by
  apply PowerSeries.ext
  intro n
  rw [coeff_bigradedExtPoincarePowerSeries_dualNumberGradedResidue]
  simp [T_pow, mul_comm]

/-- The full series satisfies the geometric-series identity `P(t,q) (1 - q²t) = 1`.
The identity uses formal power-series multiplication, whose coefficients are finite sums. -/
theorem bigradedExtPoincarePowerSeries_dualNumberGradedResidue_mul_one_sub :
    bigradedExtPoincarePowerSeries k (GradedModuleCat.shift (dualNumberIntegerGrade k))
      (isGradedExtInternallyFinite_dualNumberGradedResidue.{w} k) *
        (1 - PowerSeries.C (T 2) * PowerSeries.X) = 1 := by
  rw [bigradedExtPoincarePowerSeries_dualNumberGradedResidue_eq_rescale]
  simpa [PowerSeries.rescale_X] using congrArg (PowerSeries.rescale (T (R := ℤ) 2))
    (PowerSeries.mk_one_mul_one_sub_eq_one (LaurentPolynomial ℤ))

/-- No Laurent-coefficient polynomial represents the full dual-number Ext Poincaré series:
its cohomological support is infinite. -/
theorem not_exists_polynomial_bigradedExtPoincarePowerSeries_dualNumberGradedResidue :
    ¬ ∃ p : Polynomial (LaurentPolynomial ℤ),
      (p : PowerSeries (LaurentPolynomial ℤ)) =
        bigradedExtPoincarePowerSeries k (GradedModuleCat.shift (dualNumberIntegerGrade k))
          (isGradedExtInternallyFinite_dualNumberGradedResidue.{w} k) := by
  rw [exists_polynomial_bigradedExtPoincarePowerSeries_iff]
  exact not_isGradedExtBounded_dualNumberGradedResidue k

end TauCeti
