/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.NumberTheory.Padics.Measure.PhiPsi
import Mathlib.RingTheory.PowerSeries.Binomial

/-!
# Low-degree Mahler expansion and the Amice transform of Dirac measures

The square function has Mahler coefficients `0, 1, 2`, and pushforward by multiplication
by `p` sends the Amice transforms of the Dirac measures at zero and one to `1` and
`(1 + X) ^ p`. The zero measure has zero transform.
-/

public section

open Polynomial PadicInt AbstractMeasure

namespace TauCeti.Examples.Mahler

variable {p : ℕ} [Fact p.Prime]

/-- The square function has the expected two nonzero Mahler coefficients. -/
example (x : ℤ_[p]) : x ^ 2 = mahler 1 x + 2 * mahler 2 x := by
  rw [mahler_apply, mahler_apply, Ring.choose_one_right]
  have h := Ring.descPochhammer_eq_factorial_smul_choose x 2
  norm_num [descPochhammer_succ_right, descPochhammer_zero,
    Polynomial.smeval_mul, Polynomial.smeval_X, Polynomial.smeval_sub,
    Polynomial.smeval_C, nsmul_eq_mul] at h
  linear_combination h

/-- The Amice transform of the pushforward of the Dirac measure at zero is one. -/
example : amiceTransform (phiMeasure (dirac ℤ_[p] (0 : ℤ_[p]))) = 1 := by
  rw [phiMeasure_dirac, mul_zero]
  rw [show (1 : PowerSeries ℤ_[p]) = (1 + PowerSeries.X) ^ 0 by rw [pow_zero],
    ← PowerSeries.binomialSeries_nat (R := ℤ_[p])]
  ext n
  simp only [coeff_amiceTransform, dirac_apply, smul_eq_mul, mul_one, mahler_apply,
    PowerSeries.binomialSeries_coeff, Nat.cast_zero]

/-- The Amice transform of the pushforward of the Dirac measure at one is binomial. -/
example : amiceTransform (phiMeasure (dirac ℤ_[p] (1 : ℤ_[p]))) =
    (1 + PowerSeries.X : PowerSeries ℤ_[p]) ^ p := by
  rw [phiMeasure_dirac, mul_one]
  rw [← PowerSeries.binomialSeries_nat (R := ℤ_[p])]
  ext n
  simp only [coeff_amiceTransform, dirac_apply, smul_eq_mul, mul_one, mahler_apply,
    PowerSeries.binomialSeries_coeff]

/-- The Amice transform respects the zero measure. -/
example : amiceTransform (phiMeasure (0 : D(ℤ_[p], ℤ_[p]))) = 0 := by simp only [map_zero]

end TauCeti.Examples.Mahler
