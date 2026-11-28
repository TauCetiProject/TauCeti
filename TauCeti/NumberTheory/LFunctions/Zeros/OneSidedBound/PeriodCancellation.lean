/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.JetSize
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.ModOne

/-!
# The CM normalization in the long-row jet estimate

The size of a jet uses the factor `M / Ω`, where `Ω` is the CM period scale, whereas the
expected prime sum uses the constant term of the signed prime remainder at modulus one.
These two normalizations contain the same logarithmic derivative of the quadratic
L-function. Its contribution cancels in the excess of the jet size over the expected
prime sum, making the lower endpoint of the level-prime window independent of that derivative.

The normalizations are those of `New.Parameters.bigOmega` and `New.Data.mainPrimeSum` in
`New/Reduction/Data/FieldsAndPlaces.lean` and `New/Reduction/PrimeSums.lean` of lsernau/grh-lean
at revision `72fead1`.
-/

public section

open DirichletCharacter Real

namespace TauCeti.OneSidedBound

/-- Express the logarithm of `M / Ω` through the constant term of the modulus-one signed
remainder. Here `D` is the root discriminant in the CM period scale `Ω`. -/
theorem log_div_jetScale_eq_add_logDerivMean {d : ℕ} [Fact d.Prime] (hd : d ≠ 2)
    {M D : ℝ} (hM : M ≠ 0) (hD : D ≠ 0) :
    log (M / (exp (eulerMascheroniConstant - (logDeriv (jacobiChar ℂ d).LFunction 1).re) *
      (2 * π) / D)) = log (M * D / (2 * π)) + 1 + (logDerivMean d 1 1).re := by
  have hc := congrArg Complex.re (logDerivMean_modOne_at_one d hd)
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re] at hc
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  rw [div_div_eq_mul_div, mul_comm (exp _), ← div_div,
    log_div (div_ne_zero (mul_ne_zero hM hD) hπ) (exp_ne_zero _), log_exp]
  linarith only [hc]

/-- Subtracting the expected prime sum from a jet of order `a` cancels the quadratic
logarithmic derivative exactly. `A` is the mean log weight of the places. -/
theorem jetSize_sub_expectedPrimeSum_eq {d : ℕ} [Fact d.Prime] (hd : d ≠ 2)
    {M D : ℝ} (hM : M ≠ 0) (hD : D ≠ 0) (a : ℕ) (A : ℝ) :
    jetSize (log (M / (exp (eulerMascheroniConstant -
        (logDeriv (jacobiChar ℂ d).LFunction 1).re) * (2 * π) / D))) a -
        a * (log a - A + (logDerivMean d 1 1).re) =
      log (a.factorial : ℝ) - a * log a + a * (A + log (M * D / (2 * π)) + 1) := by
  rw [log_div_jetScale_eq_add_logDerivMean hd hM hD, jetSize_def]
  ring

end TauCeti.OneSidedBound
