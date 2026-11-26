/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gaussian.Accretive.Basic

/-!
# Integrability of strictly accretive complex Gaussians

For a complex matrix `A` with positive definite hermitian part, the shifted Gaussian
`x ↦ exp (-(star x ⬝ᵥ A *ᵥ (x - a)))` is integrable against Lebesgue measure on `ι → ℂ`.
The shift occurs only in the second factor of the quadratic expression, and `A` need not
be hermitian. This supplies the absolute integrability needed to use the Gaussian formula
in iterated integrals and convolution calculations.

The normalization is that of `integral_cexp_neg_star_dotProduct_mulVec`: its integral is
`π ^ Fintype.card ι / A.det`, including when the coordinate set is empty.

## References

The integral is the accretive Gaussian formula `New.Fock.integral_gauss` in
`src/Lib/General/Analysis/GaussianIntegral.lean` of
https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207.
The proof here derives integrability from the nonzero value of the existing integral formula.
-/

public section

open MeasureTheory Matrix

namespace TauCeti

/-- A complex Gaussian with a strictly accretive quadratic matrix and a shift in its second
factor is integrable against Lebesgue measure. -/
theorem integrable_cexp_neg_star_dotProduct_mulVec {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℂ} (hA : A.IsStrictlyAccretive) (a : ι → ℂ) :
    Integrable (fun x : ι → ℂ ↦ Complex.exp (-(star x ⬝ᵥ A *ᵥ (x - a)))) := by
  classical
  apply Integrable.of_integral_ne_zero
  rw [integral_cexp_neg_star_dotProduct_mulVec hA a]
  exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    (inv_ne_zero hA.det_ne_zero)

end TauCeti
