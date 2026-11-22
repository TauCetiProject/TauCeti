/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import TauCeti.RingTheory.Derivation.BaseChange
import TauCeti.RingTheory.Derivation.Basic

/-!
# Coefficientwise lift of derivations to multivariate polynomials

For an `R`-algebra `B`, any `R`-derivation `d : Derivation R B B` lifts coefficientwise to an
`R`-derivation `d.mapCoeffsMvPolynomial` of `MvPolynomial σ B` acting by `d` on coefficients and
annihilating `X i`.

## Main definitions

* `Derivation.mapCoeffsMvPolynomial`: coefficientwise lift of `d : Derivation R B B` to
  `Derivation R (MvPolynomial σ B) (MvPolynomial σ B)`.

## Main results

* `Derivation.mapCoeffsMvPolynomial_monomial`, `Derivation.coeff_mapCoeffsMvPolynomial`,
  `Derivation.mapCoeffsMvPolynomial_C`, `Derivation.mapCoeffsMvPolynomial_X`: action of
  `mapCoeffsMvPolynomial` on monomials, arbitrary coefficients, constants, and variables.
-/

public section

namespace Derivation

open MvPolynomial TensorProduct

noncomputable section

variable {R B σ : Type*} [CommSemiring R] [CommSemiring B] [Algebra R B]

/-- Coefficientwise lift of a base derivation `d : Derivation R B B` to an `R`-derivation of
`MvPolynomial σ B`, built from `Derivation.baseChange` and `MvPolynomial.algebraTensorAlgEquiv`. -/
def mapCoeffsMvPolynomial (d : Derivation R B B) :
    Derivation R (MvPolynomial σ B) (MvPolynomial σ B) :=
  ((d.baseChange (MvPolynomial σ R)).restrictScalars R).conjAlgEquiv
    ((Algebra.TensorProduct.comm R (MvPolynomial σ R) B).trans
      ((MvPolynomial.algebraTensorAlgEquiv R B).restrictScalars R))

/-- `d.mapCoeffsMvPolynomial` acts on monomials `monomial m b` by `d` on the coefficient. -/
@[simp]
theorem mapCoeffsMvPolynomial_monomial (d : Derivation R B B) (m : σ →₀ ℕ) (b : B) :
    d.mapCoeffsMvPolynomial (monomial m b) = monomial m (d b) := by
  simp [mapCoeffsMvPolynomial, smul_monomial]

/-- `d.mapCoeffsMvPolynomial` applies `d` to every coefficient of a polynomial. -/
@[simp]
theorem coeff_mapCoeffsMvPolynomial (d : Derivation R B B) (p : MvPolynomial σ B) (m : σ →₀ ℕ) :
    (d.mapCoeffsMvPolynomial p).coeff m = d (p.coeff m) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n b => simp [coeff_monomial, apply_ite d]

/-- `d.mapCoeffsMvPolynomial` acts on base constants `C b` by `d`. -/
@[simp]
theorem mapCoeffsMvPolynomial_C (d : Derivation R B B) (b : B) :
    d.mapCoeffsMvPolynomial (σ := σ) (C b) = C (d b) := by
  rw [← monomial_zero', mapCoeffsMvPolynomial_monomial, monomial_zero']

/-- `d.mapCoeffsMvPolynomial` annihilates polynomial variables `X i`. -/
@[simp]
theorem mapCoeffsMvPolynomial_X (d : Derivation R B B) (i : σ) :
    d.mapCoeffsMvPolynomial (σ := σ) (X i) = 0 := by
  simp [mapCoeffsMvPolynomial]

end

end Derivation
