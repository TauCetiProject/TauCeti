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
`R`-derivation `d.coeffDeriv` of `MvPolynomial σ B` acting by `d` on `C b` and annihilating `X i`.

## Main definitions

* `Derivation.coeffDeriv`: coefficientwise lift of `d : Derivation R B B` to
  `Derivation R (MvPolynomial σ B) (MvPolynomial σ B)`.

## Main results

* `Derivation.coeffDeriv_C`, `Derivation.coeffDeriv_X`: action of `coeffDeriv` on constants and
  variables.
-/

public section

namespace Derivation

open MvPolynomial TensorProduct

noncomputable section

variable {R B σ : Type*} [CommSemiring R] [CommSemiring B] [Algebra R B]

/-- Coefficientwise lift of a base derivation `d : Derivation R B B` to an `R`-derivation of
`MvPolynomial σ B`, built from `Derivation.baseChange` and `MvPolynomial.algebraTensorAlgEquiv`. -/
def coeffDeriv (d : Derivation R B B) : Derivation R (MvPolynomial σ B) (MvPolynomial σ B) :=
  ((d.baseChange (MvPolynomial σ R)).restrictScalars R).conjAlgEquiv
    ((Algebra.TensorProduct.comm R (MvPolynomial σ R) B).trans
      ((MvPolynomial.algebraTensorAlgEquiv R B).restrictScalars R))

/-- `d.coeffDeriv` acts on base constants `C b` by `d`. -/
@[simp]
theorem coeffDeriv_C (d : Derivation R B B) (b : B) :
    d.coeffDeriv (σ := σ) (C b) = C (d b) := by
  have h1 : (algebraTensorAlgEquiv (σ := σ) R B).symm (C b) = b ⊗ₜ[R] (1 : MvPolynomial σ R) := by
    simpa [monomial_zero'] using algebraTensorAlgEquiv_symm_monomial (σ := σ) R B 0 b
  have h2 : algebraTensorAlgEquiv (σ := σ) R B (d b ⊗ₜ[R] (1 : MvPolynomial σ R)) = C (d b) := by
    simp [algebraTensorAlgEquiv_tmul, Algebra.smul_def, MvPolynomial.algebraMap_eq]
  simp [coeffDeriv, h1, h2]

/-- `d.coeffDeriv` annihilates polynomial variables `X i`. -/
@[simp]
theorem coeffDeriv_X (d : Derivation R B B) (i : σ) :
    d.coeffDeriv (σ := σ) (X i) = 0 := by
  simp [coeffDeriv]

end

end Derivation
