/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.SymmetricPower.Polynomial
public import TauCeti.RepresentationTheory.SU2.SymmetricPower

/-!
# The polynomial model of the symmetric powers of `ℂ²`

The dictionary `TauCeti.symPowerRepEquivPolynomialRep` between symmetric tensors and forms
intertwines the symmetric powers `TauCeti.SU2.symPower` of the standard representation of `SU(2)`
with the substitution action `TauCeti.polynomialAction` of `SU(2)` on binary forms. With the
binary monomials `TauCeti.polynomialMonomial`, this gives the polynomial model of the symmetric
powers of `ℂ²` under `SU(2)`, in which explicit computations with these representations are
coordinate calculations with binary forms.

## Main results

* `TauCeti.coe_symPowerRepEquivPolynomialRep_symPower`: the dictionary intertwines the symmetric
  powers of the standard representation of `SU(2)` with substitution.

## References

* P. Etingof, *Lie Groups and Lie Algebras*, arXiv:2201.09397v5, §11.4, p. 63: the
  representations of `SL₂` on homogeneous polynomials in two variables.
-/

public section

open MvPolynomial Matrix
open scoped TensorProduct

namespace TauCeti

/-- The equivalence `TauCeti.symPowerRepEquivPolynomialRep` intertwines the symmetric powers
`TauCeti.SU2.symPower` of the standard representation of `SU(2)` with the substitution of
standard vectors. -/
theorem coe_symPowerRepEquivPolynomialRep_symPower {d : ℕ} (g : SU2) (x : Sym[ℂ]^d(Fin 2 → ℂ)) :
    (symPowerRepEquivPolynomialRep ℂ 2 d (SU2.symPower d g x) : MvPolynomial (Fin 2) ℂ) =
      polynomialAction (g : Matrix (Fin 2) (Fin 2) ℂ) (symPowerRepEquivPolynomialRep ℂ 2 d x) := by
  rw [SU2.symPower_apply, coe_symPowerRepEquivPolynomialRep_symPowerRep, SU2.coe_toGL]

end TauCeti
