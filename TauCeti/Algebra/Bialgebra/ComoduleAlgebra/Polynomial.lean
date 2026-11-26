/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra
public import TauCeti.Algebra.Coalgebra.Comodule.SymmetricAlgebra.Polynomial

/-!
# Polynomial functions on a comodule as a comodule algebra

This file equips the polynomial functions `MvPolynomial ι R` on a finite-basis comodule over a
commutative Hopf algebra with their natural comodule-algebra structure, extending
`TauCeti.Comodule.polynomial`.

## Main declarations

* `TauCeti.ComoduleAlgebra.polynomial`: the comodule-algebra structure on `MvPolynomial ι R`
  extending `TauCeti.Comodule.polynomial H b`.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., I.2.
* J. S. Milne, *Algebraic Groups* (2017), §4.a.
-/

public section

namespace TauCeti.ComoduleAlgebra

variable {R H V ι : Type*} [CommSemiring R] [CommSemiring H] [HopfAlgebra R H]
  [AddCommMonoid V] [Module R V] [Comodule R H V] [Fintype ι] [DecidableEq ι]

variable (H) in
/-- The polynomial functions `MvPolynomial ι R` on a comodule `V` with finite basis `b` form a
comodule algebra over `H`, with underlying comodule `TauCeti.Comodule.polynomial H b`.

Like `TauCeti.Comodule.polynomial`, this is deliberately not a global instance. -/
@[expose, implicit_reducible]
noncomputable def polynomial (b : Module.Basis ι R V) : ComoduleAlgebra R H (MvPolynomial ι R) where
  toComodule := Comodule.polynomial H b
  coact_one := by let _ := Comodule.polynomial H b; rw [Comodule.polynomial_coact_apply, map_one]
  coact_mul p q := by
    let _ := Comodule.polynomial H b
    rw [Comodule.polynomial_coact_apply, Comodule.polynomial_coact_apply,
      Comodule.polynomial_coact_apply, map_mul]

end TauCeti.ComoduleAlgebra
