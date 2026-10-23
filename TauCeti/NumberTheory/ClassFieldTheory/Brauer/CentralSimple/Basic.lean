/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Comparison
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Basic

/-!
# The cohomological Brauer group is the Brauer group of central simple algebras

Class field theory works with the cohomological Brauer group
`TauCeti.ClassFieldTheory.Br F = H²(G_F, (Fˢ)ˣ)`, on the coefficient object `unitsRep F` over
`Field.absoluteGaloisGroup F`. The crossed-product comparison
`TauCeti.brauerExplicitH2Equiv F` identifies Mathlib's `BrauerGroup F` of central simple algebras
with the explicit continuous `H²` of the separable-closure model `AbsoluteGaloisGroup F` with
coefficients `UnitsCoeff F`. Following it with `TauCeti.ClassFieldTheory.unitsRepH2Equiv F`, which
changes the model of the Galois group and of the coefficients, gives

```text
brauerGroupEquivBr F : Additive (BrauerGroup F) ≃+ Br F.
```

This is the bridge along which the local invariant `TauCeti.ClassFieldTheory.invMap` and the other
invariants of class field theory evaluate Brauer classes of central simple algebras, such as the
classes of quaternion algebras.

## Main definitions

* `TauCeti.ClassFieldTheory.brauerGroupEquivBr F`: the identification
  `Additive (BrauerGroup F) ≃+ Br F`.

## References

* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), §4.4.
* J.-P. Serre, *Local Fields*, Chapter X, §5.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

variable (F : Type) [Field F]

/-- **The Brauer group of central simple algebras is the cohomological Brauer group.** The
crossed-product comparison `TauCeti.brauerExplicitH2Equiv F` into the explicit model of
`H²(G_F, (Fˢ)ˣ)`, transported to the carrier `Br F` of class field theory. Multiplication of
Brauer classes goes to addition of cohomology classes. -/
def brauerGroupEquivBr : Additive (BrauerGroup F) ≃+ Br F :=
  (brauerExplicitH2Equiv F).trans (unitsRepH2Equiv F)

/-- `brauerGroupEquivBr` is the crossed-product comparison followed by the change of model to
`Br F`. -/
theorem brauerGroupEquivBr_apply (x : Additive (BrauerGroup F)) :
    brauerGroupEquivBr F x = unitsRepH2Equiv F (brauerExplicitH2Equiv F x) :=
  (rfl)

end TauCeti.ClassFieldTheory
