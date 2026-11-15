/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Generator.Basic
public import TauCeti.Algebra.Bialgebra.Hom.Finite

/-!
# Finiteness of the scheme of generators

For a finite free affine monoid scheme `G` and a finite monoid `A`, the scheme of
Katz–Mazur `A`-generators of `G` is finite and finitely presented over the base.
Its coordinate algebra is the existing quotient by `generatorIdeal`. Finiteness follows
because it is a closed subscheme of the finite scheme of homomorphisms `A → G`.

For `A = ℤ/N`, this is finiteness of the generator scheme `Gˣ`. No cyclicity or invertibility
of `N` is needed, and no flatness assertion about the generator scheme is made.

## References

* N. M. Katz, B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §§1.10 and 6.1.
-/

public section

namespace TauCeti

variable (R H : Type*) [CommRing R] [CommRing H] [Bialgebra R H]
  [Module.Free R H] [Module.Finite R H] (A : Type*) [Monoid A] [Fintype A]

attribute [local instance] Module.finitePresentation_of_projective

/-- The coordinate algebra of the scheme of `A`-generators is module-finite over the base.
Together with its existing finite-presentation instance, this gives a finite scheme of
finite presentation, including when the order of `A` is not invertible. -/
instance : Module.Finite R
    (Bialgebra.HomAlgebra R H (ConstantGroup.coordinateRing R A) ⧸ generatorIdeal R H A) :=
  inferInstance

end TauCeti
