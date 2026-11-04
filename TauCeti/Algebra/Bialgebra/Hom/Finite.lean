/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.Hom.Representable
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Basic
import TauCeti.RingTheory.WeilRestriction.Finite

/-!
# Homomorphisms from finite constant monoid schemes to finite monoid schemes

For a finite, finitely presented affine monoid scheme `Spec H` and a split finite monoid
scheme `Spec G` (for example, a finite constant monoid scheme), the scheme of homomorphisms
`Spec G → Spec H` is finite. The ambient scheme of maps is finite by the split-algebra
Weil restriction theorem, and the homomorphism equations define a closed subscheme.

This is a finiteness statement, not a flatness statement. It is used to prove finiteness
of the closed locus of Katz–Mazur generators.

## References

* N. M. Katz, B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §§1.6 and 1.10.
-/

public section

open scoped TensorProduct

namespace TauCeti.Bialgebra.HomAlgebra

variable {R H G : Type*} [CommRing R] [CommRing H] [CommRing G]
  [Bialgebra R H] [Bialgebra R G] [Algebra.FinitePresentation R H]
  [Module.Finite R G] [Module.Projective R G]

/-- The scheme of homomorphisms from a split finite monoid scheme to a finite,
finitely presented affine monoid scheme is finite over the base. -/
theorem moduleFinite_of_split [Module.Finite R H] {ι : Type*} [Finite ι]
    (e : G ≃ₐ[R] (ι → R)) : Module.Finite R (HomAlgebra R H G) := by
  have : Module.Finite R (TauCeti.Algebra.WeilRestriction R G (G ⊗[R] H)) :=
    TauCeti.Algebra.WeilRestriction.moduleFinite_of_split e
  -- `HomAlgebra` is the quotient of this Weil restriction by the homomorphism equations.
  infer_instance

/-- Homomorphisms from a finite constant monoid scheme to a finite, finitely presented
affine monoid scheme form a finite scheme. -/
instance (A : Type*) [Monoid A] [Finite A] [Module.Finite R H] :
    Module.Finite R (HomAlgebra R H (ConstantGroup.coordinateRing R A)) :=
  moduleFinite_of_split (ConstantGroup.functionAlgEquiv R A)

end TauCeti.Bialgebra.HomAlgebra
