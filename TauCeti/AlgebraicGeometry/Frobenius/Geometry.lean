/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Frobenius.UniversalHomeomorphism
public import TauCeti.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

/-!
# Geometric properties of scheme Frobenius

Absolute and relative Frobenius are integral, universally injective and surjective for arbitrary
schemes in characteristic `p`. Consequently every base change of either map is a homeomorphism.
These results apply to nonreduced schemes and to the empty scheme; neither finite type nor
perfectness of the base is required. They provide the geometric input to perfection and
topological invariance of the small étale site.

The geometric properties and their iterated versions are supplied by
`TauCeti.AlgebraicGeometry.Frobenius.UniversalHomeomorphism`. This file packages the absolute
and relative maps as instances of `TauCeti.AlgebraicGeometry.IsUniversalHomeomorphism`.

## References

* The Stacks Project, [Tag 0CC6](https://stacks.math.columbia.edu/tag/0CC6), Frobenii.
* The Stacks Project, [Tag 01S4](https://stacks.math.columbia.edu/tag/01S4), the field-valued
  criterion for universal injectivity.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

universe u

variable {X S : _root_.AlgebraicGeometry.Scheme.{u}} {p : ℕ} [hp : Fact p.Prime]

/-- Absolute Frobenius remains a homeomorphism after every base change. -/
instance AlgebraicGeometry.absoluteFrobenius_universalHomeomorphism
    (hX : (p : Γ(X, ⊤)) = 0) : AlgebraicGeometry.IsUniversalHomeomorphism (X.frobenius p hX) :=
  (AlgebraicGeometry.isUniversalHomeomorphism_iff_isIntegralHom_universallyInjective_surjective
    _).mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

variable (π : X ⟶ S) (hS : (p : Γ(S, ⊤)) = 0)

/-- Relative Frobenius remains a homeomorphism after every base change, with no flatness or
perfectness hypothesis on the base. -/
instance AlgebraicGeometry.relativeFrobenius_universalHomeomorphism :
    AlgebraicGeometry.IsUniversalHomeomorphism (π.relativeFrobenius p hS) :=
  (AlgebraicGeometry.isUniversalHomeomorphism_iff_isIntegralHom_universallyInjective_surjective
    _).mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

end TauCeti
