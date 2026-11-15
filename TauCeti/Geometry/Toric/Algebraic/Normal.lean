/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.Hom
public import TauCeti.AlgebraicGeometry.MonoidAlgebra.Normal
public import TauCeti.Geometry.Toric.Algebraic.AffineScheme

/-!
# Normality of toric coordinate rings, integral models, and affine toric schemes

Every pointed cone `σ` in an integral lattice `(N, V, i)` has a saturated dual semigroup
`dualSemigroup hi σ ≤ (N →+ ℤ)` (`TauCeti.Toric.nsmulSaturated_dualSemigroup`), and the character
group `N →+ ℤ` is torsion-free over `ℤ` (`AddMonoidHom.instModuleIsTorsionFree`). Together with
`TauCeti.Algebra.Group.UniqueProds.TorsionFree` and
`AddMonoidAlgebra.isIntegrallyClosed_of_nsmulSaturated`, this shows that the
dual-semigroup algebra `AddMonoidAlgebra R (dualSemigroup hi σ)` over any integrally closed domain
`R` is an integrally closed domain, with no rationality, salience, or finite-generation hypothesis
on `σ`.

Specializing to `R = ℤ` and `R = ℂ` shows that:

* the integral dual-semigroup model `addMonoidAlgebraIntegralModel (dualSemigroup hi σ)` is a
  normal scheme;
* the complex coordinate ring `affineCoordinateRing hi σ` is an integrally closed domain and its
  spectrum `affineToricScheme hi σ` (the complex base change of the integral model) is a normal
  scheme.

For normality of the glued toric scheme of a finite fan, see
`TauCeti.Geometry.Toric.Algebraic.Fan.Normal`.

## Main declarations

* `TauCeti.Toric.isIntegrallyClosed_addMonoidAlgebra_dualSemigroup`: over an integrally closed
  domain `R`, `AddMonoidAlgebra R (dualSemigroup hi σ)` is integrally closed.
* `TauCeti.Toric.isIntegrallyClosed_affineCoordinateRing`: `affineCoordinateRing hi σ` is
  integrally closed.
* `TauCeti.Toric.isNormalScheme_addMonoidAlgebraIntegralModel_dualSemigroup`: the integral model of
  any cone's dual semigroup is a normal scheme.
* `TauCeti.Toric.isNormalScheme_affineToricScheme`: the native affine toric scheme of any cone is
  normal.

## References

* W. Fulton, *Introduction to Toric Varieties*, §2.1, Proposition (p. 29).
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, Theorem 1.3.5.
-/

public section

open AlgebraicGeometry
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

/-- Over any integrally closed domain `R`, the dual-semigroup algebra of a cone is integrally
closed. -/
instance isIntegrallyClosed_addMonoidAlgebra_dualSemigroup (R : Type*) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    IsIntegrallyClosed (AddMonoidAlgebra R (dualSemigroup hi σ)) :=
  AddMonoidAlgebra.isIntegrallyClosed_of_nsmulSaturated (nsmulSaturated_dualSemigroup hi σ)

/-- The complex coordinate ring of the affine toric chart of any cone is integrally closed. -/
instance isIntegrallyClosed_affineCoordinateRing (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    IsIntegrallyClosed (affineCoordinateRing hi σ) :=
  IsIntegrallyClosed.of_equiv
    (AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ (dualSemigroup hi σ)).toRingEquiv

/-- The integral dual-semigroup model `Spec ℤ[S_σ]` of any cone is a normal scheme. -/
instance isNormalScheme_addMonoidAlgebraIntegralModel_dualSemigroup
    (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    IsNormalScheme (addMonoidAlgebraIntegralModel (dualSemigroup hi σ)) :=
  isNormalScheme_addMonoidAlgebraIntegralModel_of_nsmulSaturated
    (nsmulSaturated_dualSemigroup hi σ)

/-- The native affine toric scheme of any cone is normal. -/
instance isNormalScheme_affineToricScheme (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    IsNormalScheme (affineToricScheme hi σ) :=
  isNormalScheme_Spec (.of (affineCoordinateRing hi σ))

end TauCeti.Toric
