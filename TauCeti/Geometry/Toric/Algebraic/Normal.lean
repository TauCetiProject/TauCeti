/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.MonoidAlgebra.Normal
public import TauCeti.Geometry.Toric.Algebraic.Fan.Scheme
public import TauCeti.Geometry.Toric.Algebraic.IntegralModel
import Mathlib.Algebra.Module.Torsion.Pi

/-!
# Normality of toric coordinate rings, integral models, and toric schemes

Every pointed cone `σ` in an integral lattice `(N, V, i)` has a saturated dual semigroup
`dualSemigroup hi σ ≤ (N →+ ℤ)` (`TauCeti.Toric.dualSemigroup_nsmulSaturated`), and the character
group `N →+ ℤ` is torsion-free over `ℤ`. Applying
`AddSubmonoid.isIntegrallyClosed_addMonoidAlgebra_of_nsmulSaturated` shows that the dual-semigroup
algebra `AddMonoidAlgebra R (dualSemigroup hi σ)` over any integrally closed domain `R` is an
integrally closed domain, with no rationality, salience, or finite-generation hypothesis on `σ`.

Specializing to `R = ℤ` and `R = ℂ` shows that:

* the integral dual-semigroup model `addMonoidAlgebraIntegralModel (dualSemigroup hi σ)` is a
  normal scheme;
* the complex coordinate ring `affineCoordinateRing hi σ` is an integrally closed domain and its
  spectrum `affineToricScheme hi σ` (the complex base change of the integral model) is a normal
  scheme;
* the toric scheme `Φ.algebraicRealization` of any finite fan `Φ`—glued from its normal affine
  toric charts along open immersions—is a normal scheme, even when the cones of `Φ` are singular.

## Main declarations

* `TauCeti.Toric.isDomain_addMonoidAlgebra_dualSemigroup` and
  `TauCeti.Toric.isIntegrallyClosed_addMonoidAlgebra_dualSemigroup`: over an integrally closed
  domain `R`, `AddMonoidAlgebra R (dualSemigroup hi σ)` is an integrally closed domain.
* `TauCeti.Toric.isDomain_affineCoordinateRing` and
  `TauCeti.Toric.isIntegrallyClosed_affineCoordinateRing`: `affineCoordinateRing hi σ` is an
  integrally closed domain.
* `TauCeti.Toric.isNormalScheme_addMonoidAlgebraIntegralModel_dualSemigroup`: the integral model of
  any cone's dual semigroup is a normal scheme.
* `TauCeti.Toric.isNormalScheme_affineToricScheme`: the native affine toric scheme of any cone is
  normal.
* `TauCeti.Toric.Fan.isNormalScheme_algebraicRealization`: the toric scheme of any finite fan is
  normal.

## References

* W. Fulton, *Introduction to Toric Varieties*, §2.1, Proposition (p. 29).
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, Theorem 1.3.5 and Theorem 3.1.19.
-/

public section

open AlgebraicGeometry
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric

section Cone

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

private theorem isTorsionFree_characterGroup : Module.IsTorsionFree ℤ (N →+ ℤ) :=
  (DFunLike.coe_injective (F := N →+ ℤ)).moduleIsTorsionFree DFunLike.coe fun _ _ ↦ rfl

/-- Over any integral domain `R`, the dual-semigroup algebra of a cone is an integral domain. -/
instance isDomain_addMonoidAlgebra_dualSemigroup (R : Type*) [CommRing R] [IsDomain R]
    (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    IsDomain (AddMonoidAlgebra R (dualSemigroup hi σ)) :=
  have := isTorsionFree_characterGroup (N := N)
  inferInstance

/-- Over any integrally closed domain `R`, the dual-semigroup algebra of a cone is integrally
closed. -/
instance isIntegrallyClosed_addMonoidAlgebra_dualSemigroup (R : Type*) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    IsIntegrallyClosed (AddMonoidAlgebra R (dualSemigroup hi σ)) :=
  have := isTorsionFree_characterGroup (N := N)
  AddSubmonoid.isIntegrallyClosed_addMonoidAlgebra_of_nsmulSaturated R
    (dualSemigroup_nsmulSaturated hi σ)

/-- The complex coordinate ring of the affine toric chart of any cone is an integral domain. -/
instance isDomain_affineCoordinateRing (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    IsDomain (affineCoordinateRing hi σ) :=
  (AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ
    (dualSemigroup hi σ)).symm.toRingEquiv.toMulEquiv.isDomain _

/-- The complex coordinate ring of the affine toric chart of any cone is integrally closed. -/
instance isIntegrallyClosed_affineCoordinateRing (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    IsIntegrallyClosed (affineCoordinateRing hi σ) :=
  IsIntegrallyClosed.of_equiv
    (AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ (dualSemigroup hi σ)).toRingEquiv

/-- The integral dual-semigroup model `Spec ℤ[S_σ]` of any cone is a normal scheme. -/
instance isNormalScheme_addMonoidAlgebraIntegralModel_dualSemigroup
    (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    IsNormalScheme (addMonoidAlgebraIntegralModel (dualSemigroup hi σ)) :=
  have := isTorsionFree_characterGroup (N := N)
  isNormalScheme_addMonoidAlgebraIntegralModel_of_nsmulSaturated
    (dualSemigroup_nsmulSaturated hi σ)

/-- The native affine toric scheme of any cone is normal. -/
instance isNormalScheme_affineToricScheme (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    IsNormalScheme (affineToricScheme hi σ) :=
  isNormalScheme_Spec (.of (affineCoordinateRing hi σ))

end Cone

namespace Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

/-- Every toric scheme associated to a finite fan is normal, regardless of whether its cones are
regular. -/
instance isNormalScheme_algebraicRealization (Φ : Fan i) :
    IsNormalScheme Φ.algebraicRealization :=
  (isNormalScheme_iff_openCover Φ.affineToricOpenCover).mpr fun σ ↦
    isNormalScheme_affineToricScheme Φ.lattice σ.1

end Fan

end TauCeti.Toric
