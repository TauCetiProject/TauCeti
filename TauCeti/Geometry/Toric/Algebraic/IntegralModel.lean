/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.MonoidAlgebra.BaseChange
public import TauCeti.Geometry.Toric.Algebraic.AffineScheme

/-!
# Integral models and additive coordinates of affine toric schemes

For a cone's native dual semigroup `S`, the affine toric scheme is canonically the
spectrum of `AddMonoidAlgebra ℂ S`. Thus it is the complex base change of the integral
semigroup model `Spec (AddMonoidAlgebra ℤ S)`. The comparison preserves the existing
`affineCoordinateRing` and `affineToricScheme` carriers, using Mathlib's
`AddMonoidAlgebra.toMultiplicativeAlgEquiv` to change the additive notation for exponents.

Both comparisons are isomorphisms over `Spec ℂ`. The equation for the integral
projection identifies its coefficient map on the native coordinate ring.

## References

W. Fulton, *Introduction to Toric Varieties*, §1.2; D. Cox, J. Little and H. Schenck,
*Toric Varieties*, §§1.1–1.3.
-/

public section

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraMonoidAlgebra

namespace TauCeti.Toric

variable {V N : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup N]
  {i : N →+ V}

/-- The native affine toric scheme, in additive semigroup coordinates, over `Spec ℂ`. -/
noncomputable def affineToricSchemeIsoAddMonoidAlgebraSpec
    (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    Over.mk (Spec.algebraMap ℂ (affineCoordinateRing hi σ)) ≅
      Over.mk (Spec.algebraMap ℂ (AddMonoidAlgebra ℂ (dualSemigroup hi σ))) := by
  let e := AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ (dualSemigroup hi σ)
  refine Over.isoMk (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op) ?_
  simp only [Over.mk_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map,
    Spec.algebraMap, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext fun r ↦ e.commutes r

/-- The additive-coordinate comparison applies `Spec` to the native exponent-conversion map. -/
theorem affineToricSchemeIsoAddMonoidAlgebraSpec_hom_left
    (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    (affineToricSchemeIsoAddMonoidAlgebraSpec hi σ).hom.left =
      Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ
          (dualSemigroup hi σ)).toRingHom) :=
  (rfl)

/-- The inverse additive-coordinate comparison applies `Spec` to the inverse exponent map. -/
theorem affineToricSchemeIsoAddMonoidAlgebraSpec_inv_left
    (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    (affineToricSchemeIsoAddMonoidAlgebraSpec hi σ).inv.left =
      Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ
          (dualSemigroup hi σ)).symm.toRingHom) :=
  (rfl)

/-- The complex base change of the integral dual-semigroup model is the native affine
toric scheme, with its original coordinate ring, over `Spec ℂ`. -/
noncomputable def affineToricIntegralModelBaseChangeIso
    (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    Over.mk (pullback.snd
      (Spec.algebraMap ℤ (AddMonoidAlgebra ℤ (dualSemigroup hi σ)))
      (Spec.algebraMap ℤ ℂ)) ≅
        Over.mk (Spec.algebraMap ℂ (affineCoordinateRing hi σ)) :=
  AlgebraicGeometry.addMonoidAlgebraSpecBaseChangeIso ℤ ℂ (dualSemigroup hi σ) ≪≫
    (affineToricSchemeIsoAddMonoidAlgebraSpec hi σ).symm

/-- The base-change map is the semigroup base-change map followed by conversion to the
native toric coordinates. -/
theorem affineToricIntegralModelBaseChangeIso_hom_left
    (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    (affineToricIntegralModelBaseChangeIso hi σ).hom.left =
      (AlgebraicGeometry.addMonoidAlgebraSpecBaseChangeIso ℤ ℂ
        (dualSemigroup hi σ)).hom.left ≫
          (affineToricSchemeIsoAddMonoidAlgebraSpec hi σ).inv.left :=
  (rfl)

/-- The comparison commutes with the projection to the integral model. On coordinate rings,
this is extension of integral coefficients followed by the native exponent-conversion map. -/
@[reassoc (attr := simp↓)]
theorem affineToricIntegralModelBaseChangeIso_hom_fst
    (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    (affineToricIntegralModelBaseChangeIso hi σ).hom.left ≫
        Spec.map (CommRingCat.ofHom
          ((AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ
            (dualSemigroup hi σ)).toRingHom.comp
              (algebraMap (AddMonoidAlgebra ℤ (dualSemigroup hi σ))
                (AddMonoidAlgebra ℂ (dualSemigroup hi σ))))) =
      pullback.fst (Spec.algebraMap ℤ (AddMonoidAlgebra ℤ (dualSemigroup hi σ)))
        (Spec.algebraMap ℤ ℂ) := by
  rw [affineToricIntegralModelBaseChangeIso_hom_left,
    CommRingCat.ofHom_comp, Spec.map_comp,
    ← affineToricSchemeIsoAddMonoidAlgebraSpec_hom_left, Category.assoc,
    Over.inv_left_hom_left_assoc]
  exact AlgebraicGeometry.addMonoidAlgebraSpecBaseChangeIso_hom_fst ℤ ℂ
    (dualSemigroup hi σ)

end TauCeti.Toric
