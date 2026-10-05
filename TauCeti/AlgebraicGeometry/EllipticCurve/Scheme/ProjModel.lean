/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.CoordinateRing

/-!
# The projective Weierstrass model

For a Weierstrass curve `W` over a commutative ring `R`, the projective Weierstrass model is the
scheme over `R` cut out by the cubic

`Y²Z + a₁XYZ + a₃YZ² = X³ + a₂X²Z + a₄XZ² + a₆Z³`

in homogeneous coordinates `[X : Y : Z]`. It is constructed here as the `Proj` of the graded
homogeneous coordinate ring `WeierstrassCurve.Projective.CoordinateRing W`. No ellipticity
hypothesis is needed for the construction, for properness, or for the zero section `[0 : 1 : 0]`;
ellipticity enters only for smoothness.

The zero section is defined on the standard affine chart `D₊(Y)`, where it is the point
`X/Y = Z/Y = 0`.

## Main definitions

* `WeierstrassCurve.projModel W`: the projective Weierstrass model, a scheme.
* `WeierstrassCurve.projModelOver W`: its structure morphism to `Spec R`.
* `WeierstrassCurve.projModelZero W`: the zero section `[0 : 1 : 0]`, a morphism
  `Spec R ⟶ projModel W`, defined on the standard affine chart `D₊(Y)`.

## Main results

* `WeierstrassCurve.isProper_projModelOver`: the projective Weierstrass model is proper over the
  base.
* `WeierstrassCurve.projModelZero_projModelOver`: the zero section is a section of the structure
  morphism.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.2.
* P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, II.1.
-/

public section

open CategoryTheory AlgebraicGeometry MvPolynomial

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The **projective Weierstrass model** of `W`: the projective cubic
`Y²Z + a₁XYZ + a₃YZ² = X³ + a₂X²Z + a₄XZ² + a₆Z³` over `R`, as the `Proj` of the homogeneous
coordinate ring `R[X, Y, Z] ⧸ (W(X, Y, Z))` graded by total degree. -/
noncomputable abbrev projModel : Scheme.{u} :=
  Proj W.toProjective.grading

/-- The structure morphism `projModel W ⟶ Spec R` of the projective Weierstrass model: the
structure morphism of `Proj` to the spectrum of the degree-zero part, which is `R`. -/
noncomputable def projModelOver : W.projModel ⟶ Spec (.of R) :=
  Proj.toSpecZero W.toProjective.grading ≫
    Spec.map W.toProjective.gradingZeroEquiv.toRingEquiv.toCommRingCatIso.hom

/-- The projective Weierstrass model is proper over its base. -/
instance isProper_projModelOver : IsProper W.projModelOver := by
  unfold projModelOver
  infer_instance

/-- The coordinate `Y`, of degree one in the homogeneous coordinate ring. -/
private noncomputable abbrev projY : W.toProjective.CoordinateRing :=
  Ideal.Quotient.mk _ (X 1)

/-- The point `[0 : 1 : 0]` on the standard affine chart `D₊(Y)` of the projective model:
evaluation of the degree-zero part of the localization away from `Y` at `X/Y = Z/Y = 0`. -/
private noncomputable def awayYEvalZero :
    HomogeneousLocalization.Away W.toProjective.grading W.projY →+* R :=
  (IsLocalization.Away.lift (S := Localization.Away W.projY) W.projY
      (g := W.toProjective.evalZero.toRingHom) (by simp)).comp
    (algebraMap _ (Localization.Away W.projY))

/-- The **zero section** `[0 : 1 : 0]` of the projective Weierstrass model, a morphism
`Spec R ⟶ projModel W` through the standard affine chart `D₊(Y)`. -/
noncomputable def projModelZero : Spec (.of R) ⟶ W.projModel :=
  Spec.map (CommRingCat.ofHom W.awayYEvalZero) ≫
    Proj.awayι W.toProjective.grading W.projY
      (W.toProjective.mk_mem_grading (isHomogeneous_X R 1)) one_pos

/-- The zero section is a section of the structure morphism. -/
@[reassoc (attr := simp)]
theorem projModelZero_projModelOver : W.projModelZero ≫ W.projModelOver = 𝟙 _ := by
  rw [projModelZero, projModelOver, Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp,
    ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext r
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, awayYEvalZero,
    ← HomogeneousLocalization.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  simp [IsScalarTower.algebraMap_apply _ W.toProjective.CoordinateRing (Localization.Away W.projY),
    IsLocalization.Away.lift_eq]

end WeierstrassCurve
