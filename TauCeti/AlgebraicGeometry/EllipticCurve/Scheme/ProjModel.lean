/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.VariableChange
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic

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

An admissible change of variables `C` induces an isomorphism `projModel (C • W) ≅ projModel W`
over `Spec R` carrying the zero section to the zero section: `Proj` of the graded isomorphism of
homogeneous coordinate rings `WeierstrassCurve.Projective.variableChangeEquiv W C`.

## Main definitions

* `WeierstrassCurve.projModel W`: the projective Weierstrass model, a scheme.
* `WeierstrassCurve.projModelOver W`: its structure morphism to `Spec R`.
* `WeierstrassCurve.projModelZero W`: the zero section `[0 : 1 : 0]`, a morphism
  `Spec R ⟶ projModel W`, defined on the standard affine chart `D₊(Y)`.
* `WeierstrassCurve.projModelVariableChangeIso W C`: the isomorphism
  `projModel (C • W) ≅ projModel W` induced by a change of variables `C`.

## Main results

* `WeierstrassCurve.isProper_projModelOver`: the projective Weierstrass model is proper over the
  base.
* `WeierstrassCurve.projModelZero_projModelOver`: the zero section is a section of the structure
  morphism.
* `WeierstrassCurve.projModelVariableChangeIso_hom_projModelOver` and
  `WeierstrassCurve.projModelZero_projModelVariableChangeIso_hom`: the isomorphism induced by a
  change of variables lies over `Spec R` and preserves the zero section.

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
  HomogeneousLocalization.Away.lift _ W.toProjective.evalZero.toRingHom (f := W.projY) (by simp)

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
  simp [awayYEvalZero, ← HomogeneousLocalization.algebraMap_eq]

section VariableChange

variable (C : VariableChange R)

/-- `Projective.variableChangeEquiv W C` as a graded ring homomorphism. -/
private noncomputable def variableChangeGradedHom :
    W.toProjective.grading →+*ᵍ (C • W).toProjective.grading where
  __ := (Projective.variableChangeEquiv W C).toRingEquiv.toRingHom
  map_mem := Projective.variableChangeEquiv_mem_grading W C

/-- The inverse of `Projective.variableChangeEquiv W C` as a graded ring homomorphism. -/
private noncomputable def variableChangeGradedHomSymm :
    (C • W).toProjective.grading →+*ᵍ W.toProjective.grading where
  __ := (Projective.variableChangeEquiv W C).symm.toRingEquiv.toRingHom
  map_mem := Projective.variableChangeEquiv_symm_mem_grading W C

private theorem variableChangeGradedHom_apply (x : W.toProjective.CoordinateRing) :
    variableChangeGradedHom W C x = Projective.variableChangeEquiv W C x :=
  rfl

private theorem rightInverse_variableChangeGradedHomSymm :
    Function.RightInverse (variableChangeGradedHomSymm W C) (variableChangeGradedHom W C) :=
  (Projective.variableChangeEquiv W C).apply_symm_apply

private theorem leftInverse_variableChangeGradedHomSymm :
    Function.LeftInverse (variableChangeGradedHomSymm W C) (variableChangeGradedHom W C) :=
  (Projective.variableChangeEquiv W C).symm_apply_apply

/-- The isomorphism `projModel (C • W) ≅ projModel W` of projective Weierstrass models induced by
the change of variables `C`. On homogeneous coordinates it is
`[X : Y : Z] ↦ [u²X + rZ : u²sX + u³Y + tZ : Z]`, so on the affine part it is
`(x, y) ↦ (u²x + r, u³y + u²sx + t)`. -/
noncomputable def projModelVariableChangeIso : (C • W).projModel ≅ W.projModel :=
  Proj.mapIso (variableChangeGradedHom W C) (variableChangeGradedHomSymm W C)
    (rightInverse_variableChangeGradedHomSymm W C) (leftInverse_variableChangeGradedHomSymm W C)

/-- The isomorphism induced by a change of variables lies over the base. -/
@[reassoc (attr := simp)]
theorem projModelVariableChangeIso_hom_projModelOver :
    (W.projModelVariableChangeIso C).hom ≫ W.projModelOver = (C • W).projModelOver := by
  rw [projModelVariableChangeIso, Proj.mapIso_hom, projModelOver, Proj.map_toSpecZero_assoc,
    projModelOver, ← Spec.map_comp]
  congr 2
  ext r
  simp [variableChangeGradedHom]

/-- The isomorphism induced by a change of variables carries the zero section to the zero
section: `[0 : 1 : 0] ↦ [0 : u³ : 0] = [0 : 1 : 0]`. -/
@[reassoc (attr := simp)]
theorem projModelZero_projModelVariableChangeIso_hom :
    (C • W).projModelZero ≫ (W.projModelVariableChangeIso C).hom = W.projModelZero := by
  have hY : W.projY ∈ W.toProjective.grading 1 :=
    W.toProjective.mk_mem_grading (isHomogeneous_X R 1)
  -- the image `u²sX + u³Y + tZ` of `Y` under the change of variables is `u³` at `[0 : 1 : 0]`
  have hFY :
      IsUnit ((C • W).toProjective.evalZero.toRingHom (variableChangeGradedHom W C W.projY)) := by
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, variableChangeGradedHom_apply,
      Projective.evalZero_variableChangeEquiv W C hY]
    simp [projY]
  rw [projModelVariableChangeIso, Proj.mapIso_hom, projModelZero, projModelZero, awayYEvalZero,
    awayYEvalZero, Proj.SpecMap_awayLift_awayι_eq _ _ one_pos
      (GradedFunLike.map_mem (variableChangeGradedHom W C) hY) one_pos _ hFY,
    Category.assoc, Proj.awayι_comp_map _ _ one_pos _ hY, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, HomogeneousLocalization.Away.lift_comp_map]
  congr 3
  exact HomogeneousLocalization.Away.lift_eq_of_forall_mem _ _ (C.u ^ 3)
    (fun n a ha ↦ by
      rw [Units.val_pow_eq_pow_val]
      exact Projective.evalZero_variableChangeEquiv W C ha) hY _ _

end VariableChange

end WeierstrassCurve
