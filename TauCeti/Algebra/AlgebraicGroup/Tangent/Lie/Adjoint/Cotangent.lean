/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Cotangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Representation

/-!
# The adjoint action on the cotangent-dual Lie algebra

For a Hopf algebra with finite projective cotangent space, the adjoint point representation acts
on scalar extensions of the cotangent dual. After the scalar-extension comparison, this action is
convolution conjugation, so it preserves the Lie bracket.

## Main declarations

* `Derivation.adjointLieEquiv`: every algebra-valued point acts by Lie algebra
  automorphisms on the scalar-extended tangent space.
* `Derivation.adjointAction_bracket`: the established adjoint action preserves brackets.
* `Derivation.endOfPoint_adjointComodule_bracket`: so does the point action of the adjoint
  comodule.
* `Derivation.endOfPoint_adjointComodule_comp_baseChange_ad`: a point fixing `x` commutes with
  `ad x`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a and item 10.20.
-/

public section

open scoped TensorProduct

namespace Derivation

open TauCeti

universe u v

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
variable [Module.Projective R (Bialgebra.CotangentSpace R H)]

/-- The adjoint point action preserves the bracket on the scalar-extended tangent space. -/
@[simp]
theorem adjointAction_bracket
    (A : CommAlgCat.{max u v} R) (g : HopfAlgebra.points (H := H) A)
    (x y : A ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H)) :
    (adjointAction A g).val ⁅x, y⁆ =
      ⁅(adjointAction A g).val x, (adjointAction A g).val y⁆ := by
  apply (tangentScalarExtensionEquiv (R := R) (A := H) (B := A)).injective
  rw [tangentScalarExtensionEquiv_bracket,
    tangentScalarExtensionEquiv_adjointAction,
    tangentScalarExtensionEquiv_bracket,
    tangentScalarExtensionEquiv_adjointAction,
    tangentScalarExtensionEquiv_adjointAction]
  exact adDerivation_lie A (pointInCounitAlgebra A g) _ _

/-- The point action of the adjoint comodule preserves the bracket on the scalar-extended
tangent space. -/
@[simp]
theorem endOfPoint_adjointComodule_bracket
    (A : CommAlgCat.{max u v} R) (g : HopfAlgebra.points (H := H) A)
    (x y : A ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H)) :
    letI := adjointComodule (R := R) (H := H)
    Comodule.endOfPoint (Module.Dual R (Bialgebra.CotangentSpace R H)) g.ofConv ⁅x, y⁆ =
      ⁅Comodule.endOfPoint (Module.Dual R (Bialgebra.CotangentSpace R H)) g.ofConv x,
        Comodule.endOfPoint (Module.Dual R (Bialgebra.CotangentSpace R H)) g.ofConv y⁆ := by
  apply (tangentScalarExtensionEquiv (R := R) (A := H) (B := A)).injective
  rw [tangentScalarExtensionEquiv_bracket,
    tangentScalarExtensionEquiv_adjointComodule_endOfPoint,
    tangentScalarExtensionEquiv_bracket,
    tangentScalarExtensionEquiv_adjointComodule_endOfPoint,
    tangentScalarExtensionEquiv_adjointComodule_endOfPoint]
  exact adDerivation_lie A (pointInCounitAlgebra A g) _ _

/-- A point of the adjoint comodule that fixes `1 ⊗ x` commutes with the base change of `ad x`,
since it preserves brackets and the base change of `ad x` is the bracket with `1 ⊗ x`. -/
theorem endOfPoint_adjointComodule_comp_baseChange_ad
    (A : CommAlgCat.{max u v} R) (g : HopfAlgebra.points (H := H) A)
    (x : Module.Dual R (Bialgebra.CotangentSpace R H))
    (hg : letI := adjointComodule (R := R) (H := H)
      Comodule.endOfPoint (Module.Dual R (Bialgebra.CotangentSpace R H)) g.ofConv
        (1 ⊗ₜ[R] x) = 1 ⊗ₜ[R] x) :
    letI := adjointComodule (R := R) (H := H)
    Comodule.endOfPoint (Module.Dual R (Bialgebra.CotangentSpace R H)) g.ofConv ∘ₗ
        (LieAlgebra.ad R (Module.Dual R (Bialgebra.CotangentSpace R H)) x).baseChange A =
      (LieAlgebra.ad R (Module.Dual R (Bialgebra.CotangentSpace R H)) x).baseChange A ∘ₗ
        Comodule.endOfPoint (Module.Dual R (Bialgebra.CotangentSpace R H)) g.ofConv := by
  let := adjointComodule (R := R) (H := H)
  have had (z : A ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H)) :
      (LieAlgebra.ad R (Module.Dual R (Bialgebra.CotangentSpace R H)) x).baseChange A z =
        ⁅(1 : A) ⊗ₜ[R] x, z⁆ :=
    (LinearMap.congr_fun (LieModule.toEnd_baseChange R A _ _ x) z).symm
  refine LinearMap.ext fun z ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, had, had, endOfPoint_adjointComodule_bracket,
    hg]

/-- Every algebra-valued point acts on the scalar-extended tangent space by a Lie algebra
automorphism. -/
noncomputable def adjointLieEquiv
    (A : CommAlgCat.{max u v} R) (g : HopfAlgebra.points (H := H) A) :
    LieEquiv A (A ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H))
      (A ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H)) :=
  let e := (adjointAction A g).toLinearEquiv
  { e with
    map_lie' := fun {x y} => adjointAction_bracket A g x y }

/-- The adjoint Lie automorphism acts by the existing adjoint point representation. -/
@[simp]
theorem adjointLieEquiv_apply
    (A : CommAlgCat.{max u v} R) (g : HopfAlgebra.points (H := H) A)
    (x : A ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H)) :
    adjointLieEquiv (R := R) (H := H) A g x = (adjointAction A g).val x := by
  -- The wrapper has no generated equation lemma, so isolate its definitional reduction here.
  change (adjointAction A g).val x = _
  rfl

/-- The identity point acts as the identity Lie automorphism. -/
@[simp]
theorem adjointLieEquiv_one
    (A : CommAlgCat.{max u v} R) :
    adjointLieEquiv (R := R) (H := H) A 1 = 1 := by
  ext x
  rw [adjointLieEquiv_apply, one_apply_eq_self]
  exact congrArg
    (fun e : LinearMap.GeneralLinearGroup A
        (A ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H)) => e.val x)
    (map_one (adjointAction A).hom)

/-- The adjoint Lie automorphism of a product is the composite of the two adjoint Lie
automorphisms. -/
@[simp]
theorem adjointLieEquiv_mul
    (A : CommAlgCat.{max u v} R) (g h : HopfAlgebra.points (H := H) A) :
    adjointLieEquiv (R := R) (H := H) A (g * h) =
      (adjointLieEquiv (R := R) (H := H) A h).trans
        (adjointLieEquiv (R := R) (H := H) A g) := by
  ext x
  simp only [adjointLieEquiv_apply, LieEquiv.trans_apply]
  rw [map_mul (adjointAction A).hom, Units.val_mul, mul_apply_eq_comp]

/-- The inverse adjoint Lie automorphism is the automorphism of the inverse point. -/
@[simp]
theorem adjointLieEquiv_symm
    (A : CommAlgCat.{max u v} R) (g : HopfAlgebra.points (H := H) A) :
    (adjointLieEquiv (R := R) (H := H) A g).symm =
      adjointLieEquiv (R := R) (H := H) A g⁻¹ := by
  ext x
  apply (adjointLieEquiv (R := R) (H := H) A g).symm_apply_eq.mpr
  have h := congrArg
    (fun e : LieEquiv A (A ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H))
        (A ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H)) => e x)
    (adjointLieEquiv_mul (R := R) (H := H) A g g⁻¹)
  simpa only [mul_inv_cancel, adjointLieEquiv_one, one_apply_eq_self,
    LieEquiv.trans_apply] using h

end Derivation
