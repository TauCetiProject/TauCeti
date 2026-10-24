/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ScalarExtension
public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.GroupFunctor

/-!
# Tannakian reconstruction using natural point representations

Finite natural point representations and finite comodules have equivalent symmetric monoidal
categories. Precomposing scalar extension with this equivalence identifies their tensor
automorphisms. Thus Tannakian reconstruction may be used with natural actions on every
algebra-valued point group, rather than with a chosen coordinate coaction.

The comparison uses `TauCeti.fgPointRepresentationCategoryEquivalence` and the existing
`TauCeti.Tannaka.fgPointTensorIsoEquiv`. No finite-type, smoothness or reducedness hypothesis
on the affine group is needed.

## References

* J. S. Milne, *Algebraic Groups* (2017), §9.4.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v

namespace Tannaka

section Comparison

variable (R : Type u) [CommRing R] (H : Type v) [CommRing H] [HopfAlgebra R H]
variable (A : Type u) [CommRing A] [Algebra R A]

/-- Tensor automorphisms on finite comodules are exactly tensor automorphisms on finite
natural point representations, by precomposition with their monoidal equivalence. -/
noncomputable def tensorAutEquivPointRepresentation :
    Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A) ≃*
      Aut (FGPointRepresentationCat.scalarExtensionMonoidalFunctor R H A) :=
  MulEquiv.ofBijective
    ((fgPointRepresentationCategoryEquivalence R H).functor.precomposeLaxMonoidal.mapAut
      (FGComoduleCat.scalarExtensionMonoidalFunctor R H A)) (by
    have h := ((fgPointRepresentationCategoryEquivalence R H).precomposeLaxMonoidalEquivalence
      (E := SemimoduleCat.{u} A)).fullyFaithfulFunctor.autMulEquivOfFullyFaithful
        (FGComoduleCat.scalarExtensionMonoidalFunctor R H A) |>.bijective
    -- The fully faithful automorphism equivalence has `mapAut` as its forward function.
    change Function.Bijective
      (((fgPointRepresentationCategoryEquivalence R H).precomposeLaxMonoidalEquivalence
        (E := SemimoduleCat.{u} A)).functor.mapAut
          (FGComoduleCat.scalarExtensionMonoidalFunctor R H A)) at h
    rw [Equivalence.precomposeLaxMonoidalEquivalence_functor] at h
    exact h)

/-- On a representation the comparison evaluates the original automorphism on its recovered
comodule. The components have propositionally identified scalar-extension objects. -/
theorem tensorAutEquivPointRepresentation_hom_app
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A))
    (V : FGPointRepresentationCat.{u, v, u} R H) :
    HEq ((tensorAutEquivPointRepresentation R H A η).asIso.hom.hom.app V)
      (η.asIso.hom.hom.app
        ((fgPointRepresentationCategoryEquivalence R H).functor.obj V)) := by
  simp only [tensorAutEquivPointRepresentation, MulEquiv.ofBijective_apply,
    Functor.mapAut_apply_asIso, Functor.mapIso_hom]
  exact Functor.precomposeLaxMonoidal_map_hom_app
    (fgPointRepresentationCategoryEquivalence R H).functor η.asIso.hom V

/-- Base change of tensor automorphisms of finite point-representation scalar extension.
It is the base change of comodule components, transported through the monoidal dictionary. -/
noncomputable def pointRepresentationTensorAutMapValueHom (B : Type u)
    [CommRing B] [Algebra R B] (f : A →ₐ[R] B) :
    Aut (FGPointRepresentationCat.scalarExtensionMonoidalFunctor R H A) →*
      Aut (FGPointRepresentationCat.scalarExtensionMonoidalFunctor R H B) :=
  (tensorAutEquivPointRepresentation R H B).toMonoidHom.comp
    ((tensorAutMapValueHom R H A B f).comp
      (tensorAutEquivPointRepresentation R H A).symm.toMonoidHom)

/-- Base change evaluates by transporting to comodules, changing scalars, and transporting
back to point representations. -/
@[simp]
theorem pointRepresentationTensorAutMapValueHom_apply (B : Type u)
    [CommRing B] [Algebra R B] (f : A →ₐ[R] B)
    (η : Aut (FGPointRepresentationCat.scalarExtensionMonoidalFunctor R H A)) :
    pointRepresentationTensorAutMapValueHom R H A B f η =
      tensorAutEquivPointRepresentation R H B
        (tensorAutMapValue R H A B f ((tensorAutEquivPointRepresentation R H A).symm η)) :=
  by simp [pointRepresentationTensorAutMapValueHom, tensorAutMapValueHom_apply]

end Comparison

section Functor

variable (R : Type u) [CommRing R] (H : Type v) [CommRing H] [HopfAlgebra R H]

/-- The group-valued tensor-automorphism functor on finite natural point representations,
with value-algebra maps induced by base change of components. -/
noncomputable def pointRepresentationTensorAutFunctor :
    CommAlgCat.{u} R ⥤ GrpCat.{max (u + 1) (v + 1)} where
  obj A := GrpCat.of (Aut (FGPointRepresentationCat.scalarExtensionMonoidalFunctor R H A))
  map {A B} f := GrpCat.ofHom (pointRepresentationTensorAutMapValueHom R H A B f.hom)
  map_id A := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro η
    simp [pointRepresentationTensorAutMapValueHom_apply, tensorAutMapValue_id]
  map_comp {A B C} f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro η
    simp [pointRepresentationTensorAutMapValueHom_apply, tensorAutMapValue_comp]

/-- The object of the point-representation tensor-automorphism functor is the actual
monoidal automorphism group. -/
@[simp]
theorem pointRepresentationTensorAutFunctor_obj (B : CommAlgCat.{u} R) :
    (pointRepresentationTensorAutFunctor R H).obj B =
      GrpCat.of (Aut (FGPointRepresentationCat.scalarExtensionMonoidalFunctor R H B)) :=
  (rfl)

/-- The tensor-automorphism functor acts on a value-algebra map by base change of components. -/
@[simp]
theorem pointRepresentationTensorAutFunctor_map {B C : CommAlgCat.{u} R} (f : B ⟶ C) :
    (pointRepresentationTensorAutFunctor R H).map f =
      eqToHom (pointRepresentationTensorAutFunctor_obj R H B) ≫
        GrpCat.ofHom (pointRepresentationTensorAutMapValueHom R H B C f.hom) ≫
          eqToHom (pointRepresentationTensorAutFunctor_obj R H C).symm := by
  apply (conj_eqToHom_iff_heq _ _ (pointRepresentationTensorAutFunctor_obj R H B)
    (pointRepresentationTensorAutFunctor_obj R H C)).2
  rw [pointRepresentationTensorAutFunctor]

/-- Applying the point-representation tensor-automorphism functor map to a transported
automorphism changes its value algebra through the representation--comodule dictionary. -/
theorem pointRepresentationTensorAutFunctor_map_transport_apply
    {B C : CommAlgCat.{u} R} (f : B ⟶ C)
    (η : Aut (FGPointRepresentationCat.scalarExtensionMonoidalFunctor R H B)) :
    eqToHom (pointRepresentationTensorAutFunctor_obj R H C)
        ((pointRepresentationTensorAutFunctor R H).map f
          (eqToHom (pointRepresentationTensorAutFunctor_obj R H B).symm η)) =
      tensorAutEquivPointRepresentation R H C
        (tensorAutMapValue R H B C f.hom ((tensorAutEquivPointRepresentation R H B).symm η)) := by
  exact pointRepresentationTensorAutMapValueHom_apply R H B C f.hom η

end Functor

section FunctorComparison

-- A common universe identifies the comodule and point-representation functor targets.
variable (R H : Type u) [CommRing R] [CommRing H] [HopfAlgebra R H]

/-- The representation--comodule dictionary identifies tensor-automorphism functors,
naturally in every commutative value algebra. -/
noncomputable def tensorAutFunctorIsoPointRepresentationTensorAutFunctor :
    tensorAutFunctor R H ≅ pointRepresentationTensorAutFunctor R H :=
  NatIso.ofComponents (fun A ↦
    eqToIso (tensorAutFunctor_obj R H A) ≪≫
      (tensorAutEquivPointRepresentation R H A).toGrpIso ≪≫
        eqToIso (pointRepresentationTensorAutFunctor_obj R H A).symm)
    (fun {A B} f ↦ by
      apply (cancel_mono (eqToHom (pointRepresentationTensorAutFunctor_obj R H B))).mp
      apply (cancel_epi (eqToHom (tensorAutFunctor_obj R H A).symm)).mp
      rw [tensorAutFunctor_map, pointRepresentationTensorAutFunctor_map]
      dsimp only [Iso.trans_hom, eqToIso.hom]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
        Category.comp_id, Category.id_comp]
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro η
      simp only [GrpCat.hom_comp, GrpCat.hom_ofHom, MonoidHom.comp_apply,
        MulEquiv.toGrpIso, tensorAutMapValueHom_apply]
      simp)

/-- The tensor-automorphism dictionary acts by precomposition at each value algebra. -/
theorem tensorAutFunctorIsoPointRepresentationTensorAutFunctor_hom_app
    (B : CommAlgCat.{u} R) :
    (tensorAutFunctorIsoPointRepresentationTensorAutFunctor R H).hom.app B =
      eqToHom (tensorAutFunctor_obj R H B) ≫
        (tensorAutEquivPointRepresentation R H B).toGrpIso.hom ≫
          eqToHom (pointRepresentationTensorAutFunctor_obj R H B).symm :=
  (rfl)

/-- Evaluation of the tensor-automorphism dictionary after identifying its functor objects. -/
theorem tensorAutFunctorIsoPointRepresentationTensorAutFunctor_hom_app_apply
    (B : CommAlgCat.{u} R) (η : (tensorAutFunctor R H).obj B) :
    eqToHom (pointRepresentationTensorAutFunctor_obj R H B)
        ((tensorAutFunctorIsoPointRepresentationTensorAutFunctor R H).hom.app B η) =
      tensorAutEquivPointRepresentation R H B (eqToHom (tensorAutFunctor_obj R H B) η) := by
  rw [tensorAutFunctorIsoPointRepresentationTensorAutFunctor_hom_app]
  -- The new functor-object transport is reflexive by construction; the remaining
  -- composition is exactly the underlying group equivalence.
  rfl

end FunctorComparison

section Reconstruction

variable (k H A : Type u) [Field k] [CommRing H] [HopfAlgebra k H]
  [CommRing A] [Algebra k A]

/-- Tannakian reconstruction on the category of finite natural point representations. -/
noncomputable def pointRepresentationTensorIsoEquiv :
    WithConv (H →ₐ[k] A) ≃*
      Aut (FGPointRepresentationCat.scalarExtensionMonoidalFunctor k H A) :=
  (fgPointTensorIsoEquiv k H A).trans (tensorAutEquivPointRepresentation k H A)

/-- A point acts on a representation through the tensor automorphism of its recovered
comodule. -/
@[simp]
theorem pointRepresentationTensorIsoEquiv_apply (g : WithConv (H →ₐ[k] A)) :
    pointRepresentationTensorIsoEquiv k H A g =
      tensorAutEquivPointRepresentation k H A (fgPointTensorIso k H A g) := by
  rw [pointRepresentationTensorIsoEquiv, MulEquiv.trans_apply, fgPointTensorIsoEquiv_apply]

/-- Recover the point from a tensor automorphism of point-representation scalar extension by
transporting it back to finite comodules. -/
@[simp]
theorem pointRepresentationTensorIsoEquiv_symm_apply
    (η : Aut (FGPointRepresentationCat.scalarExtensionMonoidalFunctor k H A)) :
    (pointRepresentationTensorIsoEquiv k H A).symm η =
      reconstructedPoint k H A ((tensorAutEquivPointRepresentation k H A).symm η) := by
  rw [pointRepresentationTensorIsoEquiv, MulEquiv.symm_trans_apply,
    fgPointTensorIsoEquiv_symm_apply]

/-- Tannakian reconstruction as a natural isomorphism using finite natural point
representations. The universe lift is the same as in the comodule reconstruction. -/
noncomputable def pointsFunctorIsoPointRepresentationTensorAutFunctor :
    HopfAlgebra.pointsFunctor (R := k) (H := H) ⋙ GrpCat.uliftFunctor.{u + 1, u} ≅
      pointRepresentationTensorAutFunctor k H :=
  pointsFunctorIsoTensorAutFunctor k H ≪≫
    tensorAutFunctorIsoPointRepresentationTensorAutFunctor k H

/-- The natural reconstruction comparison sends a point to its tensor action on finite
point representations. -/
theorem pointsFunctorIsoPointRepresentationTensorAutFunctor_hom_app_apply
    (B : CommAlgCat.{u} k) (x : ULift.{u + 1} (WithConv (H →ₐ[k] B))) :
    eqToHom (pointRepresentationTensorAutFunctor_obj k H B)
        ((pointsFunctorIsoPointRepresentationTensorAutFunctor k H).hom.app B x) =
      pointRepresentationTensorIsoEquiv k H B x.down := by
  -- Evaluate the composite isomorphism directly: its source functor is definitionally
  -- the universe-lifted point type, so rewriting inside its application loses that typing.
  change eqToHom (pointRepresentationTensorAutFunctor_obj k H B)
    ((tensorAutFunctorIsoPointRepresentationTensorAutFunctor k H).hom.app B
      ((pointsFunctorIsoTensorAutFunctor k H).hom.app B x)) = _
  rw [tensorAutFunctorIsoPointRepresentationTensorAutFunctor_hom_app_apply,
    pointsFunctorIsoTensorAutFunctor_hom_app_apply, pointRepresentationTensorIsoEquiv_apply]

/-- The inverse natural comparison reconstructs the point of a tensor automorphism. -/
theorem pointsFunctorIsoPointRepresentationTensorAutFunctor_inv_app_apply
    (B : CommAlgCat.{u} k)
    (η : Aut (FGPointRepresentationCat.scalarExtensionMonoidalFunctor k H B)) :
    ((pointsFunctorIsoPointRepresentationTensorAutFunctor k H).inv.app B
        (eqToHom (pointRepresentationTensorAutFunctor_obj k H B).symm η)).down =
      (pointRepresentationTensorIsoEquiv k H B).symm η := by
  apply (pointRepresentationTensorIsoEquiv k H B).injective
  have h := pointsFunctorIsoPointRepresentationTensorAutFunctor_hom_app_apply k H B
    ((pointsFunctorIsoPointRepresentationTensorAutFunctor k H).inv.app B
      (eqToHom (pointRepresentationTensorAutFunctor_obj k H B).symm η))
  have hi := Iso.inv_hom_id_apply
    ((pointsFunctorIsoPointRepresentationTensorAutFunctor k H).app B)
    (eqToHom (pointRepresentationTensorAutFunctor_obj k H B).symm η)
  simp only [Iso.app_hom, Iso.app_inv] at hi
  rw [hi] at h
  have hc : eqToHom (pointRepresentationTensorAutFunctor_obj k H B)
      (eqToHom (pointRepresentationTensorAutFunctor_obj k H B).symm η) = η := by
    exact Iso.inv_hom_id_apply (eqToIso (pointRepresentationTensorAutFunctor_obj k H B)) η
  rw [hc] at h
  simpa only [MulEquiv.apply_symm_apply] using h.symm

end Reconstruction

end Tannaka

end TauCeti
