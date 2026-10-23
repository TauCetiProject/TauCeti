/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.Basic
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Opposite

/-!
# Opposite stable categories

When relative projectives and injectives coincide, the projective stable category of the
opposite exact category is additively equivalent to the opposite projective stable category.
In particular this applies to every Frobenius exact category. The comparison sends an opposite
object to the opposite of its stable class, and does the same on morphisms.

Projectives in the opposite are injectives in the original category. Equality of projectives
and injectives identifies the two ideals that must be killed. The quotient comparison then
comes from `MorphismIdeal.opQuotientFunctor`, rather than a second construction of
opposite ideal quotients. Enough projectives or injectives are not needed for this additive
comparison.

This file constructs the equivalence and its compatibility with the quotient functors.
It does not assert compatibility with the shifts or distinguished triangles.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] (E : ExactStructure C)
  (hPI : ∀ X, E.isProjective X ↔ E.isInjective X)
include hPI

/-- If relative projectives and injectives coincide, the projective stable ideal of the
opposite exact structure is the opposite projective stable ideal. -/
@[simp]
theorem projectiveStableIdeal_op :
    E.op.projectiveStableIdeal = E.projectiveStableIdeal.op := by
  ext X Y f
  simp only [MorphismIdeal.mem_op_hom, mem_projectiveStableIdeal_iff,
    ObjectProperty.factorsThrough_iff]
  constructor
  · rintro ⟨Q, hQ, i, p, hp⟩
    refine ⟨Q.unop, (hPI Q.unop).mpr
      ((E.isInjective_iff_isProjective_op Q.unop).mpr hQ), p.unop, i.unop, ?_⟩
    exact congrArg Quiver.Hom.unop hp
  · rintro ⟨Q, hQ, i, p, hp⟩
    refine ⟨Opposite.op Q, (E.isInjective_iff_isProjective_op Q).mp
      ((hPI Q).mp hQ), p.op, i.op, ?_⟩
    exact congrArg Quiver.Hom.op hp

/-- The comparison from the stable category of the opposite to the opposite stable category.
It is the lift of the opposite quotient functor. -/
noncomputable def projectiveStableOpFunctor :
    E.op.ProjectiveStableCategory ⥤ E.ProjectiveStableCategoryᵒᵖ :=
  E.op.projectiveStableIdeal.lift E.projectiveStableFunctor.op fun X Y f hf ↦ by
    rw [Functor.mem_kerIdeal_hom]
    apply Quiver.Hom.unop_inj
    rw [E.projectiveStableIdeal_op hPI, MorphismIdeal.mem_op_hom] at hf
    simpa using E.projectiveStableIdeal.quotientFunctor_map_eq_zero_iff.mpr hf

/-- The opposite stable comparison has the expected object formula. -/
@[simp]
theorem projectiveStableOpFunctor_obj (X : Cᵒᵖ) :
    (E.projectiveStableOpFunctor hPI).obj (E.op.projectiveStableFunctor.obj X) =
      Opposite.op (E.projectiveStableFunctor.obj X.unop) := by
  rw [projectiveStableOpFunctor, CategoryTheory.Quotient.lift_obj_functor_obj,
    Functor.op_obj]

/-- The opposite stable comparison sends the class of a map to the opposite class of its
unopposite. The transports identify the objects using the object formula. -/
@[simp]
theorem projectiveStableOpFunctor_map {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (E.projectiveStableOpFunctor hPI).map (E.op.projectiveStableFunctor.map f) =
      eqToHom (E.projectiveStableOpFunctor_obj hPI X) ≫
        (E.projectiveStableFunctor.map f.unop).op ≫
          eqToHom (E.projectiveStableOpFunctor_obj hPI Y).symm := by
  apply (conj_eqToHom_iff_heq _ _ (E.projectiveStableOpFunctor_obj hPI X)
    (E.projectiveStableOpFunctor_obj hPI Y)).mpr
  rw [projectiveStableOpFunctor, CategoryTheory.Quotient.lift_map_functor_map,
    Functor.op_map]

/-- The comparison commutes with taking stable classes and opposites. -/
@[simp]
theorem projectiveStableFunctor_op_comp_projectiveStableOpFunctor :
    E.op.projectiveStableFunctor ⋙ E.projectiveStableOpFunctor hPI =
      E.projectiveStableFunctor.op := by
  rw [projectiveStableOpFunctor]
  exact CategoryTheory.Quotient.lift_spec _ _ _

instance : (E.projectiveStableOpFunctor hPI).Additive := by
  rw [projectiveStableOpFunctor]
  infer_instance

noncomputable instance : (E.projectiveStableOpFunctor hPI).IsEquivalence := by
  rw [projectiveStableOpFunctor]
  exact MorphismIdeal.isEquivalence_op_lift _ _ (E.projectiveStableIdeal_op hPI) _

/-- When relative projectives and injectives coincide, the projective stable category of the
opposite is additively equivalent to the opposite projective stable category. No choice of
suspension presentations enters this comparison. For a Frobenius structure, take
`hPI := hE.projective_iff_injective`. -/
noncomputable def projectiveStableOpEquivalence :
    E.op.ProjectiveStableCategory ≌ E.ProjectiveStableCategoryᵒᵖ :=
  (E.projectiveStableOpFunctor hPI).asEquivalence

/-- The forward direction of the opposite stable equivalence is the comparison functor. -/
@[simp]
theorem projectiveStableOpEquivalence_functor :
    (E.projectiveStableOpEquivalence hPI).functor = E.projectiveStableOpFunctor hPI := by
  rw [projectiveStableOpEquivalence, Functor.asEquivalence_functor]

instance : (E.projectiveStableOpEquivalence hPI).functor.Additive := by
  rw [projectiveStableOpEquivalence_functor]
  infer_instance

/-- The inverse comparison carries the opposite stable class of an object back to the
stable class of its opposite, naturally in objects of the original opposite category. -/
noncomputable def projectiveStableFunctorOpCompInverseIso :
    E.projectiveStableFunctor.op ⋙ (E.projectiveStableOpEquivalence hPI).inverse ≅
      E.op.projectiveStableFunctor :=
  (eqToIso (by
    rw [projectiveStableOpEquivalence_functor,
      E.projectiveStableFunctor_op_comp_projectiveStableOpFunctor hPI])).compInverseIso

end TauCeti.ExactStructure
