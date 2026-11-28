/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Equivalences of full subcategories

This file supplements Mathlib's `Mathlib.CategoryTheory.ObjectProperty.Equivalence` with API for
`CategoryTheory.Equivalence.congrFullSubcategory`, the equivalence between full subcategories of
corresponding properties induced by an equivalence of ambient categories. The restricted functors
act on underlying objects and morphisms as the ambient ones, by Mathlib's `@[simps]` projections
`CategoryTheory.Equivalence.congrFullSubcategory_functor` and
`CategoryTheory.Equivalence.congrFullSubcategory_inverse` together with
`CategoryTheory.ObjectProperty.lift`.

## Main declarations

* `CategoryTheory.ObjectProperty.inverseImage_eq_of_iso`: an isomorphism-invariant property has
  the same inverse image along isomorphic functors.
* `CategoryTheory.ObjectProperty.inverseImage_functor_inverseImage_inverse`: pulling an
  isomorphism-invariant property backward along both functors of an equivalence recovers it, as
  `congrFullSubcategory` asks of the transported property `P.inverseImage e.inverse`.
* `CategoryTheory.ObjectProperty.antiEquivalence`: given contravariant functors `F : Cᵒᵖ ⥤ D` and
  `G : Dᵒᵖ ⥤ C` sending `P` and `Q` into each other, together with natural evaluation
  isomorphisms satisfying the triangle identity, constructs the anti-equivalence
  `P.FullSubcategoryᵒᵖ ≌ Q.FullSubcategory`, accompanied by projection lemmas
  `antiEquivalence_functor_*`, `antiEquivalence_inverse_*`, `antiEquivalence_unitIso_*`, and
  `antiEquivalence_counitIso_*`.
* `CategoryTheory.Equivalence.congrFullSubcategory_functor_additive` and
  `CategoryTheory.Equivalence.congrFullSubcategory_inverse_additive`: if the ambient functor,
  respectively the ambient inverse, of an equivalence is additive, then so is its restriction to
  corresponding full subcategories.
-/

public section

namespace CategoryTheory

open Opposite

namespace ObjectProperty

/-- An isomorphism-invariant property has the same inverse image along isomorphic functors. -/
theorem inverseImage_eq_of_iso {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms] {F G : C ⥤ D} (α : F ≅ G) :
    P.inverseImage F = P.inverseImage G := by
  ext X
  exact P.prop_iff_of_iso (α.app X)

/-- Pulling an isomorphism-invariant object property backward along both functors of an
equivalence recovers the original property. This is
`CategoryTheory.ObjectProperty.inverseImage_eq_of_iso` for the unit of the equivalence. -/
@[simp]
theorem inverseImage_functor_inverseImage_inverse {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] (e : C ≌ D) :
    (P.inverseImage e.inverse).inverseImage e.functor = P :=
  P.inverseImage_eq_of_iso e.unitIso.symm

/-- Given contravariant functors `F : Cᵒᵖ ⥤ D` and `G : Dᵒᵖ ⥤ C` sending full subcategories `P`
and `Q` into each other, together with natural evaluation isomorphisms
`X ≅ G.obj (op (F.obj (op X)))` on `P` and `Y ≅ F.obj (op (G.obj (op Y)))` on `Q` satisfying the
triangle identity, `F` and `G` restrict to an anti-equivalence
`P.FullSubcategoryᵒᵖ ≌ Q.FullSubcategory`. -/
-- Exposed so that `.functor.obj` and `.inverse.obj` reduce definitionally in downstream
-- dependent-type statements (such as `unitIso`/`counitIso` comparisons without `eqToHom` in
-- `ModuleCat.matlisDualityOn` and `IsInjectiveEnvelope.fgModuleCatMatlisDuality`).
@[expose]
def antiEquivalence {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (F : Cᵒᵖ ⥤ D) (G : Dᵒᵖ ⥤ C)
    (hPQ : ∀ X, P X → Q (F.obj (op X)))
    (hQP : ∀ Y, Q Y → P (G.obj (op Y)))
    (η : ∀ X, P X → (X ≅ G.obj (op (F.obj (op X)))))
    (hη : ∀ {X X' : C} (hX : P X) (hX' : P X') (f : X ⟶ X'),
      f ≫ (η X' hX').hom = (η X hX).hom ≫ G.map (F.map f.op).op)
    (ε : ∀ Y, Q Y → (Y ≅ F.obj (op (G.obj (op Y)))))
    (hε : ∀ {Y Y' : D} (hY : Q Y) (hY' : Q Y') (g : Y ⟶ Y'),
      g ≫ (ε Y' hY').hom = (ε Y hY).hom ≫ F.map (G.map g.op).op)
    (hTri : ∀ X (hX : P X),
      (ε (F.obj (op X)) (hPQ X hX)).hom = F.map (η X hX).inv.op) :
    P.FullSubcategoryᵒᵖ ≌ Q.FullSubcategory where
  functor := Q.lift (P.ι.op ⋙ F) fun M => hPQ _ M.unop.property
  inverse := (P.lift (Q.ι.op ⋙ G) fun N => hQP _ N.unop.property).rightOp
  unitIso := NatIso.ofComponents
    (fun M => (P.isoMk (η M.unop.obj M.unop.property)).symm.op)
    (fun {X Y} g => by
      refine Quiver.Hom.unop_inj ((Iso.inv_comp_eq _).mpr ?_)
      refine ((Iso.eq_comp_inv _).mpr (P.hom_ext ?_)).trans (Category.assoc _ _ _)
      exact hη Y.unop.property X.unop.property g.unop.hom)
  counitIso := NatIso.ofComponents
    (fun N => (Q.isoMk (ε N.obj N.property)).symm)
    (fun {X Y} g => by
      refine (Iso.comp_inv_eq _).mpr ?_
      refine ((Iso.eq_inv_comp _).mpr (Q.hom_ext ?_)).trans (Category.assoc _ _ _).symm
      exact (hε X.property Y.property g.hom).symm)
  functor_unitIso_comp M := by
    refine Q.hom_ext ?_
    exact (Iso.comp_inv_eq_id (ε (F.obj (op M.unop.obj)) (hPQ _ M.unop.property))).mpr
      (hTri M.unop.obj M.unop.property).symm

section AntiEquivalenceProjections

variable {C D : Type*} [Category* C] [Category* D]
  {P : ObjectProperty C} {Q : ObjectProperty D}
  {F : Cᵒᵖ ⥤ D} {G : Dᵒᵖ ⥤ C}
  {hPQ : ∀ X, P X → Q (F.obj (op X))}
  {hQP : ∀ Y, Q Y → P (G.obj (op Y))}
  {η : ∀ X, P X → (X ≅ G.obj (op (F.obj (op X))))}
  {hη : ∀ {X X' : C} (hX : P X) (hX' : P X') (f : X ⟶ X'),
    f ≫ (η X' hX').hom = (η X hX).hom ≫ G.map (F.map f.op).op}
  {ε : ∀ Y, Q Y → (Y ≅ F.obj (op (G.obj (op Y))))}
  {hε : ∀ {Y Y' : D} (hY : Q Y) (hY' : Q Y') (g : Y ⟶ Y'),
    g ≫ (ε Y' hY').hom = (ε Y hY).hom ≫ F.map (G.map g.op).op}
  {hTri : ∀ X (hX : P X),
    (ε (F.obj (op X)) (hPQ X hX)).hom = F.map (η X hX).inv.op}

/-- The underlying object of `(antiEquivalence ...).functor.obj M` is `F.obj (op M.unop.obj)`. -/
theorem antiEquivalence_functor_obj_obj (M : P.FullSubcategoryᵒᵖ) :
    ((antiEquivalence P Q F G hPQ hQP η hη ε hε hTri).functor.obj M).obj =
      F.obj (op M.unop.obj) :=
  rfl

/-- The underlying morphism of `(antiEquivalence ...).functor.map g` is `F.map g.unop.hom.op`. -/
theorem antiEquivalence_functor_map_hom {M M' : P.FullSubcategoryᵒᵖ} (g : M ⟶ M') :
    ((antiEquivalence P Q F G hPQ hQP η hη ε hε hTri).functor.map g).hom =
      F.map g.unop.hom.op :=
  rfl

/-- The underlying object of `(antiEquivalence ...).inverse.obj N` is `G.obj (op N.obj)`. -/
theorem antiEquivalence_inverse_obj_unop_obj (N : Q.FullSubcategory) :
    ((antiEquivalence P Q F G hPQ hQP η hη ε hε hTri).inverse.obj N).unop.obj =
      G.obj (op N.obj) :=
  rfl

/-- The underlying morphism of `(antiEquivalence ...).inverse.map g` is `G.map g.hom.op`. -/
theorem antiEquivalence_inverse_map_unop_hom {N N' : Q.FullSubcategory} (g : N ⟶ N') :
    ((antiEquivalence P Q F G hPQ hQP η hη ε hε hTri).inverse.map g).unop.hom =
      G.map g.hom.op :=
  rfl

/-- The inverse unit component of `antiEquivalence` has underlying morphism `(η _ _).hom`. -/
theorem antiEquivalence_unitIso_inv_app_unop_hom (M : P.FullSubcategoryᵒᵖ) :
    ((antiEquivalence P Q F G hPQ hQP η hη ε hε hTri).unitIso.inv.app M).unop.hom =
      (η M.unop.obj M.unop.property).hom :=
  rfl

/-- The forward unit component of `antiEquivalence` has underlying morphism `(η _ _).inv`. -/
theorem antiEquivalence_unitIso_hom_app_unop_hom (M : P.FullSubcategoryᵒᵖ) :
    ((antiEquivalence P Q F G hPQ hQP η hη ε hε hTri).unitIso.hom.app M).unop.hom =
      (η M.unop.obj M.unop.property).inv :=
  rfl

/-- The inverse counit component of `antiEquivalence` has underlying morphism `(ε _ _).hom`. -/
theorem antiEquivalence_counitIso_inv_app_hom (N : Q.FullSubcategory) :
    ((antiEquivalence P Q F G hPQ hQP η hη ε hε hTri).counitIso.inv.app N).hom =
      (ε N.obj N.property).hom :=
  rfl

/-- The forward counit component of `antiEquivalence` has underlying morphism `(ε _ _).inv`. -/
theorem antiEquivalence_counitIso_hom_app_hom (N : Q.FullSubcategory) :
    ((antiEquivalence P Q F G hPQ hQP η hη ε hε hTri).counitIso.hom.app N).hom =
      (ε N.obj N.property).inv :=
  rfl

end AntiEquivalenceProjections

end ObjectProperty

namespace Equivalence

/-- If the functor of an equivalence is additive, then so is its restriction to corresponding full
subcategories. -/
instance congrFullSubcategory_functor_additive {C D : Type*} [Category* C] [Preadditive C]
    [Category* D] [Preadditive D] {P : ObjectProperty C} {Q : ObjectProperty D}
    [Q.IsClosedUnderIsomorphisms] (e : C ≌ D) [e.functor.Additive]
    (h : Q.inverseImage e.functor = P) : (e.congrFullSubcategory h).functor.Additive := by
  rw [congrFullSubcategory_functor]
  infer_instance

/-- If the inverse of an equivalence is additive, then so is its restriction to corresponding full
subcategories. Mathlib's `CategoryTheory.Equivalence.inverse_additive` derives this only from
additivity of the forward functor, so it does not apply under the hypothesis
`[e.inverse.Additive]` alone. -/
instance congrFullSubcategory_inverse_additive {C D : Type*} [Category* C] [Preadditive C]
    [Category* D] [Preadditive D] {P : ObjectProperty C} {Q : ObjectProperty D}
    [Q.IsClosedUnderIsomorphisms] (e : C ≌ D) [e.inverse.Additive]
    (h : Q.inverseImage e.functor = P) : (e.congrFullSubcategory h).inverse.Additive := by
  rw [congrFullSubcategory_inverse]
  infer_instance

end Equivalence

end CategoryTheory
