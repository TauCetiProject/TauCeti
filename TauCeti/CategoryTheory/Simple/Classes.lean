/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.HomOrthogonal
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.CategoryTheory.Skeletal

/-!
# Isomorphism classes of simple objects

For a category with zero morphisms, `TauCeti.SimpleClasses C` is the subtype of the skeleton of
`C` consisting of the classes represented by simple objects.  Using the skeleton makes equality
in this type exactly isomorphism of representatives, while retaining a chosen representative in
`C` for constructions indexed by simple classes.

The type is invariant under equivalence of categories.  This lets finiteness assumptions and sums
over simple classes be transported without choosing a separate indexing family of objects.
In a preadditive category with kernels, Schur's lemma makes the chosen representatives of
distinct simple classes hom orthogonal.

## Main declarations

* `TauCeti.SimpleClasses`: the type of isomorphism classes of simple objects;
* `TauCeti.SimpleClasses.classOf`: the class of a simple object;
* `TauCeti.SimpleClasses.eq_iff_nonempty_iso`: two classes are equal exactly when their
  representatives are isomorphic;
* `TauCeti.SimpleClasses.equiv`: an equivalence of categories induces an equivalence between their
  types of simple classes;
* `TauCeti.SimpleClasses.homOrthogonal_repr`: in a preadditive category with kernels, the chosen
  representatives of distinct simple classes are hom orthogonal (Schur's lemma);
* `TauCeti.SimpleClasses.classOf_eq_iff_exists_ne_zero`: two simple objects have the same class
  exactly when there is a nonzero morphism between them (Schur's lemma);
* `TauCeti.SimpleClasses.sum_comp_classOfReprIso_eq_id`: a biproduct decomposition into simple
  objects resolves the identity through the chosen representatives of their classes.
-/

public section

namespace TauCeti

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

variable (C : Type u₁) [_root_.CategoryTheory.Category.{v₁} C]
  [_root_.CategoryTheory.Limits.HasZeroMorphisms C]

/-- The isomorphism classes of simple objects of `C`, realized as the simple part of its
skeleton. -/
abbrev SimpleClasses := {X : Skeleton C // Simple X.out}

namespace SimpleClasses

variable {C}

/-- The chosen representative in `C` of a simple isomorphism class. -/
noncomputable abbrev repr (S : SimpleClasses C) : C := S.1.out

/-- The chosen representative of a simple class is simple. -/
instance (S : SimpleClasses C) : Simple S.repr := S.2

/-- The isomorphism class of a simple object. -/
noncomputable def classOf (X : C) [Simple X] : SimpleClasses C :=
  ⟨toSkeleton X, Simple.of_iso (fromSkeletonToSkeletonIso X)⟩

/-- The chosen representative of the class of a simple object is isomorphic to that object. -/
noncomputable def classOfReprIso (X : C) [Simple X] : (classOf X).repr ≅ X :=
  fromSkeletonToSkeletonIso X

/-- Taking the class of a chosen representative recovers the original simple class. -/
@[simp]
theorem classOf_repr (S : SimpleClasses C) : classOf S.repr = S := by
  apply Subtype.ext
  exact toSkeleton_fromSkeleton_obj S.1

/-- Two simple classes are equal exactly when their chosen representatives are isomorphic. -/
@[simp]
theorem eq_iff_nonempty_iso (S T : SimpleClasses C) :
    S = T ↔ Nonempty (S.repr ≅ T.repr) := by
  rw [Subtype.ext_iff, ← toSkeleton_fromSkeleton_obj S.1,
    ← toSkeleton_fromSkeleton_obj T.1, toSkeleton_eq_toSkeleton_iff]
  rfl

/-- Two simple objects determine the same simple class exactly when they are isomorphic. -/
theorem classOf_eq_iff_nonempty_iso (X Y : C) [Simple X] [Simple Y] :
    classOf X = classOf Y ↔ Nonempty (X ≅ Y) := by
  rw [Subtype.ext_iff]
  exact toSkeleton_eq_toSkeleton_iff

/-- Every simple object is isomorphic to the representative of a unique simple class. -/
theorem existsUnique_nonempty_iso_repr (X : C) [Simple X] :
    ∃! S : SimpleClasses C, Nonempty (X ≅ S.repr) := by
  refine ⟨classOf X, ⟨(classOfReprIso X).symm⟩, ?_⟩
  rintro T ⟨i⟩
  apply (eq_iff_nonempty_iso T (classOf X)).2
  exact ⟨i.symm.trans (classOfReprIso X).symm⟩

section Equivalence

variable {D : Type u₂} [_root_.CategoryTheory.Category.{v₂} D]
  [_root_.CategoryTheory.Limits.HasZeroMorphisms D]

/-- An equivalence of categories induces an equivalence between their simple isomorphism classes. -/
noncomputable def equiv (e : C ≌ D) : SimpleClasses C ≃ SimpleClasses D where
  toFun S := by
    let _ := _root_.CategoryTheory.simple_obj e.functor S.repr
    exact classOf (e.functor.obj S.repr)
  invFun T := by
    let _ := _root_.CategoryTheory.simple_obj e.inverse T.repr
    exact classOf (e.inverse.obj T.repr)
  left_inv S := by
    let _ : Simple (e.functor.obj S.repr) :=
      _root_.CategoryTheory.simple_obj e.functor S.repr
    let _ : Simple (e.inverse.obj (classOf (e.functor.obj S.repr)).repr) :=
      _root_.CategoryTheory.simple_obj e.inverse _
    apply (eq_iff_nonempty_iso _ _).2
    exact ⟨classOfReprIso _ ≪≫ e.inverse.mapIso (classOfReprIso _) ≪≫
      (e.unitIso.app S.repr).symm⟩
  right_inv T := by
    let _ : Simple (e.inverse.obj T.repr) :=
      _root_.CategoryTheory.simple_obj e.inverse T.repr
    let _ : Simple (e.functor.obj (classOf (e.inverse.obj T.repr)).repr) :=
      _root_.CategoryTheory.simple_obj e.functor _
    apply (eq_iff_nonempty_iso _ _).2
    exact ⟨classOfReprIso _ ≪≫ e.functor.mapIso (classOfReprIso _) ≪≫
      e.counitIso.app T.repr⟩

/-- The representative of the image of a simple class under an equivalence is isomorphic to the
image of its representative. -/
noncomputable def equivApplyReprIso (e : C ≌ D) (S : SimpleClasses C) :
    (equiv e S).repr ≅ e.functor.obj S.repr :=
  by
    let _ := _root_.CategoryTheory.simple_obj e.functor S.repr
    exact classOfReprIso _

/-- The equivalence on simple classes maps the class of an object to the class of its image. -/
@[simp]
theorem equiv_apply_classOf (e : C ≌ D) (X : C) [Simple X] :
    equiv e (classOf X) =
      @classOf D _ _ (e.functor.obj X) (_root_.CategoryTheory.simple_obj e.functor X) := by
  let _ : Simple (e.functor.obj X) := _root_.CategoryTheory.simple_obj e.functor X
  apply (eq_iff_nonempty_iso _ _).2
  exact ⟨equivApplyReprIso e (classOf X) ≪≫ e.functor.mapIso (classOfReprIso X) ≪≫
    (classOfReprIso _).symm⟩

end Equivalence

/-- Distinct isomorphism classes of simple objects have no nonzero morphisms between their
representatives. -/
theorem homOrthogonal_repr {D : Type u₁} [Category.{v₁} D] [Preadditive D] [HasKernels D] :
    HomOrthogonal (repr (C := D)) := by
  intro S T h
  apply subsingleton_of_forall_eq (0 : S.repr ⟶ T.repr)
  intro f
  by_contra hf
  have := isIso_of_hom_simple hf
  exact h ((eq_iff_nonempty_iso S T).2 ⟨asIso f⟩)

/-- Two simple objects have the same class exactly when there is a nonzero morphism between them
(Schur's lemma). -/
theorem classOf_eq_iff_exists_ne_zero {D : Type u₁} [Category.{v₁} D] [Preadditive D]
    [HasKernels D] {X Y : D} [Simple X] [Simple Y] :
    classOf X = classOf Y ↔ ∃ f : X ⟶ Y, f ≠ 0 := by
  rw [classOf_eq_iff_nonempty_iso]
  constructor
  · rintro ⟨e⟩
    exact ⟨e.hom, (isIso_iff_ne_zero e.hom).1 inferInstance⟩
  · rintro ⟨f, hf⟩
    have := isIso_of_hom_simple hf
    exact ⟨asIso f⟩

/-- A biproduct decomposition `e : Y ≅ ⨁ a` into simple objects resolves `𝟙 Y` through the chosen
representatives `(classOf (a i)).repr` of their isomorphism classes. -/
theorem sum_comp_classOfReprIso_eq_id {D : Type u₁} [Category.{v₁} D] [Preadditive D]
    {Y : D} {ι : Type*} [Fintype ι] (a : ι → D) [∀ i, Simple (a i)] [HasBiproduct a]
    (e : Y ≅ ⨁ a) :
    ∑ i : ι, (e.hom ≫ biproduct.π a i ≫ (classOfReprIso (a i)).inv) ≫
      ((classOfReprIso (a i)).hom ≫ biproduct.ι a i ≫ e.inv) = 𝟙 Y := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  calc ∑ i, e.hom ≫ biproduct.π a i ≫ biproduct.ι a i ≫ e.inv
      = e.hom ≫ (∑ i, biproduct.π a i ≫ biproduct.ι a i) ≫ e.inv := by
          simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
    _ = 𝟙 Y := by rw [biproduct.total, Category.id_comp, e.hom_inv_id]

end SimpleClasses

end TauCeti
