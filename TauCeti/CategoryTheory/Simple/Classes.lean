/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Skeletal

/-!
# Isomorphism classes of simple objects

For a category with zero morphisms, `TauCeti.SimpleClasses C` is the subtype of the skeleton of
`C` consisting of the classes represented by simple objects.  Using the skeleton makes equality
in this type exactly isomorphism of representatives, while retaining a chosen representative in
`C` for constructions indexed by simple classes.

The type is invariant under equivalence of categories.  This lets finiteness assumptions and sums
over simple classes be transported without choosing a separate indexing family of objects.

## Main declarations

* `TauCeti.SimpleClasses`: the type of isomorphism classes of simple objects;
* `TauCeti.SimpleClasses.classOf`: the class of a simple object;
* `TauCeti.SimpleClasses.eq_iff_nonempty_iso`: two classes are equal exactly when their
  representatives are isomorphic;
* `TauCeti.SimpleClasses.equiv`: an equivalence of categories induces an equivalence between their
  types of simple classes.
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
noncomputable abbrev rep (S : SimpleClasses C) : C := S.1.out

/-- The chosen representative of a simple class is simple. -/
instance (S : SimpleClasses C) : Simple S.rep := S.2

/-- The isomorphism class of a simple object. -/
noncomputable def classOf (X : C) [Simple X] : SimpleClasses C :=
  ⟨toSkeleton X, Simple.of_iso (fromSkeletonToSkeletonIso X)⟩

/-- The chosen representative of the class of a simple object is isomorphic to that object. -/
noncomputable def classOfRepIso (X : C) [Simple X] : (classOf X).rep ≅ X :=
  fromSkeletonToSkeletonIso X

/-- Taking the class of a chosen representative recovers the original simple class. -/
@[simp]
theorem classOf_rep (S : SimpleClasses C) : classOf S.rep = S := by
  apply Subtype.ext
  exact toSkeleton_fromSkeleton_obj S.1

/-- Two simple classes are equal exactly when their chosen representatives are isomorphic. -/
@[simp]
theorem eq_iff_nonempty_iso (S T : SimpleClasses C) :
    S = T ↔ Nonempty (S.rep ≅ T.rep) := by
  rw [Subtype.ext_iff, ← toSkeleton_fromSkeleton_obj S.1,
    ← toSkeleton_fromSkeleton_obj T.1, toSkeleton_eq_toSkeleton_iff]
  rfl

/-- Two simple objects determine the same simple class exactly when they are isomorphic. -/
theorem classOf_eq_iff_nonempty_iso (X Y : C) [Simple X] [Simple Y] :
    classOf X = classOf Y ↔ Nonempty (X ≅ Y) := by
  rw [Subtype.ext_iff]
  exact toSkeleton_eq_toSkeleton_iff

/-- Every simple object is isomorphic to the representative of a unique simple class. -/
theorem existsUnique_nonempty_iso_rep (X : C) [Simple X] :
    ∃! S : SimpleClasses C, Nonempty (X ≅ S.rep) := by
  refine ⟨classOf X, ⟨(classOfRepIso X).symm⟩, ?_⟩
  rintro T ⟨i⟩
  apply (eq_iff_nonempty_iso T (classOf X)).2
  exact ⟨i.symm.trans (classOfRepIso X).symm⟩

section Equivalence

variable {D : Type u₂} [_root_.CategoryTheory.Category.{v₂} D]
  [_root_.CategoryTheory.Limits.HasZeroMorphisms D]

/-- An equivalence of categories induces an equivalence between their simple isomorphism classes. -/
noncomputable def equiv (e : C ≌ D) : SimpleClasses C ≃ SimpleClasses D where
  toFun S := by
    let _ := _root_.CategoryTheory.simple_obj e.functor S.rep
    exact classOf (e.functor.obj S.rep)
  invFun T := by
    let _ := _root_.CategoryTheory.simple_obj e.inverse T.rep
    exact classOf (e.inverse.obj T.rep)
  left_inv S := by
    let _ : Simple (e.functor.obj S.rep) :=
      _root_.CategoryTheory.simple_obj e.functor S.rep
    let _ : Simple (e.inverse.obj (classOf (e.functor.obj S.rep)).rep) :=
      _root_.CategoryTheory.simple_obj e.inverse _
    apply (eq_iff_nonempty_iso _ _).2
    exact ⟨classOfRepIso _ ≪≫ e.inverse.mapIso (classOfRepIso _) ≪≫
      (e.unitIso.app S.rep).symm⟩
  right_inv T := by
    let _ : Simple (e.inverse.obj T.rep) :=
      _root_.CategoryTheory.simple_obj e.inverse T.rep
    let _ : Simple (e.functor.obj (classOf (e.inverse.obj T.rep)).rep) :=
      _root_.CategoryTheory.simple_obj e.functor _
    apply (eq_iff_nonempty_iso _ _).2
    exact ⟨classOfRepIso _ ≪≫ e.functor.mapIso (classOfRepIso _) ≪≫
      e.counitIso.app T.rep⟩

/-- The representative of the image of a simple class under an equivalence is isomorphic to the
image of its representative. -/
noncomputable def equivApplyRepIso (e : C ≌ D) (S : SimpleClasses C) :
    (equiv e S).rep ≅ e.functor.obj S.rep :=
  by
    let _ := _root_.CategoryTheory.simple_obj e.functor S.rep
    exact classOfRepIso _

/-- The equivalence on simple classes maps the class of an object to the class of its image. -/
@[simp]
theorem equiv_apply_classOf (e : C ≌ D) (X : C) [Simple X] :
    equiv e (classOf X) =
      @classOf D _ _ (e.functor.obj X) (_root_.CategoryTheory.simple_obj e.functor X) := by
  let _ : Simple (e.functor.obj X) := _root_.CategoryTheory.simple_obj e.functor X
  apply (eq_iff_nonempty_iso _ _).2
  exact ⟨equivApplyRepIso e (classOf X) ≪≫ e.functor.mapIso (classOfRepIso X) ≪≫
    (classOfRepIso _).symm⟩

end Equivalence

end SimpleClasses

end TauCeti
