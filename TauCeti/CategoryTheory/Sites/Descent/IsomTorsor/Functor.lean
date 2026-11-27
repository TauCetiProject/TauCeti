/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.IsomTorsor.Sheaf
public import TauCeti.CategoryTheory.Sites.Descent.IsGerbe

/-!
# Functoriality of Isom torsors in both endpoints

The Isom torsors of an abelian-banded gerbe form a functor, contravariant in the source and
covariant in the target. Precomposition and postcomposition commute with the band action, so
transport is equivariant. The underlying sheaf map sends `p` to `e|_T ≫ p ≫ f|_T`.
This allows constructions on torsors, such as extension of the structure group, to be applied
functorially to the local isomorphisms of a gerbe.

## References

* Martin Olsson, *Stacks* (lecture notes), Lemma 31.3 and Remark 31.5.
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.AbelianBanding

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat.{v'}}
  (b : F.AbelianBanding J A) [F.IsGerbe J] {U : C}

/-- The Isom torsors of a gerbe, contravariant in their source and covariant in their target.
An arrow `(e, f)` sends a local isomorphism `p` to `e|_T ≫ p ≫ f|_T`. -/
-- Exposed so that the sections of its values are the existing local morphisms of `F`, and
-- the action is the existing `sheafHomTorsor` action.
@[expose] noncomputable def sheafHomTorsorFunctor (U : C) :
    (F.obj (.mk (op U)))ᵒᵖ × F.obj (.mk (op U)) ⥤
      Sheaf.Torsor ((abelianSheafToGrpSheaf (J.over U)).obj
        ((J.overPullback AddCommGrpCat.{v'} U).obj A)) where
  obj p := b.sheafHomTorsor p.1.unop p.2 (IsGerbe.exists_covering_iso _ _)
  map {p q} f :=
    { hom := (F.sheafHomBifunctor J U).map f
      map_smul T a h := by
        let c := (abelianSheafToGrpSheafObjEquiv
          ((J.overPullback AddCommGrpCat.{v'} U).obj A) T).symm a
        let e := (F.map T.unop.hom.op.toLoc).toFunctor.map f.1.unop
        let g := (F.map T.unop.hom.op.toLoc).toFunctor.map f.2
        refine (congrArg (((F.sheafHomBifunctor J U).map f).hom.app T)
          (b.sheafHomTorsor_smul (IsGerbe.exists_covering_iso _ _) a h)).trans ?_
        refine (F.sheafHomBifunctor_map_hom_app J f T (b.homAct h c)).trans ?_
        have hact : e ≫ b.homAct h c ≫ g = b.homAct (e ≫ h ≫ g) c := by
          exact (congrArg (e ≫ ·) (b.homAct_comp_hom h (asIso g) c)).trans
            (b.comp_homAct e (h ≫ g) c)
        refine hact.trans ?_
        refine (congrArg (fun k ↦ b.homAct k c)
          (F.sheafHomBifunctor_map_hom_app J f T h).symm).trans ?_
        exact (b.sheafHomTorsor_smul (IsGerbe.exists_covering_iso _ _) a _).symm }
  map_id p := by
    apply Sheaf.Torsor.hom_ext
    exact (F.sheafHomBifunctor J U).map_id p
  map_comp f g := by
    apply Sheaf.Torsor.hom_ext
    exact (F.sheafHomBifunctor J U).map_comp f g

@[simp]
lemma sheafHomTorsorFunctor_obj (p : (F.obj (.mk (op U)))ᵒᵖ × F.obj (.mk (op U))) :
    (b.sheafHomTorsorFunctor U).obj p =
      b.sheafHomTorsor p.1.unop p.2 (IsGerbe.exists_covering_iso _ _) := (rfl)

/-- Evaluation of the transport of an Isom torsor on a local isomorphism. -/
@[simp]
lemma sheafHomTorsorFunctor_map_hom_app {p q : (F.obj (.mk (op U)))ᵒᵖ ×
    F.obj (.mk (op U))} (f : p ⟶ q) (T : (Over U)ᵒᵖ)
    (h : (F.presheafHom p.1.unop p.2).obj T) :
    ((b.sheafHomTorsorFunctor U).map f).hom.hom.app T h =
      (F.map T.unop.hom.op.toLoc).toFunctor.map f.1.unop ≫ h ≫
        (F.map T.unop.hom.op.toLoc).toFunctor.map f.2 :=
  F.sheafHomBifunctor_map_hom_app J f T h

end CategoryTheory.Pseudofunctor.AbelianBanding
