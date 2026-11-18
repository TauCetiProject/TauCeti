/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import TauCeti.AlgebraicGeometry.Stack.StackInGroupoids
public import TauCeti.CategoryTheory.Sites.Descent.Discrete

/-!
# The stack in setoids of an fppf sheaf

An fppf sheaf of sets `F` on schemes defines a stack in groupoids `StackInGroupoids.ofSheaf F`:
its fibre over a scheme `T` is the discrete groupoid on `F(T)`, with pullback given by the
restriction maps of `F`. It is a stack because `F` is a sheaf
(`CategoryTheory.Functor.isStack_discretePseudofunctor_iff`). This is how fppf sheaves, and in
particular algebraic spaces and schemes, are regarded as stacks in groupoids, so that 2-fibre
products and representability by algebraic spaces can be phrased inside the 2-category of stacks.

A morphism of fppf sheaves gives a morphism of the associated stacks
(`StackInGroupoids.ofSheafMap`). Since the fppf topology is subcanonical, every scheme `X`
defines the stack `StackInGroupoids.ofScheme X`, whose fibre over `T` is the discrete groupoid on
the set of morphisms `T ⟶ X`.

## Main declarations

* `TauCeti.AlgebraicGeometry.StackInGroupoids.ofSheaf`: the stack in setoids of an fppf sheaf.
* `TauCeti.AlgebraicGeometry.StackInGroupoids.ofSheafMap`: the morphism of stacks induced by a
  morphism of fppf sheaves, with `ofSheafMapId` and `ofSheafMapComp` comparing it with identities
  and composites.
* `TauCeti.AlgebraicGeometry.StackInGroupoids.ofScheme`: the stack represented by a scheme.

## References

* [Stacks Project, Lemma 8.6.3](https://stacks.math.columbia.edu/tag/0432)
-/

public section

open CategoryTheory Opposite

open CategoryTheory.Functor.discretePseudofunctor (objEquiv)

namespace TauCeti.AlgebraicGeometry.StackInGroupoids

open _root_.AlgebraicGeometry

universe u

/-- The stack in setoids of an fppf sheaf of sets `F` on schemes: the fibre over `T` is the
discrete groupoid on `F(T)`, and pullback along `f : T' ⟶ T` is `F.map f.op`. -/
@[expose, simps toSchPseudofunctor, stacks 0432]
def ofSheaf (F : Sheaf Scheme.fppfTopology (Type u)) : StackInGroupoids.{u} where
  toSchPseudofunctor := F.obj.discretePseudofunctor.{u + 1}
  isGroupoid _ := inferInstance
  isStack := (F.obj.isStack_discretePseudofunctor_iff _).2
    ((isSheaf_iff_isSheaf_of_type _ _).1 F.property)

/-- Pulling back an object of the stack in setoids of `F` along `f` applies the restriction map
`F.map f.op`. -/
@[simp]
lemma objEquiv_ofSheaf_map_toFunctor_obj (F : Sheaf Scheme.fppfTopology (Type u))
    {T T' : Scheme.{u}} (f : T' ⟶ T) (M : (ofSheaf F).toSchPseudofunctor.obj (.mk (op T))) :
    objEquiv _ (((ofSheaf F).toSchPseudofunctor.map f.op.toLoc).toFunctor.obj M) =
      F.obj.map f.op (objEquiv _ M) :=
  Functor.discretePseudofunctor.objEquiv_map_toFunctor_obj f.op M

/-- The morphism of stacks in setoids induced by a morphism of fppf sheaves: on the fibre over
`T` it applies `α` at `T`. -/
def ofSheafMap {F G : Sheaf Scheme.fppfTopology (Type u)} (α : F ⟶ G) :
    (ofSheaf F).Hom (ofSheaf G) :=
  Functor.discretePseudofunctorMap α.hom

/-- The morphism of stacks induced by `α` applies `α` to the underlying elements. -/
@[simp]
lemma objEquiv_ofSheafMap_app_toFunctor_obj {F G : Sheaf Scheme.fppfTopology (Type u)}
    (α : F ⟶ G) (T : Scheme.{u}) (M : (ofSheaf F).toSchPseudofunctor.obj (.mk (op T))) :
    objEquiv _ (((ofSheafMap α).app (.mk (op T))).toFunctor.obj M) =
      α.hom.app (op T) (objEquiv _ M) :=
  Functor.discretePseudofunctor.objEquiv_discretePseudofunctorMap_app_toFunctor_obj α.hom M

open scoped Pseudofunctor.StrongTrans in
/-- The morphism of stacks induced by the identity of an fppf sheaf is isomorphic to the
identity. -/
def ofSheafMapId (F : Sheaf Scheme.fppfTopology (Type u)) :
    Iso (C := (ofSheaf F).toSchPseudofunctor ⟶ (ofSheaf F).toSchPseudofunctor)
      (ofSheafMap (𝟙 F)) (Pseudofunctor.StrongTrans.id _) :=
  Functor.discretePseudofunctorMapId F.obj

open scoped Pseudofunctor.StrongTrans in
/-- The morphism of stacks induced by a composite of morphisms of fppf sheaves is isomorphic to
the composite of the induced morphisms of stacks. -/
def ofSheafMapComp {F G H : Sheaf Scheme.fppfTopology (Type u)} (α : F ⟶ G) (β : G ⟶ H) :
    Iso (C := (ofSheaf F).toSchPseudofunctor ⟶ (ofSheaf H).toSchPseudofunctor)
      (ofSheafMap (α ≫ β)) ((ofSheafMap α).vcomp (ofSheafMap β)) :=
  Functor.discretePseudofunctorMapComp α.hom β.hom

/-- The stack represented by a scheme `X`: the stack in setoids of the fppf sheaf
`T ↦ (T ⟶ X)`, which is a sheaf because the fppf topology is subcanonical. -/
@[expose, simps! toSchPseudofunctor]
def ofScheme (X : Scheme.{u}) : StackInGroupoids.{u} :=
  ofSheaf (Scheme.fppfTopology.yoneda.obj X)

/-- Pulling back an object `T ⟶ X` of the stack represented by `X` along `f` is composition with
`f`. -/
@[simp]
lemma objEquiv_ofScheme_map_toFunctor_obj (X : Scheme.{u}) {T T' : Scheme.{u}} (f : T' ⟶ T)
    (M : (ofScheme X).toSchPseudofunctor.obj (.mk (op T))) :
    objEquiv (P := yoneda.obj X) _
        (((ofScheme X).toSchPseudofunctor.map f.op.toLoc).toFunctor.obj M) =
      f ≫ objEquiv (P := yoneda.obj X) _ M :=
  Functor.discretePseudofunctor.objEquiv_map_toFunctor_obj f.op M

end TauCeti.AlgebraicGeometry.StackInGroupoids
