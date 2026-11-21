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

An fppf sheaf of sets `F` on schemes defines a stack in groupoids `StackInGroupoids.ofSheaf F`
(defined in `TauCeti.AlgebraicGeometry.Stack.StackInGroupoids`): its fibre over a scheme `T` is
the discrete groupoid on `F(T)`, with pullback given by the restriction maps of `F`. It is a stack
because `F` is a sheaf (`CategoryTheory.Pseudofunctor.isStack_ofPresheaf_iff`). This file
develops its API. This is how fppf sheaves, and in
particular algebraic spaces and schemes, are regarded as stacks in groupoids, so that 2-fibre
products and representability by algebraic spaces can be phrased inside the 2-category of stacks.

A morphism of fppf sheaves gives a morphism of the associated stacks
(`StackInGroupoids.ofSheafMap`). Since the fppf topology is subcanonical, every scheme `X`
defines the stack `StackInGroupoids.ofScheme X`, whose fibre over `T` is the discrete groupoid on
the set of morphisms `T ⟶ X`.

## Main declarations

* `TauCeti.AlgebraicGeometry.StackInGroupoids.ofSheaf.objEquiv`: the objects of the fibre over
  `T` of the stack in setoids of an fppf sheaf `F` are the elements of `F(T)`.
* `TauCeti.AlgebraicGeometry.StackInGroupoids.ofSheafMap`: the morphism of stacks induced by a
  morphism of fppf sheaves, with `ofSheafMapId` and `ofSheafMapComp` comparing it with identities
  and composites.
* `TauCeti.AlgebraicGeometry.StackInGroupoids.ofScheme`: the stack represented by a scheme, with
  `ofScheme.objEquiv` identifying the objects of its fibre over `T` with the morphisms `T ⟶ X`.

## References

* [Stacks Project, Lemma 8.6.3](https://stacks.math.columbia.edu/tag/0432)
-/

public section

open CategoryTheory Opposite

namespace TauCeti.AlgebraicGeometry.StackInGroupoids

open _root_.AlgebraicGeometry

universe u

/-- The objects of the fibre of the stack in setoids of `F` over `T` are the elements of
`F(T)`. -/
def ofSheaf.objEquiv (F : Sheaf Scheme.fppfTopology (Type u)) (T : Scheme.{u}) :
    (ofSheaf F).toSchPseudofunctor.obj (.mk (op T)) ≃ F.obj.obj (op T) :=
  Pseudofunctor.ofPresheaf.objEquiv (op T)

/-- Pulling back an object of the stack in setoids of `F` along `f` applies the restriction map
`F.map f.op`. -/
@[simp]
lemma ofSheaf.objEquiv_map_toFunctor_obj (F : Sheaf Scheme.fppfTopology (Type u))
    {T T' : Scheme.{u}} (f : T' ⟶ T) (M : (ofSheaf F).toSchPseudofunctor.obj (.mk (op T))) :
    ofSheaf.objEquiv F T' (((ofSheaf F).toSchPseudofunctor.map f.op.toLoc).toFunctor.obj M) =
      F.obj.map f.op (ofSheaf.objEquiv F T M) :=
  Pseudofunctor.ofPresheaf.objEquiv_map_toFunctor_obj f.op M

/-- The morphism of stacks in setoids induced by a morphism of fppf sheaves: on the fibre over
`T` it applies `α` at `T`. -/
def ofSheafMap {F G : Sheaf Scheme.fppfTopology (Type u)} (α : F ⟶ G) :
    (ofSheaf F).Hom (ofSheaf G) :=
  Pseudofunctor.ofPresheafMap α.hom

/-- The morphism of stacks induced by `α` applies `α` to the underlying elements. -/
@[simp]
lemma ofSheaf.objEquiv_ofSheafMap_app_toFunctor_obj {F G : Sheaf Scheme.fppfTopology (Type u)}
    (α : F ⟶ G) (T : Scheme.{u}) (M : (ofSheaf F).toSchPseudofunctor.obj (.mk (op T))) :
    ofSheaf.objEquiv G T (((ofSheafMap α).app (.mk (op T))).toFunctor.obj M) =
      α.hom.app (op T) (ofSheaf.objEquiv F T M) :=
  Pseudofunctor.ofPresheaf.objEquiv_ofPresheafMap_app_toFunctor_obj α.hom M

open scoped Pseudofunctor.StrongTrans in
/-- The morphism of stacks induced by the identity of an fppf sheaf is isomorphic to the
identity. -/
def ofSheafMapId (F : Sheaf Scheme.fppfTopology (Type u)) :
    Iso (C := (ofSheaf F).toSchPseudofunctor ⟶ (ofSheaf F).toSchPseudofunctor)
      (ofSheafMap (𝟙 F)) (Pseudofunctor.StrongTrans.id _) :=
  Pseudofunctor.ofPresheafMapId F.obj

open scoped Pseudofunctor.StrongTrans in
/-- The morphism of stacks induced by a composite of morphisms of fppf sheaves is isomorphic to
the composite of the induced morphisms of stacks. -/
def ofSheafMapComp {F G H : Sheaf Scheme.fppfTopology (Type u)} (α : F ⟶ G) (β : G ⟶ H) :
    Iso (C := (ofSheaf F).toSchPseudofunctor ⟶ (ofSheaf H).toSchPseudofunctor)
      (ofSheafMap (α ≫ β)) ((ofSheafMap α).vcomp (ofSheafMap β)) :=
  Pseudofunctor.ofPresheafMapComp α.hom β.hom

/-- The stack represented by a scheme `X`: the stack in setoids of the fppf sheaf
`T ↦ (T ⟶ X)`, which is a sheaf because the fppf topology is subcanonical. -/
@[expose, simps! toSchPseudofunctor]
def ofScheme (X : Scheme.{u}) : StackInGroupoids.{u} :=
  ofSheaf (Scheme.fppfTopology.yoneda.obj X)

/-- The objects of the fibre of the stack represented by `X` over `T` are the morphisms
`T ⟶ X`. -/
def ofScheme.objEquiv (X T : Scheme.{u}) :
    (ofScheme X).toSchPseudofunctor.obj (.mk (op T)) ≃ (T ⟶ X) :=
  ofSheaf.objEquiv _ T

/-- Pulling back an object `T ⟶ X` of the stack represented by `X` along `f` is composition with
`f`. -/
@[simp]
lemma ofScheme.objEquiv_map_toFunctor_obj (X : Scheme.{u}) {T T' : Scheme.{u}} (f : T' ⟶ T)
    (M : (ofScheme X).toSchPseudofunctor.obj (.mk (op T))) :
    ofScheme.objEquiv X T' (((ofScheme X).toSchPseudofunctor.map f.op.toLoc).toFunctor.obj M) =
      f ≫ ofScheme.objEquiv X T M :=
  ofSheaf.objEquiv_map_toFunctor_obj _ f M

end TauCeti.AlgebraicGeometry.StackInGroupoids
