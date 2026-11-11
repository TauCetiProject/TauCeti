/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import TauCeti.AlgebraicGeometry.Stack.Basic

/-!
# Stacks in groupoids over schemes

A stack in groupoids over schemes is a `Cat`-valued pseudofunctor on schemes
(a `SchPseudofunctor`) whose fibre categories are groupoids and which is a stack, in the sense of
Mathlib's `Pseudofunctor.IsStack`, for the fppf topology (Stacks, Definitions 026F and 02ZI).
Morphisms of stacks in groupoids are strong transformations of the underlying pseudofunctors.

## Main declarations

* `TauCeti.AlgebraicGeometry.StackInGroupoids`: stacks in groupoids over schemes for the fppf
  topology.
* `TauCeti.AlgebraicGeometry.StackInGroupoids.Hom`: morphisms of stacks in groupoids, the strong
  transformations of the underlying pseudofunctors, with identities `Hom.id` and composition
  `Hom.comp`.
* `TauCeti.AlgebraicGeometry.StackInGroupoids.Hom.IsFibrewiseEquiv`: a morphism whose component
  on every scheme is an equivalence of fibre groupoids. It holds for identities, is closed under
  composition, and satisfies two-out-of-three.

## References

* [Stacks Project, Definition 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Definition 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
-/

public section

open CategoryTheory Bicategory Opposite

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

/-- A stack in groupoids over schemes: a `Cat`-valued pseudofunctor on schemes whose fibre
categories are groupoids and which is a stack for the fppf topology (Stacks, Definitions 026F
and 02ZI). -/
@[stacks 02ZI]
structure StackInGroupoids where
  /-- The underlying pseudofunctor on schemes. -/
  toSchPseudofunctor : SchPseudofunctor.{u}
  /-- Every fibre category is a groupoid. -/
  isGroupoid (T : Scheme.{u}) : IsGroupoid (toSchPseudofunctor.obj (.mk (op T)))
  /-- The underlying pseudofunctor is a stack for the fppf topology. -/
  isStack : toSchPseudofunctor.IsStack Scheme.fppfTopology

namespace StackInGroupoids

attribute [instance] StackInGroupoids.isGroupoid StackInGroupoids.isStack

/-- Morphisms of stacks in groupoids: strong transformations of the underlying pseudofunctors. -/
abbrev Hom (X Y : StackInGroupoids.{u}) : Type (u + 1) :=
  Pseudofunctor.StrongTrans X.toSchPseudofunctor Y.toSchPseudofunctor

namespace Hom

/-- The identity morphism of a stack in groupoids. -/
abbrev id (X : StackInGroupoids.{u}) : Hom X X :=
  Pseudofunctor.StrongTrans.id X.toSchPseudofunctor

/-- The composition of morphisms of stacks in groupoids. -/
abbrev comp {X Y Z : StackInGroupoids.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  Pseudofunctor.StrongTrans.vcomp f g

@[simp]
lemma id_app (X : StackInGroupoids.{u}) (T : Scheme.{u}) :
    (id X).app (.mk (op T)) = 𝟙 (X.toSchPseudofunctor.obj (.mk (op T))) :=
  rfl

@[simp]
lemma comp_app {X Y Z : StackInGroupoids.{u}} (f : Hom X Y) (g : Hom Y Z) (T : Scheme.{u}) :
    (comp f g).app (.mk (op T)) = f.app (.mk (op T)) ≫ g.app (.mk (op T)) :=
  rfl

/-- A morphism of stacks in groupoids is a fibrewise equivalence if its component on every
scheme is an equivalence of fibre groupoids. -/
def IsFibrewiseEquiv {X Y : StackInGroupoids.{u}} (f : Hom X Y) : Prop :=
  ∀ T : Scheme.{u}, (f.app (.mk (op T))).toFunctor.IsEquivalence

lemma isFibrewiseEquiv_iff {X Y : StackInGroupoids.{u}} (f : Hom X Y) :
    f.IsFibrewiseEquiv ↔ ∀ T : Scheme.{u}, (f.app (.mk (op T))).toFunctor.IsEquivalence :=
  Iff.rfl

lemma isFibrewiseEquiv_id (X : StackInGroupoids.{u}) : (id X).IsFibrewiseEquiv := fun _ ↦
  inferInstanceAs (Functor.id _).IsEquivalence

variable {X Y Z : StackInGroupoids.{u}} {f : Hom X Y} {g : Hom Y Z}

lemma IsFibrewiseEquiv.comp (hf : f.IsFibrewiseEquiv) (hg : g.IsFibrewiseEquiv) :
    (comp f g).IsFibrewiseEquiv := fun T ↦
  have := hf T
  have := hg T
  inferInstanceAs ((f.app (.mk (op T))).toFunctor ⋙ (g.app (.mk (op T))).toFunctor).IsEquivalence

/-- If `g` and the composite `comp f g` are fibrewise equivalences, so is `f`. -/
lemma IsFibrewiseEquiv.of_comp_right (hg : g.IsFibrewiseEquiv)
    (hfg : (f.comp g).IsFibrewiseEquiv) : f.IsFibrewiseEquiv := fun T ↦
  have := hg T
  have : ((f.app (.mk (op T))).toFunctor ⋙ (g.app (.mk (op T))).toFunctor).IsEquivalence :=
    hfg T
  Functor.isEquivalence_of_comp_right _ (g.app (.mk (op T))).toFunctor

/-- If `f` and the composite `comp f g` are fibrewise equivalences, so is `g`. -/
lemma IsFibrewiseEquiv.of_comp_left (hf : f.IsFibrewiseEquiv)
    (hfg : (f.comp g).IsFibrewiseEquiv) : g.IsFibrewiseEquiv := fun T ↦
  have := hf T
  have : ((f.app (.mk (op T))).toFunctor ⋙ (g.app (.mk (op T))).toFunctor).IsEquivalence :=
    hfg T
  Functor.isEquivalence_of_comp_left (f.app (.mk (op T))).toFunctor _

end Hom

end StackInGroupoids

end TauCeti.AlgebraicGeometry
