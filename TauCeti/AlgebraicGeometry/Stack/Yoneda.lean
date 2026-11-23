/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Stack.OfSheaf
public import TauCeti.CategoryTheory.Sites.Descent.Yoneda

/-!
# The 2-Yoneda lemma for stacks in groupoids

A scheme `T` defines the stack in setoids `h_T = StackInGroupoids.ofScheme T` of its functor of
points, which is an fppf sheaf because the fppf topology is subcanonical. The 2-Yoneda lemma
identifies morphisms of stacks `h_T → 𝒳` with objects of the fibre `𝒳(T)`: evaluating a morphism at
`𝟙 T` is an equivalence between the groupoid of morphisms `h_T → 𝒳` (with invertible modifications
as arrows) and the groupoid `𝒳(T)`, whose inverse sends `x` to the morphism `f ↦ f^* x`. In
particular the automorphisms of the morphism `h_T → 𝒳` attached to `x` are the automorphisms of `x`.
This is how an object `x ∈ 𝒳(T)` is regarded as a morphism `T → 𝒳`, for instance to form 2-fibre
products `T ×_𝒳 𝒴`.

## Main declarations

* `TauCeti.AlgebraicGeometry.StackInGroupoids.yonedaEquiv`: the equivalence of groupoids
  `Hom(h_T, 𝒳) ≌ 𝒳(T)`.

## References

* [Stacks Project, Lemma 004B](https://stacks.math.columbia.edu/tag/004B)
-/

@[expose] public section

open CategoryTheory Opposite Pseudofunctor.StrongTrans

namespace TauCeti.AlgebraicGeometry.StackInGroupoids

open _root_.AlgebraicGeometry

universe u

/-- The 2-Yoneda lemma for stacks in groupoids (Stacks, Lemma 004B): evaluation at `𝟙 T` is an
equivalence between the groupoid of morphisms `h_T → 𝒳` (with invertible modifications as
morphisms) and the fibre `𝒳(T)`. Its inverse sends `x` to the morphism whose component at
`f : T' ⟶ T` is `f^* x`. -/
@[stacks 004B]
def yonedaEquiv (T : Scheme.{u}) (𝒳 : StackInGroupoids.{u}) :
    ((ofScheme T).toSchPseudofunctor ⟶ 𝒳.toSchPseudofunctor) ≌
      𝒳.toSchPseudofunctor.obj (.mk (op T)) :=
  Pseudofunctor.yonedaEquiv.{u + 1} 𝒳.toSchPseudofunctor T

@[simp]
lemma yonedaEquiv_functor (T : Scheme.{u}) (𝒳 : StackInGroupoids.{u}) :
    (yonedaEquiv T 𝒳).functor = Pseudofunctor.yonedaEvaluation.{u + 1} 𝒳.toSchPseudofunctor T :=
  rfl

@[simp]
lemma yonedaEquiv_inverse (T : Scheme.{u}) (𝒳 : StackInGroupoids.{u}) :
    (yonedaEquiv T 𝒳).inverse = Pseudofunctor.yonedaPullback.{u + 1} 𝒳.toSchPseudofunctor T :=
  rfl

@[simp]
lemma yonedaEquiv_counitIso (T : Scheme.{u}) (𝒳 : StackInGroupoids.{u}) :
    (yonedaEquiv T 𝒳).counitIso = Pseudofunctor.yonedaCounitIso.{u + 1} 𝒳.toSchPseudofunctor T :=
  rfl

end TauCeti.AlgebraicGeometry.StackInGroupoids
