/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Stack.StackInGroupoids
public import TauCeti.CategoryTheory.Sites.Descent.TwoFiberProduct

/-!
# 2-fibre products of stacks in groupoids

For morphisms `f : X ⟶ Z` and `g : Y ⟶ Z` of stacks in groupoids over schemes, the 2-fibre product
`X ×_Z Y` is the site-level 2-fibre product `TauCeti.Stack.twoFiberProduct f g` of the underlying
pseudofunctors, objectwise Mathlib's `CategoricalPullback`: over a scheme `T` its objects are
triples `(x, y, φ)` with `x ∈ X(T)`, `y ∈ Y(T)` and `φ : f x ≅ g y`. Its fibres are groupoids
(`TauCeti.Stack.twoFiberProduct.isGroupoid_obj`) and it is an fppf stack (Stacks, Lemma 8.4.6
(026G), `TauCeti.Stack.twoFiberProduct.isStack`), so it is a stack in groupoids
(Stacks, Lemma 8.5.6 (02ZL)).

The 2-fibre product along a fiberwise equivalence, in particular along the identity of `Z`,
recovers the other factor: its second projection is a fiberwise equivalence
(`TauCeti.AlgebraicGeometry.StackInGroupoids.twoFiberProduct.isFiberwiseEquiv_snd_id`).

## Main definitions

* `TauCeti.AlgebraicGeometry.StackInGroupoids.twoFiberProduct f g`: the 2-fibre product. Its
  underlying pseudofunctor is `TauCeti.Stack.twoFiberProduct f g` by definition, so its projections,
  the 2-cell `fst ≫ f ≅ snd ≫ g` and the morphism from a 2-commutative square are the site-level
  `TauCeti.Stack.twoFiberProduct.fst`, `.snd`, `.iso` and `.lift`.

## Main results

* `TauCeti.AlgebraicGeometry.StackInGroupoids.twoFiberProduct.isFiberwiseEquiv_snd`: the second
  projection of the 2-fibre product along a fiberwise equivalence is a fiberwise equivalence;
  `isFiberwiseEquiv_fst` is the symmetric statement.

## References

* [Stacks Project, Lemma 026G](https://stacks.math.columbia.edu/tag/026G)
* [Stacks Project, Lemma 02ZL](https://stacks.math.columbia.edu/tag/02ZL)
-/

public section

open CategoryTheory Bicategory Opposite
open scoped Pseudofunctor.StrongTrans

namespace TauCeti.AlgebraicGeometry.StackInGroupoids

open _root_.AlgebraicGeometry

universe u

variable {X Y Z : StackInGroupoids.{u}} (f : X.toSchPseudofunctor ⟶ Z.toSchPseudofunctor)
  (g : Y.toSchPseudofunctor ⟶ Z.toSchPseudofunctor)

/-- The **2-fibre product** `X ×_Z Y` of two morphisms of stacks in groupoids, the site-level
2-fibre product of the underlying pseudofunctors (Stacks, Lemmas 026G and 02ZL). -/
@[expose, stacks 02ZL]
noncomputable def twoFiberProduct : StackInGroupoids.{u} where
  toSchPseudofunctor := Stack.twoFiberProduct.{u + 1, u} f g
  isGroupoid _ := inferInstance
  isStack := inferInstance

namespace twoFiberProduct

/-- The underlying pseudofunctor of the 2-fibre product is the site-level 2-fibre product, so its
projections, 2-cell and lift are `TauCeti.Stack.twoFiberProduct.fst`, `.snd`, `.iso` and `.lift`. -/
@[simp]
theorem toSchPseudofunctor_eq :
    (twoFiberProduct f g).toSchPseudofunctor = Stack.twoFiberProduct.{u + 1, u} f g :=
  (rfl)

/-- **2-base change of a fiberwise equivalence.** The second projection of the 2-fibre product
along a fiberwise equivalence `f` is a fiberwise equivalence. -/
theorem isFiberwiseEquiv_snd (hf : Hom.IsFiberwiseEquiv f) :
    Hom.IsFiberwiseEquiv (X := twoFiberProduct f g) (Stack.twoFiberProduct.snd.{u + 1, u} f g) :=
  (Hom.isFiberwiseEquiv_iff _).mpr fun T ↦
  have := (Hom.isFiberwiseEquiv_iff f).mp hf T
  Stack.twoFiberProduct.isEquivalence_snd_app.{u + 1, u} f g (.mk (op T))

/-- **2-base change of a fiberwise equivalence.** The first projection of the 2-fibre product
along a fiberwise equivalence `g` is a fiberwise equivalence. -/
theorem isFiberwiseEquiv_fst (hg : Hom.IsFiberwiseEquiv g) :
    Hom.IsFiberwiseEquiv (X := twoFiberProduct f g) (Stack.twoFiberProduct.fst.{u + 1, u} f g) :=
  (Hom.isFiberwiseEquiv_iff _).mpr fun T ↦
  have := (Hom.isFiberwiseEquiv_iff g).mp hg T
  Stack.twoFiberProduct.isEquivalence_fst_app.{u + 1, u} f g (.mk (op T))

/-- **A 2-fibre product along the identity recovers the other factor**: for `g : Y ⟶ Z`, the
second projection `Z ×_Z Y ⟶ Y` is a fiberwise equivalence. -/
theorem isFiberwiseEquiv_snd_id :
    Hom.IsFiberwiseEquiv (X := twoFiberProduct (𝟙 Z.toSchPseudofunctor) g)
      (Stack.twoFiberProduct.snd.{u + 1, u} (𝟙 Z.toSchPseudofunctor) g) :=
  isFiberwiseEquiv_snd _ g (Hom.isFiberwiseEquiv_id Z)

end twoFiberProduct

end TauCeti.AlgebraicGeometry.StackInGroupoids
