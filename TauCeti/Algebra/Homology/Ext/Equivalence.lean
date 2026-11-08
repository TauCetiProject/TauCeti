/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.Map.Adjunction
public import TauCeti.CategoryTheory.Abelian.Projective.Dimension

/-!
# `Ext` groups are invariant under an additive equivalence

An additive equivalence `e` induces an additive equivalence on `Ext` groups via
`e.functor.mapExtAddHom`, whose underlying map is
`CategoryTheory.Abelian.Ext.mapExactFunctor`. Bijectivity follows from
`CategoryTheory.Adjunction.mapExt_bijective_of_isIso_unit_app` applied to `e.toAdjunction`.
That criterion uses Mathlib's `CategoryTheory.Adjunction.extEquiv`. Since projective dimension
is defined by the vanishing of `Ext`, it is invariant under any equivalence of abelian
categories, which is automatically additive.

## Main definitions

* `CategoryTheory.Equivalence.extAddEquiv`: `Extⁿ(X, Y) ≃+ Extⁿ(e X, e Y)` for an additive
  equivalence `e`.
* `TauCeti.extLinearEquivOfEquivalence`: its `R`-linear refinement for an `R`-linear equivalence
  of `R`-linear abelian categories.  `R`-linearity of `e` is genuinely needed for the linear
  statement: an additive isomorphism of `k`-vector spaces need not preserve dimension.

## Main results

* `CategoryTheory.Equivalence.mapExtAddHom_bijective`: the forward functor of an additive
  equivalence is bijective on `Ext`.
* `CategoryTheory.Equivalence.projectiveDimension_functor_obj`: an equivalence of abelian
  categories preserves projective dimension.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w w' v v' u u' t

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]

section Ext

variable [HasExt.{w} C] [HasExt.{w'} D]

/-- **`Ext` groups are invariant under an additive equivalence.** The additive equivalence
`Extⁿ(X, Y) ≃+ Extⁿ(e X, e Y)` has underlying map
`CategoryTheory.Abelian.Ext.mapExactFunctor` for `e.functor`. -/
noncomputable def _root_.CategoryTheory.Equivalence.extAddEquiv
    (e : C ≌ D) [e.functor.Additive] (X Y : C) (n : ℕ) :
    Ext.{w} X Y n ≃+ Ext.{w'} (e.functor.obj X) (e.functor.obj Y) n :=
  AddEquiv.ofBijective (e.functor.mapExtAddHom X Y n)
    (e.toAdjunction.mapExt_bijective_of_isIso_unit_app X Y n)

@[simp]
theorem _root_.CategoryTheory.Equivalence.extAddEquiv_apply
    (e : C ≌ D) [e.functor.Additive] {X Y : C} {n : ℕ}
    (α : Ext.{w} X Y n) :
    e.extAddEquiv X Y n α = α.mapExactFunctor e.functor := (rfl)

/-- The forward functor of an additive equivalence induces a bijection on `Ext` groups. -/
theorem _root_.CategoryTheory.Equivalence.mapExtAddHom_bijective
    (e : C ≌ D) [e.functor.Additive] (X Y : C) (n : ℕ) :
    Function.Bijective (e.functor.mapExtAddHom.{w, w'} X Y n) :=
  e.toAdjunction.mapExt_bijective_of_isIso_unit_app X Y n

/-- **The `R`-linear refinement of `CategoryTheory.Equivalence.extAddEquiv`.**  For an `R`-linear
equivalence of `R`-linear abelian categories, `Extⁿ(X, Y)` and `Extⁿ(e X, e Y)` are isomorphic as
`R`-modules. -/
noncomputable def extLinearEquivOfEquivalence (R : Type t) [Ring R] [Linear R C] [Linear R D]
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear R] (X Y : C) (n : ℕ) :
    Ext.{w} X Y n ≃ₗ[R] Ext.{w'} (e.functor.obj X) (e.functor.obj Y) n where
  __ := e.extAddEquiv X Y n
  map_smul' r α := by simp

@[simp]
theorem extLinearEquivOfEquivalence_apply (R : Type t) [Ring R] [Linear R C] [Linear R D]
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear R] {X Y : C} {n : ℕ}
    (α : Ext.{w} X Y n) :
    extLinearEquivOfEquivalence R e X Y n α = α.mapExactFunctor e.functor :=
  e.extAddEquiv_apply α

end Ext

/-- **Projective dimension bounds are invariant under an equivalence.**  The object `e X` has
projective dimension `< n` exactly when `X` does.  No additivity hypothesis is needed: an
equivalence of abelian categories is automatically additive. -/
@[simp]
theorem _root_.CategoryTheory.Equivalence.hasProjectiveDimensionLT_functor_obj_iff
    (e : C ≌ D) (X : C) (n : ℕ) :
    HasProjectiveDimensionLT (e.functor.obj X) n ↔ HasProjectiveDimensionLT X n := by
  have := e.functor.additive_of_preserves_binary_products
  let := HasExt.standard C
  let := HasExt.standard D
  simp only [hasProjectiveDimensionLT_iff]
  refine ⟨fun h i hi Y α ↦ (e.extAddEquiv X Y i).injective ?_, fun h i hi Y β ↦ ?_⟩
  · rw [map_zero]
    exact h i hi _
  · simpa only [AddEquivClass.map_eq_zero_iff] using h i hi ((e.extAddEquiv X _ i).symm
      ((extAddEquivOfIso (Iso.refl _) (e.counitIso.app Y) i).symm β))

/-- **An equivalence of abelian categories preserves projective dimension.** -/
@[simp]
theorem _root_.CategoryTheory.Equivalence.projectiveDimension_functor_obj
    (e : C ≌ D) (X : C) :
    projectiveDimension (e.functor.obj X) = projectiveDimension X :=
  le_antisymm
    (projectiveDimension_le_of_hasProjectiveDimensionLT fun n ↦
      (e.hasProjectiveDimensionLT_functor_obj_iff X n).mpr)
    (projectiveDimension_le_of_hasProjectiveDimensionLT fun n ↦
      (e.hasProjectiveDimensionLT_functor_obj_iff X n).mp)

end TauCeti
