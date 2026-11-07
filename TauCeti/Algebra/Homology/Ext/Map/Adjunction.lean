/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import TauCeti.Algebra.Homology.Ext.Basic

/-!
# Exact adjunctions and Ext with fixed coefficients

For an adjunction `F ⊣ G` between exact functors of abelian categories, if the unit
`Y → G(F(Y))` is an isomorphism, then `F` induces a bijection on `Extⁿ(X, Y)` for every
`X` and every degree. Neither functor needs to be fully faithful on the whole category.

This criterion applies, for example, to extension of scalars along a flat ring map
which leaves a particular coefficient module unchanged.

The proof uses Mathlib's `CategoryTheory.Adjunction.extEquiv`, together with transport
of Ext along the unit isomorphism.
-/

public section

open CategoryTheory.Abelian CategoryTheory.Limits

namespace CategoryTheory.Adjunction

universe w w' v v' u u'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- An exact left adjoint preserves Ext bijectively with coefficients in any object
on which the adjunction unit is an isomorphism. The source object is unrestricted. -/
theorem mapExt_bijective_of_isIso_unit_app (adj : F ⊣ G) (X Y : C) (n : ℕ)
    [IsIso (adj.unit.app Y)] : Function.Bijective (F.mapExtAddHom.{w, w'} X Y n) := by
  let e : Ext.{w} X Y n ≃+ Ext.{w'} (F.obj X) (F.obj Y) n :=
    (TauCeti.extAddEquivOfIso (Iso.refl X) (asIso (adj.unit.app Y)) n).trans
      adj.extEquiv.symm
  have he (α : Ext.{w} X Y n) : e α = α.mapExactFunctor F := by
    simp [e, Adjunction.extEquiv_symm_apply, Ext.mapExactFunctor_comp,
      Ext.mapExactFunctor_mk₀]
  exact (funext he).subst (motive := Function.Bijective) e.bijective

end CategoryTheory.Adjunction
