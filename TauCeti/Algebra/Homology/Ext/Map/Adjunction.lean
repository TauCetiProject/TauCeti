/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import TauCeti.Algebra.Homology.Ext.Basic
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Exact adjunctions and Ext with fixed coefficients

For an adjunction `F ⊣ G` between exact functors of abelian categories, bijectivity of the
map on `Extⁿ(X, Y)` is equivalent to bijectivity of postcomposition with the unit
`Y → G(F(Y))`. In particular, if this unit is an isomorphism, then `F` induces a bijection on
`Extⁿ(X, Y)` for every `X` and every degree. Neither functor needs to be fully faithful on the
whole category.

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

omit [G.Additive] [PreservesFiniteLimits G] in
/-- Under an exact adjunction, bijectivity of the map on Ext is equivalent to bijectivity of
postcomposition with the adjunction unit on the coefficient object. -/
theorem mapExt_bijective_iff_postcomp_unit_app (adj : F ⊣ G) (X Y : C) (n : ℕ) :
    Function.Bijective (F.mapExtAddHom.{w, w'} X Y n) ↔
      Function.Bijective ((Ext.mk₀ (adj.unit.app Y)).postcomp X (add_zero n)) := by
  -- A right adjoint of an additive functor is additive and preserves finite limits.
  have := adj.right_adjoint_additive
  have : G.IsRightAdjoint := adj.isRightAdjoint
  have : PreservesFiniteLimits G := inferInstance
  have he : adj.extEquiv.symm ∘
      (Ext.mk₀ (adj.unit.app Y)).postcomp X (add_zero n) = F.mapExtAddHom X Y n := by
    funext a
    simp [Adjunction.extEquiv_symm_apply, Ext.mapExactFunctor_comp,
      Ext.mapExactFunctor_mk₀]
  rw [← he]
  exact adj.extEquiv.symm.bijective.of_comp_iff' _

omit [G.Additive] [PreservesFiniteLimits G] in
/-- For an adjunction `F ⊣ G` between exact functors, `F` preserves Ext bijectively with
coefficients in any object on which the unit is an isomorphism. The source object is
unrestricted. -/
theorem mapExt_bijective_of_isIso_unit_app (adj : F ⊣ G) (X Y : C) (n : ℕ)
    [IsIso (adj.unit.app Y)] : Function.Bijective (F.mapExtAddHom.{w, w'} X Y n) := by
  apply (adj.mapExt_bijective_iff_postcomp_unit_app X Y n).mpr
  let e := TauCeti.extAddEquivOfIso (Iso.refl X) (asIso (adj.unit.app Y)) n
  have he : ⇑e = ⇑((Ext.mk₀ (adj.unit.app Y)).postcomp X (add_zero n)) := by
    funext α
    simp [e]
  exact he ▸ e.bijective

end CategoryTheory.Adjunction
