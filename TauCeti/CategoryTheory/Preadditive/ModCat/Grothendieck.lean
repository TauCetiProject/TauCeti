/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import TauCeti.CategoryTheory.Functor.LocallySmall
public import TauCeti.CategoryTheory.Preadditive.ModCat.Basic

import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.CategoryTheory.Preadditive.Transfer

/-!
# Grothendieck structure on modules over a preadditive category

The additive Yoneda lemma shows that the representable modules separate morphisms. On a small
preadditive category their coproduct is a projective separator, and every module is a quotient of
a coproduct of copies of this separator. This gives enough projectives on any essentially small
preadditive category by passing to a small model.

Filtered colimits of additive functors are exact because they are computed pointwise in abelian
groups. Together with the separator this makes the module category Grothendieck abelian, so
Mathlib's Grothendieck category API supplies `Ext` in the value universe.

## References

* B. Mitchell, *Rings with several objects*, Adv. Math. 8 (1972), 1–161, §3.
-/

public section

universe w v u

open CategoryTheory Limits Opposite

namespace TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Modules on an essentially small preadditive category have a projective separator, obtained
from the coproduct of the representables of a small model. -/
theorem exists_projective_separator [EssentiallySmall.{w} C] :
    ∃ G : ModCat.{w} C, Projective G ∧ IsSeparator G := by
  let e := equivSmallModel.{w} C
  let : Preadditive (SmallModel.{w} C) := Preadditive.ofFullyFaithful e.fullyFaithfulInverse
  have : e.inverse.Additive := e.fullyFaithfulInverse.additive_ofFullyFaithful
  have : e.functor.Additive := e.symm.additive_inverse_of_FullyFaithful
  have : e.functor.op.Additive := Functor.op_additive e.functor
  let E := e.op.symm.congrLeft (E := AddCommGrpCat.{w})
  let M : ModCat.{w} (SmallModel.{w} C) ≌ ModCat.{w} C := E.congrFullSubcategory (by
    ext F
    simp only [ObjectProperty.prop_inverseImage_iff, additiveFunctor_iff]
    -- The functor of the ambient equivalence acts by precomposition with `e.functor.op`.
    change (e.functor.op ⋙ F).Additive ↔ F.Additive
    exact ⟨fun _ ↦ e.functor.op.additive_of_full_essSurj_comp F, fun _ ↦ inferInstance⟩)
  let G := ∐ (yoneda (SmallModel.{w} C)).obj
  have hsep : IsSeparator G := isSeparating_yoneda.isSeparator_coproduct
  exact ⟨M.functor.obj G, (M.map_projective_iff G).2 inferInstance, hsep.of_equivalence M⟩

/-- The module category has filtered colimits in the value universe. -/
instance : HasFilteredColimitsOfSize.{w, w} (ModCat.{w} C) where
  HasColimitsOfShape := inferInstance

/-- Filtered colimits in the module category are exact, even for a large source category. -/
noncomputable instance : AB5OfSize.{w, w} (ModCat.{w} C) where
  ofShape J _ _ := by
    let P := additiveFunctor Cᵒᵖ AddCommGrpCat.{w}
    have : PreservesFiniteLimits P.ι := ⟨fun _ _ _ ↦ inferInstance⟩
    exact HasExactColimitsOfShape.domain_of_functor J P.ι

/-- The category of modules over an essentially small preadditive category is Grothendieck
abelian in the value universe. -/
noncomputable instance [EssentiallySmall.{w} C] : IsGrothendieckAbelian.{w} (ModCat.{w} C) where
  hasSeparator := by
    obtain ⟨G, _, hG⟩ := exists_projective_separator (C := C)
    exact ⟨G, hG⟩

/-- Modules over an essentially small preadditive category admit epimorphisms from projectives. -/
instance [EssentiallySmall.{w} C] : EnoughProjectives (ModCat.{w} C) where
  presentation F := by
    obtain ⟨G, hG, hsep⟩ := exists_projective_separator (C := C)
    have (M : ModCat.{w} C) := hasCoproductsOfShape_of_small.{w} (ModCat.{w} C) (G ⟶ M)
    have := (isSeparator_iff_epi G).1 hsep F
    exact ⟨{ p := ∐ fun _ : G ⟶ F ↦ G, f := Sigma.desc fun f : G ⟶ F ↦ f }⟩

end TauCeti.ModCat
