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
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.CategoryTheory.Preadditive.Transfer

/-!
# Grothendieck structure on modules over a preadditive category

The additive Yoneda lemma shows that the representable modules separate morphisms. On a small
preadditive category their coproduct is a projective separator, and every module is a quotient of
a coproduct of copies of this separator.

The results here are about `ModCat.{w} C`, the modules with values in `AddCommGrpCat.{w}`, and
they assume that `C` is essentially small in the same universe `w` (`EssentiallySmall.{w} C`).
The value universe cannot be chosen independently of the size of `C`: the separator and the
projective presentations are built from a `w`-small model of `C`.

Filtered colimits of additive functors are exact because they are computed pointwise in abelian
groups. Together with the separator this makes `ModCat.{w} C` Grothendieck abelian in the
universe `w`, so Mathlib's Grothendieck category API supplies `Ext` groups that live in `w`.

## References

* B. Mitchell, *Rings with several objects*, Adv. Math. 8 (1972), 1–161, §3.
-/

public section

universe w v u

open CategoryTheory Limits Opposite

namespace TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- If `C` is essentially small in the universe `w`, then the category `ModCat.{w} C` of modules
with values in `AddCommGrpCat.{w}` has a projective separator, obtained from the coproduct of the
representables of a `w`-small model of `C`. -/
theorem exists_projective_separator [EssentiallySmall.{w} C] :
    ∃ G : ModCat.{w} C, Projective G ∧ IsSeparator G := by
  let e := equivSmallModel.{w} C
  let : Preadditive (SmallModel.{w} C) := Preadditive.ofFullyFaithful e.fullyFaithfulInverse
  have : e.inverse.Additive := e.fullyFaithfulInverse.additive_ofFullyFaithful
  have : e.functor.Additive := e.symm.additive_inverse_of_FullyFaithful
  have : e.op.functor.Additive := Functor.op_additive e.functor
  let M : ModCat.{w} (SmallModel.{w} C) ≌ ModCat.{w} C :=
    (e.op.additiveCongrLeft (E := AddCommGrpCat.{w})).symm
  let G := ∐ (yoneda (SmallModel.{w} C)).obj
  have hsep : IsSeparator G := isSeparating_yoneda.isSeparator_coproduct
  exact ⟨M.functor.obj G, (M.map_projective_iff G).2 inferInstance, hsep.of_equivalence M⟩

/-- If `C` is essentially small in the universe `w`, then `ModCat.{w} C` is Grothendieck abelian
in the universe `w`. Hence Mathlib's `HasExt.{w}` instance for Grothendieck abelian categories
applies, and the `Ext` groups of `ModCat.{w} C` live in `w`. -/
noncomputable instance [EssentiallySmall.{w} C] : IsGrothendieckAbelian.{w} (ModCat.{w} C) where
  hasSeparator := by
    obtain ⟨G, _, hG⟩ := exists_projective_separator (C := C)
    exact ⟨G, hG⟩

/-- If `C` is essentially small in the universe `w`, then `ModCat.{w} C` has enough projectives:
every module is a quotient of a coproduct of copies of the projective separator. -/
instance [EssentiallySmall.{w} C] : EnoughProjectives (ModCat.{w} C) where
  presentation F := by
    obtain ⟨G, hG, hsep⟩ := exists_projective_separator (C := C)
    have (M : ModCat.{w} C) := hasCoproductsOfShape_of_small.{w} (ModCat.{w} C) (G ⟶ M)
    have := (isSeparator_iff_epi G).1 hsep F
    exact ⟨{ p := ∐ fun _ : G ⟶ F ↦ G, f := Sigma.desc fun f : G ⟶ F ↦ f }⟩

end TauCeti.ModCat
