/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
-- supplies the `HasColimit` instance through which the colimit is reflected along `forget`
import Mathlib.Algebra.Category.Grp.Colimits

/-!
# Recognising filtered colimits of additive commutative groups

A cocone on a filtered diagram of additive commutative groups is colimiting as soon as its legs
are jointly surjective and any two elements with the same image in the apex already have a common
image somewhere deeper in the diagram.

## Main declarations

* `TauCeti.AddCommGrpCat.isColimitOfJointlySurjective`: that recognition criterion.

## Implementation notes

The forgetful functor of `AddCommGrpCat` preserves filtered colimits and reflects isomorphisms,
so it reflects them as well; the criterion is therefore
`CategoryTheory.Limits.Types.FilteredColimit.isColimitOf` transported along it. Joint
surjectivity applied to `0` supplies the object making the index category nonempty, so only
`IsFilteredOrEmpty` need be assumed.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AddCommGrpCat

variable {J : Type u} [Category.{w} J] [IsFilteredOrEmpty J] [UnivLE.{u, v}] [UnivLE.{w, v}]
  {F : J ⥤ _root_.AddCommGrpCat.{v}}

/-- A cocone on a filtered diagram of additive commutative groups is colimiting as soon as its
legs are jointly surjective and any two elements with the same image in the apex have a common
image somewhere deeper in the diagram. -/
noncomputable def isColimitOfJointlySurjective (t : Cocone F)
    (hsurj : ∀ x : t.pt, ∃ (j : J) (y : F.obj j), (t.ι.app j).hom y = x)
    (hinj : ∀ (i j : J) (xi : F.obj i) (xj : F.obj j),
      (t.ι.app i).hom xi = (t.ι.app j).hom xj →
        ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k), (F.map f).hom xi = (F.map g).hom xj) :
    IsColimit t := by
  -- The apex has a zero element, so joint surjectivity exhibits an object of `J`.
  have : Nonempty J := ⟨(hsurj 0).choose⟩
  have : IsFiltered J := ⟨⟩
  have : PreservesFilteredColimitsOfSize.{w, u} (forget _root_.AddCommGrpCat.{v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{v, v, w, u} _
  have : ReflectsColimit F (forget _root_.AddCommGrpCat.{v}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  exact isColimitOfReflects (forget _root_.AddCommGrpCat.{v})
    (Types.FilteredColimit.isColimitOf _ _
      (fun x => by obtain ⟨j, y, hy⟩ := hsurj x; exact ⟨j, y, hy.symm⟩) hinj)

end AddCommGrpCat

end TauCeti
