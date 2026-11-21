/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Quotient
public import TauCeti.CategoryTheory.NatIso

/-!
# Universal descent criteria for quotient categories

Exact `↔` characterizations of when a functor `G : C ⥤ D` factors through Mathlib's quotient
functor `CategoryTheory.Quotient.functor r`, either strictly (`functor r ⋙ F = G`) or up to a
natural isomorphism (`functor r ⋙ F ≅ G`).

## Main results

* `CategoryTheory.Quotient.exists_lift_iff`: strict factorization through `Quotient.functor r`
  holds if and only if `G` identifies every pair of morphisms related by `r`.
* `CategoryTheory.Quotient.exists_iso_lift_iff`: factorization through `Quotient.functor r` up to
  natural isomorphism holds under the exact same condition.
-/

public section

universe v u v' u'

namespace CategoryTheory.Quotient

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- A functor `G : C ⥤ D` factors strictly through `CategoryTheory.Quotient.functor r` if and only
if it identifies every pair of morphisms related by `r`. -/
theorem exists_lift_iff (r : HomRel C) (G : C ⥤ D) :
    (∃ F : Quotient r ⥤ D, functor r ⋙ F = G) ↔
      ∀ ⦃X Y : C⦄ ⦃f g : X ⟶ Y⦄, r f g → G.map f = G.map g where
  mp := fun ⟨F, hF⟩ _ _ _ _ hfg ↦ by
    rw [← hF, Functor.comp_map, Functor.comp_map, Quotient.sound r hfg]
  mpr hG := ⟨lift r G hG, lift_spec r G hG⟩

/-- A functor `G : C ⥤ D` factors through `CategoryTheory.Quotient.functor r` up to a natural
isomorphism if and only if it identifies every pair of morphisms related by `r`. -/
theorem exists_iso_lift_iff (r : HomRel C) (G : C ⥤ D) :
    (∃ F : Quotient r ⥤ D, Nonempty (functor r ⋙ F ≅ G)) ↔
      ∀ ⦃X Y : C⦄ ⦃f g : X ⟶ Y⦄, r f g → G.map f = G.map g where
  mp := fun ⟨F, ⟨e⟩⟩ _ _ _ _ hfg ↦
    (NatIso.map_eq_iff e).mp (congrArg F.map (Quotient.sound r hfg))
  mpr hG := ⟨lift r G hG, ⟨lift.isLift r G hG⟩⟩

end CategoryTheory.Quotient
