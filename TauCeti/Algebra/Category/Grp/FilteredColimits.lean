/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Recognising colimits of additive commutative groups

A cocone on a diagram of additive commutative groups is colimiting as soon as its legs
are jointly surjective and any two elements with the same image in the apex already have a common
image somewhere deeper in the diagram.

## Main declarations

* `TauCeti.AddCommGrpCat.isColimitOfJointlySurjective`: that recognition criterion.

## Implementation notes

We use `CategoryTheory.Limits.Types.FilteredColimit.isColimitOf` to construct the underlying
universal map, then prove it is additive. The equality condition applied to zero elements supplies
a common target for any two stages, so no filteredness assumption is needed. There are no universe
bounds on the index category relative to the groups. In particular, this criterion applies to
filtered diagrams without requiring a chosen colimit in the category of groups.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AddCommGrpCat

variable {J : Type u} [Category.{w} J]
  {F : J ⥤ _root_.AddCommGrpCat.{v}}

/-- A cocone on a diagram of additive commutative groups is colimiting as soon as its
legs are jointly surjective and any two elements with the same image in the apex have a common
image somewhere deeper in the diagram. -/
noncomputable def isColimitOfJointlySurjective (t : Cocone F)
    (hsurj : ∀ x : t.pt, ∃ (j : J) (y : F.obj j), (t.ι.app j).hom y = x)
    (hinj : ∀ (i j : J) (xi : F.obj i) (xj : F.obj j),
      (t.ι.app i).hom xi = (t.ι.app j).hom xj →
        ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k), (F.map f).hom xi = (F.map g).hom xj) :
    IsColimit t := by
  let Φ := forget _root_.AddCommGrpCat.{v}
  let hc : IsColimit (Φ.mapCocone t) := Types.FilteredColimit.isColimitOf _ _
    (fun x => by obtain ⟨j, y, hy⟩ := hsurj x; exact ⟨j, y, hy.symm⟩) hinj
  have hfac (s : Cocone F) (j : J) (y : F.obj j) :
      hc.desc (Φ.mapCocone s) ((t.ι.app j).hom y) = (s.ι.app j).hom y :=
    ConcreteCategory.congr_hom (hc.fac (Φ.mapCocone s) j) y
  exact
    { desc s := _root_.AddCommGrpCat.ofHom
        { toFun := hc.desc (Φ.mapCocone s)
          map_zero' := by
            obtain ⟨j, _, _⟩ := hsurj 0
            simpa using hfac s j 0
          map_add' x y := by
            obtain ⟨i, xi, rfl⟩ := hsurj x
            obtain ⟨j, xj, rfl⟩ := hsurj y
            -- Applying the equality condition to zero gives a common stage, without filteredness.
            obtain ⟨k, f, g, _⟩ := hinj i j 0 0 (by simp)
            have hf := ConcreteCategory.congr_hom (t.w f) xi
            have hg := ConcreteCategory.congr_hom (t.w g) xj
            simp only [_root_.AddCommGrpCat.comp_apply] at hf hg
            rw [← hf, ← hg, ← map_add, hfac, map_add, hfac, hfac] }
      fac s j := by
        ext y
        exact hfac s j y
      uniq s m hm := by
        ext x
        obtain ⟨j, y, rfl⟩ := hsurj x
        exact (ConcreteCategory.congr_hom (hm j) y).trans (hfac s j y).symm }

end AddCommGrpCat

end TauCeti
