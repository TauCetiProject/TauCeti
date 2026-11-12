/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import TauCeti.Algebra.Category.Grp.FilteredColimits

/-!
# Filtered colimits of modules with independent universe levels

The native filtered-colimit cocone allows the module universe to be larger than the ring
universe. This file exports preservation by the forgetful functor for that universe combination.

It also records a recognition criterion with no universe constraints at all: a cocone of modules
is colimiting as soon as its legs are jointly surjective and any two elements with the same image
in the apex already have a common image somewhere deeper in the diagram
(`TauCeti.ModuleCat.isColimitOfJointlySurjective`). Mathlib's reflection of filtered colimits by
the forgetful functor needs the modules to live in the universe of the ring; the criterion does
not, which is the situation of modules of chains with local coefficients, whose universe is that
of the space rather than that of the ring.
-/

public noncomputable section

open CategoryTheory Limits

namespace ModuleCat

universe u v

/-- Forgetting modules preserves filtered colimits also when the module universe is larger
than the ring universe. -/
instance forget_preservesFilteredColimits_max (R : Type v) [Ring R] :
    PreservesFilteredColimits (CategoryTheory.forget (ModuleCat.{max u v} R)) where
  preserves_filtered_colimits J _ _ := by
    let : PreservesColimitsOfShape J
        (CategoryTheory.forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}) :=
      { preservesColimit := fun {F} ↦
          preservesColimit_of_preserves_colimit_cocone
            (ModuleCat.FilteredColimits.colimitCoconeIsColimit F)
            (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit
              (F ⋙ CategoryTheory.forget₂ (ModuleCat.{max u v} R)
                AddCommGrpCat.{max u v})) }
    exact Limits.comp_preservesColimitsOfShape
      (CategoryTheory.forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
      (CategoryTheory.forget AddCommGrpCat.{max u v})

end ModuleCat

namespace TauCeti.ModuleCat

universe u v w

variable {R : Type*} [Ring R] {J : Type u} [Category.{w} J] {F : J ⥤ _root_.ModuleCat.{v} R}

/-- A cocone on a diagram of modules is colimiting as soon as its legs are jointly surjective and
any two elements with the same image in the apex have a common image somewhere deeper in the
diagram. There are no universe bounds on the index category, the ring or the modules. -/
def isColimitOfJointlySurjective (t : Cocone F)
    (hsurj : ∀ x : t.pt, ∃ (j : J) (y : F.obj j), (t.ι.app j).hom y = x)
    (hinj : ∀ (i j : J) (xi : F.obj i) (xj : F.obj j),
      (t.ι.app i).hom xi = (t.ι.app j).hom xj →
        ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k), (F.map f).hom xi = (F.map g).hom xj) :
    IsColimit t := by
  let Φ := forget₂ (_root_.ModuleCat.{v} R) _root_.AddCommGrpCat.{v}
  let hc : IsColimit (Φ.mapCocone t) :=
    AddCommGrpCat.isColimitOfJointlySurjective (Φ.mapCocone t) hsurj hinj
  -- the descended additive map, which agrees with the legs of `s` on the legs of `t`
  have hfac (s : Cocone F) (j : J) (y : F.obj j) :
      (hc.desc (Φ.mapCocone s)).hom ((t.ι.app j).hom y) = (s.ι.app j).hom y :=
    ConcreteCategory.congr_hom (hc.fac (Φ.mapCocone s) j) y
  exact
    { desc s := _root_.ModuleCat.ofHom
        { toFun := (hc.desc (Φ.mapCocone s)).hom
          map_add' := map_add _
          -- every element of the apex comes from a stage, where the legs are linear
          map_smul' r x := by
            obtain ⟨j, y, rfl⟩ := hsurj x
            rw [← map_smul, hfac, hfac, map_smul]
            rfl }
      fac s j := by
        ext y
        exact hfac s j y
      uniq s m hm := by
        ext x
        obtain ⟨j, y, rfl⟩ := hsurj x
        exact (ConcreteCategory.congr_hom (hm j) y).trans (hfac s j y).symm }

end TauCeti.ModuleCat
