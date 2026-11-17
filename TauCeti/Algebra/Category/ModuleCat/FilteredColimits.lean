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

The forgetful functor from `ModuleCat.{u} R` to types preserves filtered colimits regardless of
the universe of the ring `R` (`ModuleCat.forget_preservesFilteredColimits`).

It also records a recognition criterion with no universe constraints at all: a cocone of modules
is colimiting as soon as its legs are jointly surjective and any two elements with the same image
in the apex already have a common image somewhere deeper in the diagram
(`TauCeti.ModuleCat.isColimitOfJointlySurjective`). It is the criterion for abelian groups,
`TauCeti.AddCommGrpCat.isColimitOfJointlySurjective`, reflected along the forgetful functor to
`AddCommGrpCat`, which reflects colimits whatever the universes of the ring and the modules. This
covers modules of chains with local coefficients, whose universe is that of the space rather than
that of the ring.
-/

public noncomputable section

open CategoryTheory Limits

namespace ModuleCat

universe u v

/-- Forgetting modules preserves filtered colimits regardless of the universe of the ring. -/
instance forget_preservesFilteredColimits {R : Type v} [Ring R] :
    PreservesFilteredColimits (CategoryTheory.forget (ModuleCat.{u} R)) :=
  haveI : PreservesColimitsOfSize.{u, u}
      (CategoryTheory.forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) :=
    ⟨fun {J} _ ↦ ModuleCat.forget₂PreservesColimitsOfShape R J⟩
  Limits.comp_preservesFilteredColimits
    (CategoryTheory.forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
    (CategoryTheory.forget AddCommGrpCat.{u})

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
  have : HasColimit (F ⋙ Φ) := ⟨⟨_, hc⟩⟩
  exact isColimitOfReflects Φ hc

end TauCeti.ModuleCat
