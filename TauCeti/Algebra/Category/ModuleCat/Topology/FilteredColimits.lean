/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
public import TauCeti.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Recognising colimits of topological modules with discrete apex

A cocone on a diagram of topological modules whose apex is **discrete** is colimiting as
soon as its legs are jointly surjective and any two elements with the same image in the apex
already have a common image somewhere deeper in the diagram.

Discreteness of the apex is what makes this a purely algebraic criterion. The colimit that Mathlib
constructs in `TopModuleCat R` (`TopModuleCat.isColimit`) carries the finest topology making the
legs continuous and the module operations continuous; a cocone with the right underlying module but
a coarser topology on its apex is not colimiting. A discrete apex rules that out, since every map
out of a discrete space is continuous. This is the situation of the finite-quotient description of
continuous cohomology, whose apex is the discrete continuous cohomology of a compact group.

## Main declarations

* `TauCeti.TopModuleCat.isColimitOfJointlySurjective`: that recognition criterion.

## Implementation notes

The criterion is `TauCeti.ModuleCat.isColimitOfJointlySurjective` read through the forgetful
functor to `ModuleCat R`. The descended linear map is continuous because the apex is discrete. No
filteredness or universe bounds on the index category are needed.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace TopModuleCat

variable {R : Type*} [Ring R] [TopologicalSpace R]
  {J : Type u} [Category.{w} J]
  {F : J ⥤ _root_.TopModuleCat.{v} R}

/-- A cocone on a diagram of topological modules whose apex is discrete is colimiting as
soon as its legs are jointly surjective and any two elements with the same image in the apex have a
common image somewhere deeper in the diagram. -/
noncomputable def isColimitOfJointlySurjective (t : Cocone F) [DiscreteTopology t.pt]
    (hsurj : ∀ x : t.pt, ∃ (j : J) (y : F.obj j), (t.ι.app j).hom y = x)
    (hinj : ∀ (i j : J) (xi : F.obj i) (xj : F.obj j),
      (t.ι.app i).hom xi = (t.ι.app j).hom xj →
        ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k), (F.map f).hom xi = (F.map g).hom xj) :
    IsColimit t := by
  let Φ := forget₂ (_root_.TopModuleCat.{v} R) (_root_.ModuleCat.{v} R)
  let hc : IsColimit (Φ.mapCocone t) :=
    ModuleCat.isColimitOfJointlySurjective (Φ.mapCocone t) hsurj hinj
  exact
    { desc s := _root_.TopModuleCat.ofHom
        { toLinearMap := (hc.desc (Φ.mapCocone s)).hom
          cont := continuous_of_discreteTopology }
      fac s j := by
        ext y
        exact ConcreteCategory.congr_hom (hc.fac (Φ.mapCocone s) j) y
      uniq s m hm := by
        ext x
        refine ConcreteCategory.congr_hom (hc.uniq (Φ.mapCocone s) (Φ.map m) fun j ↦ ?_) x
        exact (Φ.map_comp _ _).symm.trans (congrArg Φ.map (hm j)) }

end TopModuleCat

end TauCeti
