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

The forgetful functor from `ModuleCat.{u} R` to `Type u` preserves filtered colimits with no
constraint between the ring universe `v` and the module universe `u`
(`ModuleCat.forget_preservesFilteredColimits`), factoring through `AddCommGrpCat.{u}`.

It also records a recognition criterion with no universe constraints at all: a cocone of modules
is colimiting as soon as its legs are jointly surjective and any two elements with the same image
in the apex already have a common image somewhere deeper in the diagram
(`TauCeti.ModuleCat.isColimitOfJointlySurjective`). It is the criterion for abelian groups,
`TauCeti.AddCommGrpCat.isColimitOfJointlySurjective`, reflected along the forgetful functor to
`AddCommGrpCat`, which reflects colimits whatever the universes of the ring and the modules. This
covers modules of chains with local coefficients, whose universe is that of the space rather than
that of the ring. Over a directed order, injectivity only needs checking on elements mapped to zero
in the apex (`TauCeti.ModuleCat.isColimitOfJointlySurjectiveOfMapEqZero`).
-/

public noncomputable section

open CategoryTheory Limits

namespace ModuleCat

universe u v

/-- Forgetting modules preserves filtered colimits with no constraint between the ring universe
and the module universe. -/
instance forget_preservesFilteredColimits (R : Type v) [Ring R] :
    PreservesFilteredColimits (CategoryTheory.forget (ModuleCat.{u} R)) where
  preserves_filtered_colimits _ _ _ :=
    Limits.comp_preservesColimitsOfShape
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

/-- A cocone on a diagram of modules indexed by a directed order is colimiting as soon as its legs
are jointly surjective and every element mapped to zero in the apex is already mapped to zero
somewhere further along the diagram. -/
def isColimitOfJointlySurjectiveOfMapEqZero {ι : Type u} [Preorder ι] [IsDirectedOrder ι]
    {F : ι ⥤ _root_.ModuleCat.{v} R} (t : Cocone F)
    (hsurj : ∀ x : t.pt, ∃ (j : ι) (y : F.obj j), (t.ι.app j).hom y = x)
    (hzero : ∀ (i : ι) (x : F.obj i), (t.ι.app i).hom x = 0 →
      ∃ (j : ι) (hij : i ≤ j), (F.map (homOfLE hij)).hom x = 0) :
    IsColimit t :=
  isColimitOfJointlySurjective t hsurj fun i j xi xj hij ↦ by
    obtain ⟨l, hil, hjl⟩ := exists_ge_ge i j
    -- the difference of the two images at a common upper bound vanishes in the apex
    obtain ⟨m, hlm, hm⟩ := hzero l ((F.map (homOfLE hil)).hom xi - (F.map (homOfLE hjl)).hom xj)
      (by rwa [map_sub, sub_eq_zero, ← ConcreteCategory.comp_apply, Cocone.w,
        ← ConcreteCategory.comp_apply, Cocone.w])
    refine ⟨m, homOfLE (hil.trans hlm), homOfLE (hjl.trans hlm), ?_⟩
    rwa [map_sub, sub_eq_zero, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← F.map_comp, ← F.map_comp] at hm

end TauCeti.ModuleCat
