/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Restrict
public import TauCeti.Geometry.RingedSpace.LocallyRingedSpace.GlueMorphisms

/-!
# Gluing morphisms of formal schemes along an open cover

Given an open cover `⨆ i, U i = ⊤` of a formal scheme `X` and compatible morphisms
`f i : X.restrict (U i) ⟶ Y`, `TauCeti.FormalScheme.glueMorphisms` glues them into a unique
morphism `X ⟶ Y` (`existsUnique_glueMorphisms`; EGA I, Ch. I, 10.4.6), lifting
`AlgebraicGeometry.LocallyRingedSpace.glueMorphisms`.
-/

public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u w

namespace TauCeti.FormalScheme

variable {X Y : FormalScheme.{u}} {ι : Type w} (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
include hU

/-- Morphisms of formal schemes agreeing on every member of an open cover of the source coincide. -/
theorem hom_ext_of_ofRestrict {g g' : X ⟶ Y}
    (h : ∀ i, X.ofRestrict (U i) ≫ g = X.ofRestrict (U i) ≫ g') : g = g' :=
  fullyFaithfulForgetToLocallyRingedSpace.map_injective <|
    LocallyRingedSpace.hom_ext_of_ofRestrict U hU fun i ↦ by
      have hi := congrArg forgetToLocallyRingedSpace.map (h i)
      simp only [Functor.map_comp, forgetToLocallyRingedSpace_map_ofRestrict] at hi
      exact hi

variable (f : ∀ i, X.restrict (U i) ⟶ Y)
  (hf : ∀ i j, X.restrictHomOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
    X.restrictHomOfLE inf_le_right ≫ f j)
include hf

omit hU in
/-- Transporting overlap compatibility of restricted formal-scheme morphisms to
`LocallyRingedSpace` via `forgetToLocallyRingedSpace`. -/
theorem forgetToLocallyRingedSpace_map_glue_compat (i j : ι) :
    (forgetToLocallyRingedSpace.obj X).restrictHomOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫
        forgetToLocallyRingedSpace.map (f i) =
      (forgetToLocallyRingedSpace.obj X).restrictHomOfLE inf_le_right ≫
        forgetToLocallyRingedSpace.map (f j) := by
  have h := congrArg forgetToLocallyRingedSpace.map (hf i j)
  rw [Functor.map_comp, Functor.map_comp, forgetToLocallyRingedSpace_map_restrictHomOfLE,
    forgetToLocallyRingedSpace_map_restrictHomOfLE] at h
  exact h

/-- **Gluing morphisms of formal schemes along an open cover** (EGA I, Ch. I, 10.4.6). -/
noncomputable def glueMorphisms : X ⟶ Y :=
  InducedCategory.homMk <| LocallyRingedSpace.glueMorphisms U hU
    (fun i ↦ forgetToLocallyRingedSpace.map (f i))
    (forgetToLocallyRingedSpace_map_glue_compat U f hf)

/-- Forgetting the formal-scheme structure of `glueMorphisms` recovers locally ringed-space
gluing. -/
@[simp]
theorem forgetToLocallyRingedSpace_map_glueMorphisms :
    forgetToLocallyRingedSpace.map (glueMorphisms U hU f hf) =
      LocallyRingedSpace.glueMorphisms U hU (fun i ↦ forgetToLocallyRingedSpace.map (f i))
        (forgetToLocallyRingedSpace_map_glue_compat U f hf) := (rfl)

/-- Restricting the glued morphism to `U i` recovers `f i`. -/
@[reassoc (attr := simp)]
theorem ofRestrict_glueMorphisms (i : ι) :
    X.ofRestrict (U i) ≫ glueMorphisms U hU f hf = f i :=
  fullyFaithfulForgetToLocallyRingedSpace.map_injective <| by
    simp only [Functor.map_comp, forgetToLocallyRingedSpace_map_ofRestrict,
      forgetToLocallyRingedSpace_map_glueMorphisms]
    exact LocallyRingedSpace.ofRestrict_glueMorphisms U hU _ _ i

/-- Universal property of open-cover morphism gluing for formal schemes. -/
theorem existsUnique_glueMorphisms : ∃! g : X ⟶ Y, ∀ i, X.ofRestrict (U i) ≫ g = f i :=
  ⟨glueMorphisms U hU f hf, ofRestrict_glueMorphisms U hU f hf, fun _ hg ↦
    hom_ext_of_ofRestrict U hU fun i ↦ (hg i).trans (ofRestrict_glueMorphisms U hU f hf i).symm⟩

end TauCeti.FormalScheme
