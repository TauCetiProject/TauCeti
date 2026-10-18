/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Groupoid

/-!
# Functors on a groupoid with a weakly initial object

Let `C` be a groupoid and `x₀ : C` an object which admits a morphism to every object. Restricting
functors `F G : C ⥤ D` to `x₀` produces objects of `D` with actions of the vertex group
`End x₀`. This file proves that a morphism `F.obj x₀ ⟶ G.obj x₀` commuting with these actions
extends uniquely to a natural transformation `F ⟶ G` with the given morphism as its component at
`x₀`, and likewise for isomorphisms.

The construction is the usual transport of structure. Choosing a morphism `γ x : x₀ ⟶ x` for
every object, the component at `x` is `F.map (γ x)⁻¹ ≫ φ ≫ G.map (γ x)`; naturality at
`f : x ⟶ y` holds because the discrepancy `γ x ≫ f ≫ (γ y)⁻¹` between the two chosen morphisms
is an endomorphism of `x₀`, so equivariance applies to it. Nothing depends on the choice, since
the resulting natural transformation is determined by its component at `x₀`, and that component
is `φ` whatever `γ x₀` is.

The hypothesis is exactly connectedness of the groupoid when `C` is nonempty, but is stated as
the family of nonemptiness assertions `∀ x, Nonempty (x₀ ⟶ x)` rather than through
`CategoryTheory.IsConnected`: the intended source of that data is a path-connected topological
space, whose fundamental groupoid comes with paths from a chosen basepoint, and the equivalence
of the two formulations is not needed.

## Main declarations

* `TauCeti.Groupoid.natTrans_ext`: a natural transformation is determined by its component at the
  weakly initial object.
* `TauCeti.Groupoid.natTransOfEnd`: an equivariant morphism of the values at a weakly initial
  object of a groupoid extends to a natural transformation.
* `TauCeti.Groupoid.natTransOfEnd_app_self`: the extension restricts to the given morphism.
* `TauCeti.Groupoid.eq_natTransOfEnd`: the extension is the only natural transformation doing so.
* `TauCeti.Groupoid.natIsoOfEnd`: an equivariant isomorphism of the values at a weakly initial
  object of a groupoid extends to a natural isomorphism.
* `TauCeti.Groupoid.natIsoOfEnd_app_self`: the extension restricts to the given isomorphism.
* `TauCeti.Groupoid.eq_natIsoOfEnd`: the extension is the only natural isomorphism doing so.
-/

public section
noncomputable section

universe t w v u

open CategoryTheory

namespace TauCeti.Groupoid

variable {C : Type u} [CategoryTheory.Groupoid.{v} C] {D : Type w} [Category.{t} D]
  {F G : C ⥤ D} {x₀ : C} (hconn : ∀ x : C, Nonempty (x₀ ⟶ x))

include hconn in
/-- A natural transformation between functors out of a groupoid is determined by its component at
a weakly initial object. -/
theorem natTrans_ext {α β : F ⟶ G} (h : α.app x₀ = β.app x₀) : α = β := by
  ext x
  obtain ⟨f⟩ := hconn x
  rw [← cancel_epi (F.map f), α.naturality f, β.naturality f, h]

include hconn in
/-- A natural isomorphism between functors out of a groupoid is determined by its component at
a weakly initial object. -/
theorem natIso_ext {α β : F ≅ G} (h : α.app x₀ = β.app x₀) : α = β :=
  Iso.ext (natTrans_ext hconn (by simpa using congrArg Iso.hom h))

/-- A chosen isomorphism from the weakly initial object `x₀` to an arbitrary object. -/
private def chosenIso (x : C) : x₀ ≅ x :=
  (CategoryTheory.Groupoid.isoEquivHom x₀ x).symm (hconn x).some

/-- An `End x₀`-equivariant morphism between the values of two functors at a weakly initial
object of a groupoid extends to a natural transformation.

Its component at `x₀` is the given morphism, by `natTransOfEnd_app_self`. -/
def natTransOfEnd (φ : F.obj x₀ ⟶ G.obj x₀)
    (hφ : ∀ g : x₀ ⟶ x₀, F.map g ≫ φ = φ ≫ G.map g) : F ⟶ G where
  app x := F.map (chosenIso hconn x).inv ≫ φ ≫ G.map (chosenIso hconn x).hom
  naturality {x y} f := by
    -- Cancel the chosen transports, then apply equivariance to their discrepancy.
    rw [← cancel_epi (F.map (chosenIso hconn x).hom),
      ← cancel_mono (G.map (chosenIso hconn y).inv)]
    simp only [Category.assoc, ← F.map_comp_assoc, ← G.map_comp, Iso.hom_inv_id, F.map_id,
      G.map_id, Category.id_comp, Category.comp_id]
    exact hφ _

private theorem natTransOfEnd_app (φ : F.obj x₀ ⟶ G.obj x₀)
    (hφ : ∀ g : x₀ ⟶ x₀, F.map g ≫ φ = φ ≫ G.map g) (x : C) :
    (natTransOfEnd hconn φ hφ).app x =
      F.map (chosenIso hconn x).inv ≫ φ ≫ G.map (chosenIso hconn x).hom :=
  rfl

/-- The extension of an equivariant morphism restricts to that morphism. -/
@[simp]
theorem natTransOfEnd_app_self (φ : F.obj x₀ ⟶ G.obj x₀)
    (hφ : ∀ g : x₀ ⟶ x₀, F.map g ≫ φ = φ ≫ G.map g) :
    (natTransOfEnd hconn φ hφ).app x₀ = φ := by
  rw [natTransOfEnd_app, ← hφ (chosenIso hconn x₀).hom, ← Category.assoc, ← F.map_comp,
    Iso.inv_hom_id, F.map_id, Category.id_comp]

/-- The extension is the only natural transformation restricting to the given morphism at the
weakly initial object. -/
theorem eq_natTransOfEnd (φ : F.obj x₀ ⟶ G.obj x₀)
    (hφ : ∀ g : x₀ ⟶ x₀, F.map g ≫ φ = φ ≫ G.map g) (α : F ⟶ G) (hα : α.app x₀ = φ) :
    α = natTransOfEnd hconn φ hφ :=
  natTrans_ext hconn (by rw [hα, natTransOfEnd_app_self])

/-- An `End x₀`-equivariant isomorphism between the values of two functors at a
weakly initial object of a groupoid extends to a natural isomorphism.

Its component at `x₀` is the given isomorphism, by `natIsoOfEnd_app_self`. -/
def natIsoOfEnd (e : F.obj x₀ ≅ G.obj x₀)
    (he : ∀ g : x₀ ⟶ x₀, F.map g ≫ e.hom = e.hom ≫ G.map g) :
    F ≅ G where
  hom := natTransOfEnd hconn e.hom he
  inv := natTransOfEnd hconn e.inv fun g ↦ by
    rw [Iso.comp_inv_eq, Category.assoc, he, Iso.inv_hom_id_assoc]
  hom_inv_id := natTrans_ext hconn (by simp)
  inv_hom_id := natTrans_ext hconn (by simp)

/-- The extension of an equivariant isomorphism restricts to that isomorphism. -/
@[simp]
theorem natIsoOfEnd_app_self (e : F.obj x₀ ≅ G.obj x₀)
    (he : ∀ g : x₀ ⟶ x₀, F.map g ≫ e.hom = e.hom ≫ G.map g) :
    (natIsoOfEnd hconn e he).app x₀ = e :=
  Iso.ext (natTransOfEnd_app_self hconn e.hom he)

/-- The extension is the only natural isomorphism restricting to the given one at the weakly
initial object. -/
theorem eq_natIsoOfEnd (e : F.obj x₀ ≅ G.obj x₀)
    (he : ∀ g : x₀ ⟶ x₀, F.map g ≫ e.hom = e.hom ≫ G.map g) (α : F ≅ G) (hα : α.app x₀ = e) :
    α = natIsoOfEnd hconn e he :=
  natIso_ext hconn (by rw [hα, natIsoOfEnd_app_self])

end TauCeti.Groupoid
