/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Geometry.RingedSpace.Stalks
public import Mathlib.Topology.Sheaves.Functors
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pushforward.Basic

/-!
# Stalk maps of morphisms of ringed spaces

A morphism of ringed spaces `(f, φ) : (Y, 𝒪_Y) → (X, 𝒪_X)` is a continuous map `f : Y → X`
with a morphism of sheaves of rings `φ : 𝒪_X → f_* 𝒪_Y`. Following Mathlib's module pullback
`SheafOfModules.pullback φ` and pushforward `SheafOfModules.pushforward φ`, `φ` is a morphism from
`ringCatSheaf 𝒪_X` to the pushforward of `ringCatSheaf 𝒪_Y` along `Opens.map f`. This file
constructs the stalk map `𝒪_{X,f(y)} → 𝒪_{Y,y}` of `(f, φ)`, a morphism of commutative rings,
and computes it on germs; `TauCeti.SheafOfModules.stalkAlgebra` makes `𝒪_{Y,y}` an algebra over
`𝒪_{X,f(y)}` through it. Stalks of module pushforwards and pullbacks are compared along it.
-/

public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TauCeti

noncomputable section

namespace SheafOfModules

variable {X Y : TopCat.{u}} {𝒪X : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {𝒪Y : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}} {f : Y ⟶ X}
  (φ : ringCatSheaf 𝒪X ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf 𝒪Y))

/-- The stalk map `𝒪_{X,f(y)} → 𝒪_{Y,y}` of a morphism of ringed spaces `(f, φ)`: Mathlib's
stalk map `PresheafedSpace.Hom.stalkMap` of the morphism of presheafed spaces given by `f` and the
morphism of presheaves of commutative rings `commRingCatHom φ : 𝒪_X ⟶ f_* 𝒪_Y`. -/
def ringStalkMap (y : Y) :
    TopCat.Presheaf.stalk 𝒪X.obj (f y) ⟶ TopCat.Presheaf.stalk 𝒪Y.obj y :=
  AlgebraicGeometry.PresheafedSpace.Hom.stalkMap
    (X := ⟨Y, 𝒪Y.obj⟩) (Y := ⟨X, 𝒪X.obj⟩) ⟨f, (commRingCatHom φ :)⟩ y

/-- The stalk map of `(f, φ)` sends the germ of `r` at `f y` to the germ of `φ r` at `y`. -/
@[simp]
theorem ringStalkMap_germ (y : Y) (U : Opens X) (hy : f y ∈ U) (r : 𝒪X.obj.obj (op U)) :
    ringStalkMap φ y (TopCat.Presheaf.germ 𝒪X.obj U (f y) hy r) =
      TopCat.Presheaf.germ 𝒪Y.obj ((Opens.map f).obj U) y hy (φ.hom.app (op U) r) :=
  AlgebraicGeometry.PresheafedSpace.stalkMap_germ_apply
    (X := ⟨Y, 𝒪Y.obj⟩) (Y := ⟨X, 𝒪X.obj⟩) ⟨f, (commRingCatHom φ :)⟩ U y hy r

/-- The stalk `𝒪_{Y,y}` as an algebra over `𝒪_{X,f(y)}` through the stalk map of `(f, φ)`. It
is not an instance, since `φ` cannot be found by instance search; statements over it introduce
it with `letI`. -/
abbrev stalkAlgebra (y : Y) :
    Algebra ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) ↑(TopCat.Presheaf.stalk 𝒪Y.obj y) :=
  (ringStalkMap φ y).hom.toAlgebra

end SheafOfModules

end

end TauCeti
