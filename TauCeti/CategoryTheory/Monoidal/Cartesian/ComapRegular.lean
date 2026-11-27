/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Cartesian.Action
public import TauCeti.CategoryTheory.Monoidal.Mod.Algebra

/-!
# Orbit morphisms of a monoid acting through a homomorphism

Let `f : G ⟶ H` be a morphism of monoid objects in a cartesian monoidal category. Through `f`,
the monoid `G` acts on `H` by left multiplication (`CategoryTheory.Mod.comapRegular f`). The orbit
morphism of the unit point of `H` for this action is `f` itself
(`TauCeti.orbitMap_one_comapRegular`).

For group schemes this identifies a homomorphism with an orbit morphism, so that the theory of
orbits and translations applies to it.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

namespace TauCeti

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {G H : C} [MonObj G]
  [MonObj H]

/-- For the action of `G` on `H` by left multiplication through `f` (`Mod.comapRegular f`), the
orbit morphism of the unit point is `f`. -/
theorem orbitMap_one_comapRegular (f : G ⟶ H) [IsMonHom f] :
    letI : ModObj G H := (Mod.comapRegular f).mod
    orbitMap G (1 : 𝟙_ C ⟶ H) = f := by
  let : ModObj G H := (Mod.comapRegular f).mod
  -- Evaluate the orbit morphism on the generic point `𝟙 G`, where `comp_orbitMap` applies.
  calc orbitMap G 1 = 𝟙 G ≫ orbitMap G 1 := (Category.id_comp _).symm
    _ = f := by simp [Hom.smul_def, ← Hom.mul_def]

end TauCeti
