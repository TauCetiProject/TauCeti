/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCommRingCat

/-!
# Forgetting topology on topological commutative rings

The forgetful functor to `CommRingCat` sends a continuous ring homomorphism to its underlying
ring homomorphism. The transport lemma records this also when the source and target have been
identified by equalities.
-/

public section

namespace TauCeti.TopCommRingCat

open CategoryTheory

/-- Forgetting the topology of a morphism keeps its underlying ring homomorphism. -/
@[simp]
theorem forget₂_map {X Y : _root_.TopCommRingCat} (g : X →+* Y) (hg : Continuous g) :
    (forget₂ _root_.TopCommRingCat CommRingCat).map (⟨g, hg⟩ : X ⟶ Y) =
      CommRingCat.ofHom g := rfl

/-- Forgetting topology commutes with equality transports at both endpoints. -/
theorem forget₂_map_eqToHom_comp_comp_eqToHom {X X' Y Y' : _root_.TopCommRingCat}
    (eX : X = X') (g : X' →+* Y') (hg : Continuous g) (eY : Y = Y') :
    (forget₂ _root_.TopCommRingCat CommRingCat).map
        (eqToHom eX ≫ (⟨g, hg⟩ : X' ⟶ Y') ≫ eqToHom eY.symm) ≫
        (forget₂ _root_.TopCommRingCat CommRingCat).map (eqToHom eY) =
      (forget₂ _root_.TopCommRingCat CommRingCat).map (eqToHom eX) ≫
        CommRingCat.ofHom g := by
  subst eX eY
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, CategoryTheory.Functor.map_id,
    forget₂_map]
  -- The forgetful image of `X` is `CommRingCat.of X.α` only after unfolding `forget₂`, so the
  -- identity laws are applied by `exact`, which unifies the objects at default transparency.
  exact (Category.comp_id _).trans (Category.id_comp _).symm

end TauCeti.TopCommRingCat

end
