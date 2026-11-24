/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Category.AlgCat.Basic
public import TauCeti.Algebra.Category.ModuleCat.Basic

/-!
# Forgetting algebra structure

The standard composite functor from algebras to semimodules retains the underlying map.
-/

public section

open CategoryTheory

namespace AlgCat

universe u t

/-- The forgetful composite to semimodules acts by the original algebra homomorphism. -/
theorem forgetToSemimodule_map_apply {R : Type u} [CommRing R] {A B : AlgCat.{t} R}
    (f : A ⟶ B) (x : A) :
    (((forget₂ (AlgCat R) (ModuleCat R) ⋙ ModuleCat.equivalenceSemimoduleCat.functor).map f).hom
      x) = f.hom x := by
  rw [Functor.comp_map, AlgCat.forget₂_module_map, ModuleCat.equivalenceSemimoduleCat_map_hom,
    ModuleCat.hom_ofHom]
  exact AlgHom.toLinearMap_apply f.hom x

end AlgCat
