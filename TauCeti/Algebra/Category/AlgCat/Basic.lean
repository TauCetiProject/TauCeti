/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Category.AlgCat.Basic

/-!
# Forgetting algebra structure

The standard composite functor from algebras to semimodules retains the underlying map.
-/

public section

open CategoryTheory

namespace AlgCat

universe u t

/-- The forgetful composite to semimodules acts by the original algebra homomorphism. -/
@[simp]
theorem forgetToSemimodule_map_apply {R : Type u} [CommRing R] {A B : AlgCat.{t} R}
    (f : A ⟶ B) (x : A) :
    (ModuleCat.equivalenceSemimoduleCat.functor.map
      (ModuleCat.ofHom f.hom.toLinearMap)).hom x = f.hom x := (rfl)

end AlgCat
