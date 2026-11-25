/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# Exterior powers of finite projective modules

The exterior powers `⋀ⁿ M` of a finite projective module `M` are finite projective, so they are
objects `FiniteProjectiveModules.exteriorPower M n` of the full subcategory of `ModuleCat R` on
finite projective modules, next to the duals `FiniteProjectiveModules.dual`.
-/

public section

open CategoryTheory

namespace TauCeti.FiniteProjectiveModules

universe u

variable {R : Type u} [CommRing R]

/-- The `n`-th exterior power of a finite projective module, as a finite projective module. -/
@[expose]
def exteriorPower (M : (finiteProjectiveModules R).FullSubcategory) (n : ℕ) :
    (finiteProjectiveModules R).FullSubcategory :=
  ⟨M.obj.exteriorPower n, finiteProjectiveModules_iff.mpr
    ⟨inferInstanceAs (Module.Finite R (⋀[R]^n M.obj)),
      inferInstanceAs (Module.Projective R (⋀[R]^n M.obj))⟩⟩

/-- The underlying module of `FiniteProjectiveModules.exteriorPower M n` is `⋀ⁿ M`. -/
@[simp]
theorem exteriorPower_obj (M : (finiteProjectiveModules R).FullSubcategory) (n : ℕ) :
    (exteriorPower M n).obj = M.obj.exteriorPower n :=
  (rfl)

end TauCeti.FiniteProjectiveModules
