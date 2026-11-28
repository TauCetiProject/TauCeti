/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Module morphisms as semimodule morphisms

The standard equivalence retains the underlying linear map in the forward direction.
-/

public section

open CategoryTheory

namespace ModuleCat

universe u v

/-- The forward module-to-semimodule functor retains the underlying linear map. -/
@[simp]
theorem equivalenceSemimoduleCat_map_hom {R : Type u} [Ring R] {M N : ModuleCat.{v} R}
    (f : M ⟶ N) : (equivalenceSemimoduleCat.functor.map f).hom = f.hom := (rfl)

end ModuleCat
