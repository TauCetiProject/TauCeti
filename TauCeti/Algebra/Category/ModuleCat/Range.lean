/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Ranges of morphisms of modules followed by an isomorphism

Following a morphism of modules `f : L ⟶ M` by an isomorphism `e : M ≅ N` transports its range
along `e`: an element `x` of `N` lies in the range of `f ≫ e.hom` exactly when `e.inv x` lies in
the range of `f` (`ModuleCat.mem_range_comp_iso_hom`).
-/

public section

open CategoryTheory

namespace ModuleCat

variable {R : Type*} [Ring R] {L M N : ModuleCat R}

/-- An element `x` lies in the range of a morphism followed by an isomorphism `e` exactly when
`e.inv x` lies in the range of the morphism. -/
theorem mem_range_comp_iso_hom (f : L ⟶ M) (e : M ≅ N) (x : N) :
    x ∈ LinearMap.range (f ≫ e.hom).hom ↔ e.inv.hom x ∈ LinearMap.range f.hom := by
  rw [hom_comp, LinearMap.range_comp]
  exact Submodule.mem_map_equiv (p := LinearMap.range f.hom) (e := e.toLinearEquiv)

end ModuleCat
