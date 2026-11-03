/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import TauCeti.Algebra.Category.ModuleCat.Finrank
public import TauCeti.CategoryTheory.GrothendieckGroup.Abelian

/-!
# Finrank as an additive invariant

This file packages finrank on finitely generated modules as an invariant additive on short exact
sequences. It is the reusable bridge from `FGModuleCat` to abelian Grothendieck groups.

The coefficient ring is a Noetherian ring satisfying the rank-nullity theorem
(`HasRankNullity`). Noetherianity makes `FGModuleCat R` abelian, and rank-nullity makes finrank
additive on short exact sequences of finitely generated modules, free or not. Both hold for
division rings and for Noetherian commutative domains such as `ℤ`, where finrank is the rank of
the free part of a finitely generated abelian group.

Additivity is read off from `CategoryTheory.ShortComplex.ShortExact.moduleCat_finrank_eq_add`,
which lives one category down, so the file first records how the forgetful functor
`forget₂ (FGModuleCat R) (ModuleCat R)` interacts with finrank. This is the only place where the
definitional identification of an `FGModuleCat` object with its underlying module is used;
everything else goes through it.
-/

public section

open CategoryTheory

universe u v

namespace FGModuleCat

variable {R : Type u} [Ring R]

/-- Forgetting the finite-generation witness does not change finrank. -/
@[simp]
theorem finrank_forget₂_obj (X : FGModuleCat.{v} R) :
    Module.finrank R ((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).obj X) =
      Module.finrank R X := (rfl)

end FGModuleCat

namespace TauCeti

namespace AbelianK0.AdditiveInvariant

variable (R : Type u) [Ring R] [IsNoetherianRing R] [HasRankNullity.{v} R]

/-- Finrank on `FGModuleCat R`, as a `ℤ`-valued invariant additive on short exact sequences.

The definition is sealed; use `finrank_obj` to evaluate it on an object. -/
noncomputable def finrank : AbelianK0.AdditiveInvariant (FGModuleCat.{v} R) ℤ where
  obj X := Module.finrank R X
  map_shortExact {S} hS := by
    let F := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
    let _ : Module.Finite R (S.map F).X₂ := inferInstanceAs (Module.Finite R S.X₂)
    -- Each `(S.map F).Xᵢ` is the module underlying `S.Xᵢ`, as in `finrank_forget₂_obj`.
    exact_mod_cast (hS.map_of_exact F).moduleCat_finrank_eq_add

/-- Evaluate the finrank additive invariant as the integer-valued module finrank. -/
@[simp]
lemma finrank_obj (X : FGModuleCat.{v} R) :
    (finrank R).obj X = (Module.finrank R X : ℤ) := (rfl)

end AbelianK0.AdditiveInvariant

end TauCeti
