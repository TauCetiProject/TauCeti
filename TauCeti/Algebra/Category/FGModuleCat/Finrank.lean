/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Free
public import TauCeti.CategoryTheory.GrothendieckGroup.Abelian

/-!
# Finrank as an additive invariant

This file packages finrank on finite-dimensional vector spaces as an invariant additive on short
exact sequences. It is the reusable bridge from `FGModuleCat` to abelian Grothendieck groups.

Additivity has to be read off from `ModuleCat.free_shortExact_finrank_add`, which lives one
category down, so the file first records how the forgetful functor
`forget₂ (FGModuleCat k) (ModuleCat k)` interacts with finrank. This is the only place where the
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

variable (k : Type u) [DivisionRing k]

/-- Finrank on `FGModuleCat k`, as a `ℤ`-valued invariant additive on short exact sequences.

The definition is sealed; use `finrank_obj` to evaluate it on an object. -/
noncomputable def finrank : AbelianK0.AdditiveInvariant (FGModuleCat.{v} k) ℤ where
  obj X := Module.finrank k X
  map_iso {_ _} e := congrArg Int.ofNat (FGModuleCat.isoToLinearEquiv e).finrank_eq
  map_shortExact {S} hS := by
    let F := forget₂ (FGModuleCat.{v} k) (ModuleCat.{v} k)
    have hS' : (S.map F).ShortExact := hS.map_of_exact F
    let _ : Module.Finite k (S.map F).X₁ := inferInstanceAs (Module.Finite k S.X₁)
    let _ : Module.Finite k (S.map F).X₃ := inferInstanceAs (Module.Finite k S.X₃)
    have h := ModuleCat.free_shortExact_finrank_add hS' (n := Module.finrank k S.X₁)
      (p := Module.finrank k S.X₃) (FGModuleCat.finrank_forget₂_obj S.X₁)
      (FGModuleCat.finrank_forget₂_obj S.X₃)
    exact_mod_cast h

/-- Evaluate the finrank additive invariant as the integer-valued module finrank. -/
@[simp]
lemma finrank_obj (X : FGModuleCat.{v} k) :
    (finrank k).obj X = (Module.finrank k X : ℤ) := (rfl)

end AbelianK0.AdditiveInvariant

end TauCeti
