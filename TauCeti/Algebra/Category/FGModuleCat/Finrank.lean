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
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

namespace AbelianK0.AdditiveInvariant

variable (k : Type u) [DivisionRing k]

/-- Finrank on `FGModuleCat k`, as a `ℤ`-valued invariant additive on short exact sequences. -/
@[expose]
noncomputable def finrank : AbelianK0.AdditiveInvariant (FGModuleCat.{v} k) ℤ where
  obj X := Module.finrank k X
  map_iso {_ _} e := congrArg Int.ofNat (FGModuleCat.isoToLinearEquiv e).finrank_eq
  map_shortExact {S} hS := by
    let F := forget₂ (FGModuleCat.{v} k) (ModuleCat.{v} k)
    have hS' : (S.map F).ShortExact := hS.map_of_exact F
    let _ : Module.Finite k (S.map F).X₁ := S.X₁.property
    let _ : Module.Finite k (S.map F).X₃ := S.X₃.property
    have h := ModuleCat.free_shortExact_finrank_add hS' (n := Module.finrank k S.X₁)
      (p := Module.finrank k S.X₃) rfl rfl
    exact_mod_cast h

@[simp]
lemma finrank_obj (X : FGModuleCat.{v} k) :
    (finrank k).obj X = (Module.finrank k X : ℤ) := rfl

end AbelianK0.AdditiveInvariant

namespace FGModuleCat

variable (k : Type u) [DivisionRing k]

/-- Forgetting the finite-generation witness does not change finrank. -/
@[simp]
theorem finrank_forget₂_obj (X : FGModuleCat.{v} k) :
    Module.finrank k ((forget₂ (FGModuleCat.{v} k) (ModuleCat.{v} k)).obj X) =
      Module.finrank k X := rfl

end FGModuleCat

end TauCeti
