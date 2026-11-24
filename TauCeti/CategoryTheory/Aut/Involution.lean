/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Data.ZMod.Basic
import TauCeti.Data.ZMod.MonoidHomEquiv
import TauCeti.Data.ZMod.Two

/-!
# Involutive morphisms as `ℤ/2`-actions

Packages an involutive endomorphism `f : X ⟶ X` (`f ≫ f = 𝟙 X`) in any category into a group
homomorphism `Multiplicative (ZMod 2) →* Aut X` sending `ofAdd 1` to `f`.

## Main declarations

* `TauCeti.involutionAction`, `involutionAction_ofAdd_one`, `involutionAction_hom_eq_id_or`.
-/

public section

open CategoryTheory

namespace TauCeti

variable {C : Type*} [Category* C] {X : C} (f : X ⟶ X) (hf : f ≫ f = 𝟙 X)

/-- Package `f : X ⟶ X` (`f ≫ f = 𝟙 X`) as `Multiplicative (ZMod 2) →* Aut X`. -/
noncomputable def involutionAction : Multiplicative (ZMod 2) →* Aut X :=
  (zmodMonoidHomEquiv 2 (Aut X)).symm ⟨Aut.of ⟨f, f, hf, hf⟩, by
    rw [sq]; exact Aut.ext (Iso.ext hf)⟩

/-- The generator `ofAdd 1` acts as `f` under `involutionAction`. -/
@[simp]
theorem involutionAction_ofAdd_one : (involutionAction f hf (.ofAdd 1)).asIso.hom = f := by
  rw [involutionAction, zmodMonoidHomEquiv_symm_apply_ofAdd_one]

/-- Every element of `Multiplicative (ZMod 2)` acts either as `𝟙 X` or as `f`. -/
theorem involutionAction_hom_eq_id_or (θ : Multiplicative (ZMod 2)) :
    (involutionAction f hf θ).asIso.hom = 𝟙 X ∨ (involutionAction f hf θ).asIso.hom = f := by
  rcases Multiplicative.eq_one_or_eq_ofAdd_one θ with rfl | rfl
  · exact .inl (by simp)
  · exact .inr (involutionAction_ofAdd_one f hf)

end TauCeti
