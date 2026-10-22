/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# The lax monoidal forgetful functor on modules

The forgetful functor from modules to types sends a pair of elements to their pure tensor,
and the unique element of the cartesian unit to `1`. Its lax monoidal structure lets one
pass from enrichment in simplicial modules to enrichment in simplicial sets.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

universe u

variable (R : Type u) [CommRing R]

/-- Forgetting modules is lax monoidal: the tensor comparison is the pure tensor map. -/
instance moduleCatForgetLaxMonoidal : (forget (ModuleCat.{u} R)).LaxMonoidal :=
  Functor.LaxMonoidal.ofTensorHom
    (ε := ↾fun _ ↦ (1 : R))
    (μ := fun _ _ ↦ ↾fun p ↦ p.1 ⊗ₜ[R] p.2)
    (μ_natural := by intros; rfl)
    (associativity := fun _ _ _ ↦ by ext ⟨⟨x, y⟩, z⟩; rfl)
    (left_unitality := fun _ ↦ by ext ⟨⟨⟩, x⟩; exact (one_smul R x).symm)
    (right_unitality := fun _ ↦ by ext ⟨x, ⟨⟩⟩; exact (one_smul R x).symm)

/-- The lax unit of the module forgetful functor selects `1`. -/
@[simp]
lemma moduleCatForget_ε (x : 𝟙_ (Type u)) :
    dsimp% Functor.LaxMonoidal.ε (forget (ModuleCat.{u} R)) x = (1 : R) :=
  (rfl)

/-- The tensor comparison of the module forgetful functor forms a pure tensor. -/
@[simp]
lemma moduleCatForget_μ (M N : ModuleCat.{u} R) (x : M) (y : N) :
    dsimp% Functor.LaxMonoidal.μ (forget (ModuleCat.{u} R)) M N (x, y) = x ⊗ₜ[R] y :=
  (rfl)

end TauCeti
