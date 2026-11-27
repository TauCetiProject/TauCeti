/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.HomLift

/-!
# Lifts with fixed endpoints

When a morphism `f` of the base already has the source `p.obj a` and target `p.obj b`, a morphism
`φ : a ⟶ b` lifts `f` through `p` exactly when `p.map φ = f`.
-/

public section

namespace CategoryTheory.Functor

variable {𝒮 : Type*} {𝒳 : Type*} [Category* 𝒳] [Category* 𝒮] {p : 𝒳 ⥤ 𝒮}

/-- A morphism `φ : a ⟶ b` lifts a morphism `f : p.obj a ⟶ p.obj b` exactly when `p.map φ = f`. -/
lemma isHomLift_iff_map_eq {a b : 𝒳} {f : p.obj a ⟶ p.obj b} {φ : a ⟶ b} :
    p.IsHomLift f φ ↔ p.map φ = f :=
  ⟨fun _ ↦ (IsHomLift.eq_of_isHomLift p f φ).symm, fun h ↦ h ▸ IsHomLift.map φ⟩

end CategoryTheory.Functor
