/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Operations

/-!
# Examples: contragredients of character lines and the inverse transpose

* The dual of `ofCharacter χ` is `ofCharacter χ⁻¹`.
* It is not `ofCharacter χ` unless `χ = χ⁻¹`: a dual defined by the transpose without the inverse
  would return `χ` itself.
* The transpose `g ↦ gᵀ` is not multiplicative on `GL₂(𝔽₂) ≅ S₃` (it is an anti-homomorphism), so
  the dual of a framed representation needs the inverse transpose.
-/

open TauCeti ContinuousRep

variable {Γ A : Type*} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ] [CommRing A]
  [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace (Module.Dual A A)]
  [IsModuleTopology A (Module.Dual A A)]

-- The dual of the line of `χ` is the line of `χ⁻¹`.
example (χ : Γ →ₜ* Aˣ) : Nonempty (Iso (ofCharacter χ).dual (ofCharacter χ⁻¹)) :=
  ⟨dualOfCharacterIso χ⟩

-- The dual of the line of `χ` is not the line of `χ` when `χ⁻¹ ≠ χ`.
example (χ : Γ →ₜ* Aˣ) (hχ : χ⁻¹ ≠ χ) : IsEmpty (Iso (ofCharacter χ).dual (ofCharacter χ)) :=
  ⟨fun e => hχ ((nonempty_iso_ofCharacter_iff _ _).1 ⟨(dualOfCharacterIso χ).symm.trans e⟩)⟩

-- The transpose is not a group homomorphism `GL₂(𝔽₂) → GL₂(𝔽₂)`: for the transvections
-- `g = !![1, 1; 0, 1]` and `h = !![1, 0; 1, 1]`, `(g h)ᵀ = hᵀ gᵀ ≠ gᵀ hᵀ`.
open Matrix in
example : ¬ ∃ f : GL (Fin 2) (ZMod 2) →* GL (Fin 2) (ZMod 2),
    ∀ g, (f g : Matrix (Fin 2) (Fin 2) (ZMod 2)) = (g : Matrix (Fin 2) (Fin 2) (ZMod 2))ᵀ := by
  rintro ⟨f, hf⟩
  let g : GL (Fin 2) (ZMod 2) := ⟨!![1, 1; 0, 1], !![1, 1; 0, 1], by decide, by decide⟩
  let h : GL (Fin 2) (ZMod 2) := ⟨!![1, 0; 1, 1], !![1, 0; 1, 1], by decide, by decide⟩
  have := congrArg Units.val (map_mul f g h)
  rw [Units.val_mul, hf, hf, hf, Units.val_mul] at this
  revert this
  decide
