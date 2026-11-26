/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Operations

/-!
# Examples: the contragredient of a character line

* The dual of `ofCharacter χ` is `ofCharacter χ⁻¹`.
* It is not `ofCharacter χ` unless `χ = χ⁻¹`: a dual defined by the transpose without the inverse
  would return `χ` itself.
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
