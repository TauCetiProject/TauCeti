/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Basic

/-!
# Transporting dependent functions along composite equivalences

`Equiv.piCongrLeft P e : (∀ a, P (e a)) ≃ ∀ b, P b` transports dependent functions along an
equivalence `e : α ≃ β` of the index types. Transporting along `e₁ : α ≃ β` and then along
`e₂ : β ≃ γ` is transporting along the composite `e₁.trans e₂` (`Equiv.piCongrLeft_trans`), so
relabelling the factors of a product along two bijections in turn is relabelling them along the
composite bijection.
-/

public section

namespace Equiv

/-- Transporting dependent functions along `e₁ : α ≃ β` and then along `e₂ : β ≃ γ` is
transporting them along the composite `e₁.trans e₂`. -/
theorem piCongrLeft_trans {α β γ : Sort*} (P : γ → Sort*) (e₁ : α ≃ β) (e₂ : β ≃ γ) :
    (piCongrLeft (fun b ↦ P (e₂ b)) e₁).trans (piCongrLeft P e₂) =
      piCongrLeft P (e₁.trans e₂) :=
  symm_bijective.injective <| Equiv.ext fun _ ↦ funext fun _ ↦ (rfl)

end Equiv
