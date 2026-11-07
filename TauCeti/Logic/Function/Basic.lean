/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Function.Defs

/-!
# Basic lemmas on functions

* `Function.Injective.of_comp_eq`: if `g ∘ f` agrees pointwise with an injective map `f'`, then
  `f` is injective.
-/

public section

namespace Function

/-- If `g ∘ f` agrees pointwise with an injective map `f'`, then `f` is injective. This is
`Function.Injective.of_comp` when the factorization is given as a pointwise identity
`∀ x, g (f x) = f' x` (for instance between bundled homomorphisms). -/
theorem Injective.of_comp_eq {α β γ : Sort*} {f : α → β} {g : β → γ} {f' : α → γ}
    (hf' : Injective f') (h : ∀ x, g (f x) = f' x) : Injective f :=
  fun _ _ hab ↦ hf' (by rw [← h, ← h, hab])

end Function
