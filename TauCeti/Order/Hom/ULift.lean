/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Hom.Basic

/-!
# Injectivity and range of lifted order homomorphisms

Mathlib's `OrderHom.uliftMap` lifts an order homomorphism `f : α →o β` to
`ULift α →o ULift β`. This file records that the lift is injective when `f` is, and that its range
consists of the lifts of the elements of the range of `f`. For instance, the coface maps
`(SimplexCategory.δ j).toOrderHom.uliftMap` between the `ULift (Fin _)` index types of simplicial
thickenings inherit injectivity and their range from `Fin.succAbove`.
-/

public section

namespace OrderHom

variable {α β : Type*} [Preorder α] [Preorder β] {f : α →o β}

/-- The lift of an injective order homomorphism to `ULift` is injective. -/
theorem uliftMap_injective (hf : Function.Injective f) : Function.Injective f.uliftMap :=
  fun _ _ h ↦ ULift.ext (hf (congrArg ULift.down h))

/-- An element of `ULift β` is in the range of `f.uliftMap` if and only if its underlying element
is in the range of `f`. -/
theorem mem_range_uliftMap_iff {x : ULift β} : x ∈ Set.range f.uliftMap ↔ x.down ∈ Set.range f :=
  ⟨fun ⟨y, hy⟩ ↦ ⟨y.down, congrArg ULift.down hy⟩, fun ⟨y, hy⟩ ↦ ⟨⟨y⟩, ULift.ext hy⟩⟩

end OrderHom

end
