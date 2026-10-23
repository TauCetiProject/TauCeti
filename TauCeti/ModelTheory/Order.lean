/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Order

/-!
# Ordered structures from the order of a type

Mathlib's `FirstOrder.Language.orderStructure` makes a type with `≤` a structure in the language
of orders, but it is not an instance, and neither it nor a structure in an expanded language
`L.sum Language.order` is known to be an `OrderedStructure`. This file supplies both instances.
Thus, after installing `orderStructure M` and an `L`-structure on `M`, for example
`FirstOrder.Ring.compatibleRingOfRing M` for the language of rings, the expanded structure on `M`
interprets `≤` as the order of `M`, and results stated for ordered structures apply to it.
-/

public section

namespace FirstOrder.Language

variable {L : Language} {M : Type*}

/-- The order structure of a type interprets the order symbol `≤` as the order of the type. -/
instance orderedStructure_orderStructure (M : Type*) [LE M] :
    @OrderedStructure Language.order M _ _ (orderStructure M) :=
  @OrderedStructure.mk _ _ _ _ (orderStructure M) fun _ ↦ Iff.rfl

/-- Expanding a language by the order symbol preserves the interpretation of `≤`. -/
instance orderedStructure_sum [L.Structure M] [LE M] [Language.order.Structure M]
    [Language.order.OrderedStructure M] : (L.sum Language.order).OrderedStructure M :=
  ⟨fun x ↦ relMap_leSymb (L := Language.order) x⟩

end FirstOrder.Language
