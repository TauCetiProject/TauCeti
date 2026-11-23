/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Directed
public import Mathlib.Order.Interval.Set.Defs

/-!
# Upper intervals of a directed preorder are directed

An upper bound of two elements above `a` in a directed preorder is again above `a`, so the subtype
`Set.Ici a` is a directed preorder. Mathlib proves the corresponding cofinality statement,
`IsCofinal.Ici`, for partial orders; the instance here holds for every preorder. It makes
`Set.Ici a` an index type for direct limits, as in `TauCeti/Algebra/Category/Ring/DirectLimit.lean`.

## Main declarations

* `Set.Ici.isDirectedOrder`: `Set.Ici a` is a directed preorder when the ambient preorder is.
-/

public section

/-- The upper interval `Set.Ici a` of a directed preorder is directed. -/
instance Set.Ici.isDirectedOrder {α : Type*} [Preorder α] [IsDirectedOrder α] (a : α) :
    IsDirectedOrder (Set.Ici a) :=
  ⟨fun x y ↦
    let ⟨z, hxz, hyz⟩ := exists_ge_ge x.val y.val
    ⟨⟨z, x.property.trans hxz⟩, hxz, hyz⟩⟩
