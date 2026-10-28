/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.PowersetCard

/-!
# Coercions from fixed-cardinality subsets

`Set.powersetCard.coe_ofSingleton` identifies the finite set underlying the singleton
equivalence. It lets computations with fixed-cardinality subsets use the usual singleton API.
-/

public section

namespace Set.powersetCard

/-- The finite set underlying the singleton equivalence is the singleton itself. -/
@[simp]
theorem coe_ofSingleton {α : Type*} (a : α) :
    ((ofSingleton a : powersetCard α 1) : Finset α) = {a} := rfl

end Set.powersetCard
