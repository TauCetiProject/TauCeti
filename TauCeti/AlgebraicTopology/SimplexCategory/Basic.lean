/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Basic.Countable.Defs

/-!
# Cardinality instances for the simplex category

`SimplexCategory` has countably many objects, indexed by their length `SimplexCategory.len`, and
its `n`-truncated full subcategory `SimplexCategory.Truncated n` has finitely many objects,
indexed by `Fin (n + 1)`.
-/

public section

open CategoryTheory

namespace SimplexCategory

/-- `SimplexCategory` has countably many objects, indexed by their length. -/
instance countable : Countable SimplexCategory :=
  Function.Injective.countable (f := SimplexCategory.len) fun _ _ ↦ SimplexCategory.ext

/-- The `n`-truncated simplex category `SimplexCategory.Truncated n` has finitely many objects,
indexed by their length in `Fin (n + 1)`. -/
instance Truncated.finite (n : ℕ) : Finite (Truncated n) :=
  Finite.of_injective
    (fun a : Truncated n ↦ (⟨a.obj.len, Nat.lt_succ_of_le a.property⟩ : Fin (n + 1)))
    fun _ _ h ↦ ObjectProperty.FullSubcategory.ext (SimplexCategory.ext (Fin.mk.inj h))

end SimplexCategory
