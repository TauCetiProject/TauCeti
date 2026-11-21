/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Basic.Countable.Defs

/-!
# Basic properties and cardinality instances for the simplex category

`SimplexCategory` has countably many objects, indexed by their length `SimplexCategory.len`
(`SimplexCategory.countable`), and its `n`-truncated full subcategory `SimplexCategory.Truncated n`
has finitely many objects, indexed by `Fin (n + 1)` (`SimplexCategory.Truncated.finite`).

Every epimorphism `f : x ⟶ y` in `SimplexCategory` is surjective on vertices and monotone, so it
fixes the initial vertex `0` (`SimplexCategory.toOrderHom_zero_of_epi`). This ensures that
simplicial objects whose `n`-simplices are indexed by simplices via their initial vertex inherit
degeneracy splittings along epimorphisms in `SimplexCategory`.
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

/-- Every epimorphism in `SimplexCategory` fixes the initial vertex `0`. -/
@[simp]
theorem toOrderHom_zero_of_epi {x y : SimplexCategory} (f : x ⟶ y) [Epi f] :
    f.toOrderHom 0 = 0 := by
  obtain ⟨k, hk⟩ := (epi_iff_surjective.mp ‹Epi f›) 0
  exact le_antisymm (hk ▸ f.toOrderHom.monotone (Fin.zero_le k)) (Fin.zero_le _)

end SimplexCategory
