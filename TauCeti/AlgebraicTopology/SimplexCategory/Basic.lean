/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Basic properties of morphisms in the simplex category

Every epimorphism `f : x ⟶ y` in `SimplexCategory` is surjective on vertices and monotone, so it
fixes the initial vertex `0` (`SimplexCategory.toOrderHom_zero_of_epi`). This ensures that
simplicial objects whose `n`-simplices are indexed by simplices via their initial vertex inherit
degeneracy splittings along epimorphisms in `SimplexCategory`. We also record
`SimplexCategory.mkOfLe_eq_const`, identifying `mkOfLe i j h` with a constant map when `i = j`.
-/

public section

open CategoryTheory
open scoped Simplicial

namespace SimplexCategory

/-- Every epimorphism in `SimplexCategory` fixes the initial vertex `0`. -/
@[simp]
theorem toOrderHom_zero_of_epi {x y : SimplexCategory} (f : x ⟶ y) [Epi f] :
    f.toOrderHom 0 = 0 := by
  obtain ⟨k, hk⟩ := (epi_iff_surjective.mp ‹Epi f›) 0
  exact le_antisymm (hk ▸ f.toOrderHom.monotone (Fin.zero_le k)) (Fin.zero_le _)

/-- When `i = j`, `SimplexCategory.mkOfLe i j h` is the constant map `⦋1⦌.const ⦋n⦌ i`. -/
lemma mkOfLe_eq_const {n : ℕ} {i j : Fin (n + 1)} (h : i ≤ j) (hij : i = j) :
    mkOfLe i j h = ⦋1⦌.const ⦋n⦌ i := by
  subst hij; exact mkOfLe_refl i

end SimplexCategory
