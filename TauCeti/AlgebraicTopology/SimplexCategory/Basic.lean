/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

import TauCeti.Data.Fin.Basic

/-!
# Basic properties of the simplex category

Every epimorphism `f : x ⟶ y` in `SimplexCategory` is surjective on vertices and monotone, so it
fixes the initial vertex `0` (`SimplexCategory.toOrderHom_zero_of_epi`). This ensures that
simplicial objects whose `n`-simplices are indexed by simplices via their initial vertex inherit
degeneracy splittings along epimorphisms in `SimplexCategory`.

The coface map `δ k` fixes the vertices before `k` and shifts the others up by one; on vertex
values in `ℕ` this is `TauCeti.SimplexCategory.val_δ_toOrderHom_apply`, the form in which
identities between cofaces and other vertex maps are checked after `ext`.
-/

public section

open CategoryTheory

namespace SimplexCategory

/-- Every epimorphism in `SimplexCategory` fixes the initial vertex `0`. -/
@[simp]
theorem toOrderHom_zero_of_epi {x y : SimplexCategory} (f : x ⟶ y) [Epi f] :
    f.toOrderHom 0 = 0 := by
  obtain ⟨k, hk⟩ := (epi_iff_surjective.mp ‹Epi f›) 0
  exact le_antisymm (hk ▸ f.toOrderHom.monotone (Fin.zero_le k)) (Fin.zero_le _)

end SimplexCategory

namespace TauCeti.SimplexCategory

open _root_.SimplexCategory

/-- The coface map `δ k` fixes the vertices before `k` and shifts the others up by one.

This is `SimplexCategory.δ_apply` read under `Fin.val` with `Fin.val_succAbove`.  It is stated for
the underlying monotone map `(δ k).toOrderHom`, the form a vertex computation reaches after `ext`;
`δ_apply` is stated for the concrete-category application `δ k x`, which is by definition
`(δ k).toOrderHom x` (the concrete-category structure of `SimplexCategory` has
`hom := Hom.toOrderHom`). -/
lemma val_δ_toOrderHom_apply {n : ℕ} (k : Fin (n + 2)) (x : Fin (n + 1)) :
    ((δ k).toOrderHom x : ℕ) = if (x : ℕ) < k then (x : ℕ) else x + 1 := by
  -- The concrete-category application `δ k x` of `δ_apply` unfolds to `(δ k).toOrderHom x`.
  rw [show (δ k).toOrderHom x = k.succAbove x from δ_apply k x, Fin.val_succAbove]

end TauCeti.SimplexCategory
