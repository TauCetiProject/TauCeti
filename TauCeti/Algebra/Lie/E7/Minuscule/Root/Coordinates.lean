/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.KostantForm

/-!
# Root and coroot coordinates for the E₇ minuscule construction

The coordinate equations below specialize the pinned Dynkin root-datum identities to the rank-seven
lattices used by the E₇ minuscule construction. They identify the simple coroots with coordinate
vectors, their pairings with coordinate evaluation, and the numbered generator weights with the
signed simple roots, which are nonzero in the integral lattice.
They require no minuscule carrier or group-scheme construction.

`RootDatum` uses the root identities in the carrier's conjugation equations;
`Generated.RootWeight` and `Generated.Coroot` use the same coordinates for the generated group.
The generic `DynkinType` API gives the entrywise Cartan-row formulas.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VI.

The identities are specializations of
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.KostantForm` and its root-datum
assembly dependencies.
-/

public section

namespace TauCeti.E7Minuscule

open DynkinType

/-- The named simple coroot is the corresponding coordinate vector. -/
theorem coroot_simpleIndex (ht : E7.Valid) (i : Fin 7) :
    ((E7.simplyConnectedRootDatum ht).coroot (E7.simpleIndex ht i) : Fin 7 → ℤ) =
      Pi.single i 1 := by
  -- Use the generic formula's index type so both occurrences of `Pi.single`
  -- have matching dependent types; `E7.rank` is definitionally seven.
  change (E7.simplyConnectedRootDatum ht).coroot (E7.simpleIndex ht i) =
    (Pi.single i 1 : Fin E7.rank → ℤ)
  exact E7.coroot_simpleIndex ht i

/-- A named simple coroot evaluates a weight at its numbered coordinate. -/
theorem coroot'_simpleIndex_apply (ht : E7.Valid) (i : Fin 7) (mu : Fin 7 → ℤ) :
    (E7.simplyConnectedRootDatum ht).coroot' (E7.simpleIndex ht i) mu = mu i := by
  simpa only [rank_E7] using E7.coroot'_simpleIndex_apply ht i mu

/-- The raising-generator weight is the named positive simple root. -/
theorem rootGeneratorWeight_inl_eq_root_simpleIndex (ht : E7.Valid) (i : Fin 7) :
    (E7.rootGeneratorWeight valid_E7 (.inl i) : Fin 7 → ℤ) =
      (E7.simplyConnectedRootDatum ht).root (E7.simpleIndex ht i) := by
  simpa only [rank_E7] using E7.rootGeneratorWeight_inl_eq_root_simpleIndex ht i

/-- The lowering-generator weight is the negative named simple root. -/
theorem rootGeneratorWeight_inr_eq_neg_root_simpleIndex (ht : E7.Valid) (i : Fin 7) :
    (E7.rootGeneratorWeight valid_E7 (.inr i) : Fin 7 → ℤ) =
      -(E7.simplyConnectedRootDatum ht).root (E7.simpleIndex ht i) := by
  simpa only [rank_E7] using E7.rootGeneratorWeight_inr_eq_neg_root_simpleIndex ht i

/-- Every numbered raising or lowering weight is nonzero in the integral character lattice. -/
theorem rootGeneratorWeight_ne_zero (k : Fin 7 ⊕ Fin 7) :
    (E7.rootGeneratorWeight valid_E7 k : Fin 7 → ℤ) ≠ 0 := by
  rcases k with i | i
  · intro hzero
    exact (E7.simplyConnectedRootDatum valid_E7).ne_zero _
      ((rootGeneratorWeight_inl_eq_root_simpleIndex valid_E7 i).symm.trans hzero)
  · intro hzero
    exact (E7.simplyConnectedRootDatum valid_E7).ne_zero _
      (neg_eq_zero.mp
        ((rootGeneratorWeight_inr_eq_neg_root_simpleIndex valid_E7 i).symm.trans hzero))

end TauCeti.E7Minuscule
