/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly

/-!
# Simple-coroot coordinates for the E₆ minuscule construction

These specializations of the generic Dynkin root-datum formulas use the `Fin 6` weight
coordinates of the E₆ minuscule carrier. They identify the simple coroots with coordinate
vectors and their pairings with coordinate evaluation, without depending on the carrier.

The coordinate interface follows `TauCeti.Algebra.Lie.E7.Minuscule.Root.Coordinates`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.
-/

public section

namespace TauCeti.E6Minuscule

open DynkinType

/-- The named simple coroot is the corresponding coordinate vector. -/
theorem coroot_simpleIndex (ht : E6.Valid) (i : Fin 6) :
    ((E6.simplyConnectedRootDatum ht).coroot (E6.simpleIndex ht i) : Fin 6 → ℤ) =
      Pi.single i 1 := by
  -- The generic formula uses `Fin E6.rank`; this rank is definitionally six.
  exact E6.coroot_simpleIndex ht i

/-- A named simple coroot evaluates a weight at its numbered coordinate. -/
theorem coroot'_simpleIndex_apply (ht : E6.Valid) (i : Fin 6) (mu : Fin 6 → ℤ) :
    (E6.simplyConnectedRootDatum ht).coroot' (E6.simpleIndex ht i) mu = mu i := by
  -- Specialize the dependent rank-indexed formula to `Fin 6` before rewriting.
  simpa only [rank_E6] using E6.coroot'_simpleIndex_apply ht i mu

end TauCeti.E6Minuscule
