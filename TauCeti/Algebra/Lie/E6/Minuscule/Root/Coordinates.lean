/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter

/-!
# Simple-coroot coordinates for E₆

These equations specialize the pinned Dynkin root-datum identities to the rank-six lattices
used by the E₆ minuscule constructions. Simple coroots are coordinate vectors, their pairings
are coordinate evaluations, and the associated split-torus cocharacters evaluate coordinates.
They require no minuscule carrier or group-scheme construction. The generated doubled E₆
coroot differentials use these identifications.

The specializations follow `TauCeti.Algebra.Lie.E7.Minuscule.Root.Coordinates`.
-/

public section

namespace TauCeti.E6Minuscule

open DynkinType

/-- The named simple coroot is the corresponding coordinate vector. -/
theorem coroot_simpleIndex (ht : E6.Valid) (i : Fin 6) :
    ((E6.simplyConnectedRootDatum ht).coroot (E6.simpleIndex ht i) : Fin 6 → ℤ) =
      Pi.single i 1 := by
  -- Transport the rank in the decidable-equality instance used by `Pi.single` as well.
  simpa +instances only [rank_E6] using E6.coroot_simpleIndex ht i

/-- The coordinate evaluation cocharacter represents the named simple coroot. -/
theorem cocharEquiv_symm_coroot_simpleIndex (ht : E6.Valid) (i : Fin 6) :
    SplitTorus.cocharEquiv.symm ((E6.simplyConnectedRootDatum ht).coroot
      (E6.simpleIndex ht i) : Fin 6 → ℤ) = (Finsupp.applyAddHom i).toMultiplicative := by
  exact SplitTorus.cocharEquiv.symm_apply_eq.mpr
    ((coroot_simpleIndex ht i).trans (SplitTorus.cocharEquiv_applyAddHom i).symm)

/-- A named simple coroot evaluates a weight at its numbered coordinate. -/
theorem coroot'_simpleIndex_apply (ht : E6.Valid) (i : Fin 6) (mu : Fin 6 → ℤ) :
    (E6.simplyConnectedRootDatum ht).coroot' (E6.simpleIndex ht i) mu = mu i := by
  simpa only [rank_E6] using E6.coroot'_simpleIndex_apply ht i mu

end TauCeti.E6Minuscule
