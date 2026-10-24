/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Chain.Basic
public import TauCeti.KnotTheory.Grid.Rotation

/-!
# The half-turn on grid chains

The half-turn of grid points induces an involutive linear equivalence on the free module of
grid states. This is the chain relabeling for the fully blocked theory; coefficients are not
renamed. Its compatibility with the differential is proved in `Differential/HalfTurn.lean`.

The coordinate convention follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Chapter 3. The construction uses Mathlib's `Finsupp.domLCongr`.
-/

public section

namespace TauCeti.GridChain

variable {n : ℕ} (R : Type*) [Semiring R]

/-- The half-turn on grid chains, leaving coefficients fixed. -/
noncomputable def halfTurnEquiv : GridChain R n ≃ₗ[R] GridChain R n :=
  Finsupp.domLCongr (Function.Involutive.toPerm _ GridState.halfTurn_involutive)

/-- The coefficient at a state is read at its half-turn. -/
@[simp]
theorem halfTurnEquiv_apply (c : GridChain R n) (y : GridState n) :
    halfTurnEquiv R c y = c y.halfTurn := by
  rw [halfTurnEquiv, Finsupp.domLCongr_apply]
  exact Finsupp.equivMapDomain_apply _ _ _

/-- The half-turn moves each basis generator to its rotated state. -/
@[simp]
theorem halfTurnEquiv_single (x : GridState n) (a : R) :
    halfTurnEquiv R (Finsupp.single x a) = Finsupp.single x.halfTurn a :=
  Finsupp.domLCongr_single _ x a

/-- Applying the half-turn twice fixes every chain. -/
@[simp]
theorem halfTurnEquiv_halfTurnEquiv (c : GridChain R n) :
    halfTurnEquiv R (halfTurnEquiv R c) = c := by
  ext y
  simp

/-- The inverse half-turn is the half-turn itself. -/
@[simp]
theorem halfTurnEquiv_symm : (halfTurnEquiv R (n := n)).symm = halfTurnEquiv R := by
  apply LinearEquiv.ext
  intro c
  apply (halfTurnEquiv R).injective
  simp

end TauCeti.GridChain
