/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.HatBigrading
public import TauCeti.KnotTheory.Grid.SmallGrid.SimplyBlocked.Homology

/-!
# The simply blocked bigrading of the two-by-two unknot

Over any characteristic-two commutative coefficient ring, simply blocked homology of the
standard two-by-two unknot is concentrated in `(O-Maslov, Alexander)` bidegree `(0, 0)`.
The existing homogeneous-boundary computation and the internal direct sum establish these
piece equations without a field hypothesis.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3--4.6.
-/

public section

namespace TauCeti.GridDiagram

variable (R : Type*) [CommRing R] [CharP R 2]

local notation "P" => twoByTwo.isKnot_of_two.toOddComponentGridDiagram.bigradedHatHomologyPiece R 0

/-- Every nonzero bidegree piece of simply blocked homology of the standard two-by-two
unknot vanishes. -/
theorem twoByTwo_bigradedHatHomologyPiece_eq_bot {g : ℤ × ℤ} (hg : g ≠ (0, 0)) :
    P g = ⊥ := by
  apply le_antisymm _ bot_le
  intro y hy
  rw [Submodule.mem_bot]
  obtain ⟨z, hz, rfl⟩ := (twoByTwo.isKnot_of_two.mem_bigradedHatHomologyPiece_iff R 0).mp hy
  exact twoByTwo_simplyBlockedHomologyClass_eq_zero_of_bidegree_ne R z hg hz

/-- All simply blocked homology of the standard two-by-two unknot has bidegree `(0, 0)`. -/
theorem twoByTwo_bigradedHatHomologyPiece_zero_eq_top : P (0, 0) = ⊤ := by
  apply eq_top_iff.mpr
  rw [← twoByTwo.isKnot_of_two.toOddComponentGridDiagram.iSup_bigradedHatHomologyPiece_eq_top R 0]
  refine iSup_le fun g => ?_
  by_cases hg : g = (0, 0)
  · subst g
    exact le_rfl
  · rw [twoByTwo_bigradedHatHomologyPiece_eq_bot R hg]
    exact bot_le

end TauCeti.GridDiagram
