/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.SimplyBlocked
public import TauCeti.KnotTheory.Grid.Commutation.Grading.Map
public import TauCeti.KnotTheory.Grid.Grading.SimplyBlocked

/-!
# The bigrading of the simply blocked commutation map

The specialized pentagon map preserves both the O-Maslov and Alexander degrees,
transporting the blocked marking by the column transposition. This follows by lifting a
homogeneous specialized chain to an unblocked chain of the same bidegree. The result holds
over any commutative coefficient semiring and for any odd-component grid; only the
interpretation as simply blocked knot homology requires a knot.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.1;
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*) [CommSemiring R]
  (C : GridDiagram.ColumnCommutationData G.1) (i : Fin n)

/-- Commutation preserves the bidegree of a specialized chain, transporting the blocked
column along the transposition of columns. -/
theorem simplyBlockedCommutationMap_mem_bigradedChainHatPiece
    {g : ℤ × ℤ} {c : GridChainHat R n i} (hc : c ∈ G.bigradedChainHatPiece R i g) :
    G.1.simplyBlockedCommutationMap R C i c ∈
      (G.swapColumns C).bigradedChainHatPiece R
        (Equiv.swap C.column (finRotate n C.column) i) g := by
  obtain ⟨b, hb, rfl⟩ := G.mem_bigradedChainHatPiece_iff_exists.mp hc
  rw [GridDiagram.simplyBlockedCommutationMap_simplyBlockedSpecialization]
  exact (G.swapColumns C).simplyBlockedSpecialization_mem_bigradedChainHatPiece _
    (G.commutationMap_mem_bigradedChainMinusPiece C R hb)

end TauCeti.OddComponentGridDiagram
