/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.HalfTurn
public import TauCeti.KnotTheory.Grid.Homology.Unblocked

/-!
# The half-turn on unblocked grid homology

The half-turn of the torus carries a grid diagram `G` to `G.rotate` and its grid states to their
images under `GridState.halfTurn`, and it intertwines the unblocked differentials once the
variables are renamed along `Fin.rev` (`Differential/HalfTurn.lean`). This file descends that
symmetry to unblocked grid homology: `GH⁻(G)` and `GH⁻(G.rotate)` are identified by a
semilinear equivalence along the renaming of the variables.

## Main definitions

* `TauCeti.GridDiagram.unblockedHomologyRotateEquiv`: the equivalence `GH⁻(G) ≃ GH⁻(G.rotate)`
  induced by the half-turn, semilinear along the renaming of the variables by `Fin.revPerm`.

## Main results

* `TauCeti.GridDiagram.unblockedHomologyRotateEquiv_unblockedHomologyClass`,
  `TauCeti.GridDiagram.unblockedHomologyRotateEquiv_symm_unblockedHomologyClass`: it and its
  inverse send the class of a cycle to the class of the half-turned cycle.

## References

The symmetries of grid diagrams are in Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Chapter 3, and unblocked grid homology is defined in Chapter 4.6.
-/

public section

open MvPolynomial

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

/-- **The half-turn on `GH⁻`.** Moving grid states by the half-turn and renaming the variables
along `Fin.revPerm` induces an equivalence from `GH⁻(G)` to the unblocked homology of the
half-turned diagram `G.rotate`, semilinear along the renaming. -/
noncomputable def unblockedHomologyRotateEquiv :
    G.unblockedHomology R ≃ₛₗ[((renameEquiv R (Fin.revPerm (n := n))).toRingEquiv :
      MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R)] G.rotate.unblockedHomology R :=
  G.unblockedHomologyEquivOfIntertwining R _ (GridChain.halfTurnRenameEquiv R)
    (G.unblockedDifferential_rotate_halfTurnRenameEquiv R)

/-- The half-turn sends the class of a cycle `z` to the class of the half-turned cycle. -/
@[simp]
theorem unblockedHomologyRotateEquiv_unblockedHomologyClass
    (z : LinearMap.ker (G.unblockedDifferential R)) :
    G.unblockedHomologyRotateEquiv R (G.unblockedHomologyClass R z) =
      G.rotate.unblockedHomologyClass R
        ⟨GridChain.halfTurnRenameEquiv R z,
          G.map_mem_ker_unblockedDifferential_of_intertwining R _ _
            (G.unblockedDifferential_rotate_halfTurnRenameEquiv R) z.2⟩ :=
  G.unblockedHomologyEquivOfIntertwining_unblockedHomologyClass R _ _ _ z

/-- The inverse of the half-turn also moves the class of a cycle `w` of `GC⁻(G.rotate)` by the
half-turn, since the half-turn is an involution. -/
@[simp]
theorem unblockedHomologyRotateEquiv_symm_unblockedHomologyClass
    (w : LinearMap.ker (G.rotate.unblockedDifferential R)) :
    (G.unblockedHomologyRotateEquiv R).symm (G.rotate.unblockedHomologyClass R w) =
      G.unblockedHomologyClass R
        ⟨GridChain.halfTurnRenameEquiv R w,
          G.rotate.map_mem_ker_unblockedDifferential_of_intertwining R _ _
            (G.unblockedDifferential_halfTurnRenameEquiv R) w.2⟩ := by
  rw [LinearEquiv.symm_apply_eq, unblockedHomologyRotateEquiv_unblockedHomologyClass]
  exact congrArg _ (Subtype.ext (GridChain.halfTurnRenameEquiv_halfTurnRenameEquiv R _).symm)

end GridDiagram

end TauCeti
