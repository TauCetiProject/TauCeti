/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.HalfTurn
public import TauCeti.KnotTheory.Grid.Grading.HalfTurn
public import TauCeti.KnotTheory.Grid.Grading.SimplyBlocked

/-!
# The half-turn of the simply blocked grid complex

Rotating a grid diagram by a half-turn (`GridDiagram.rotate`) sends the `O`-marking in column `i`
to `i.rev`. `GridChain.simplyBlockedHalfTurnEquiv` moves grid states by `GridState.halfTurn` and
renames surviving polynomial variables along `Fin.revPerm`; it commutes with specialization
(`simplyBlockedSpecialization_halfTurnRenameEquiv`), intertwines the simply blocked differentials
(`GridDiagram.simplyBlockedDifferential_rotate_simplyBlockedHalfTurnEquiv`), and identifies the
homogeneous chain pieces
(`OddComponentGridDiagram.simplyBlockedHalfTurnEquiv_mem_bigradedChainHatPiece_iff`), over any
commutative semiring.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters 3 and 4.6.
-/

public section

open MvPolynomial

namespace TauCeti

namespace GridChain

variable {n : ℕ} (R : Type*) [CommSemiring R] (i : Fin n)

/-- Move grid states by the half-turn and rename the surviving polynomial variables along
`Fin.revPerm`, transporting the blocked column from `i` to `i.rev`. -/
noncomputable def simplyBlockedHalfTurnEquiv :
    GridChainHat R n i ≃ₛₗ[
      ((simplyBlockedRenameEquiv R (Fin.revPerm (n := n)) i).toRingEquiv :
        MvPolynomial {c : Fin n // c ≠ i} R →+*
          MvPolynomial {c : Fin n // c ≠ Fin.revPerm i} R)]
      GridChainHat R n (Fin.revPerm i) :=
  (Finsupp.mapRange.linearEquiv
    (simplyBlockedRenameEquiv R (Fin.revPerm (n := n)) i).toRingEquiv.toSemilinearEquiv).trans
    (halfTurnEquiv (MvPolynomial {c : Fin n // c ≠ Fin.revPerm i} R))

/-- A coefficient of a half-turned specialized chain is the renamed coefficient at the half-turned
state. -/
@[simp]
theorem simplyBlockedHalfTurnEquiv_apply (c : GridChainHat R n i) (y : GridState n) :
    simplyBlockedHalfTurnEquiv R i c y =
      simplyBlockedRenameEquiv R (Fin.revPerm (n := n)) i (c y.halfTurn) := by
  rw [simplyBlockedHalfTurnEquiv, LinearEquiv.trans_apply, halfTurnEquiv_apply,
    Finsupp.mapRange.linearEquiv_apply, Finsupp.mapRange_apply]
  exact RingEquiv.toSemilinearEquiv_apply _ _

/-- The inverse half-turn reads coefficients at half-turned states and undoes the variable
renaming. -/
@[simp]
theorem simplyBlockedHalfTurnEquiv_symm_apply (c : GridChainHat R n (Fin.revPerm i))
    (y : GridState n) :
    (simplyBlockedHalfTurnEquiv R i).symm c y =
      (simplyBlockedRenameEquiv R (Fin.revPerm (n := n)) i).symm (c y.halfTurn) :=
  (simplyBlockedRenameEquiv R (Fin.revPerm (n := n)) i).injective <| by
    rw [AlgEquiv.apply_symm_apply]
    simpa only [simplyBlockedHalfTurnEquiv_apply, GridState.halfTurn_halfTurn] using
      congrArg (fun d => d y.halfTurn) ((simplyBlockedHalfTurnEquiv R i).apply_symm_apply c)

/-- The half-turn sends a single generator to the half-turned generator with renamed
coefficient. -/
@[simp]
theorem simplyBlockedHalfTurnEquiv_single (x : GridState n)
    (p : MvPolynomial {c : Fin n // c ≠ i} R) :
    simplyBlockedHalfTurnEquiv R i (Finsupp.single x p) =
      Finsupp.single x.halfTurn (simplyBlockedRenameEquiv R (Fin.revPerm (n := n)) i p) := by
  ext y : 1
  simp only [simplyBlockedHalfTurnEquiv_apply, Finsupp.single_apply,
    GridState.halfTurn_involutive.eq_iff]
  split_ifs <;> simp

end GridChain

/-- The half-turn commutes with specialization when the blocked column is transported to
`i.rev`. -/
@[simp]
theorem simplyBlockedSpecialization_halfTurnRenameEquiv {n : ℕ} (R : Type*) [CommSemiring R]
    (i : Fin n) (c : GridChainMinus R n) :
    simplyBlockedSpecialization R (Fin.revPerm i) (GridChain.halfTurnRenameEquiv R c) =
      GridChain.simplyBlockedHalfTurnEquiv R i (simplyBlockedSpecialization R i c) := by
  ext y : 1
  simp only [simplyBlockedSpecialization_apply, GridChain.halfTurnRenameEquiv_apply,
    GridChain.simplyBlockedHalfTurnEquiv_apply]
  exact simplyBlockedRingHom_rename R (Fin.revPerm (n := n)) i (c y.halfTurn)

/-- The half-turn intertwines the simply blocked differentials of `G` and `G.rotate`, moving the
blocked column from `i` to `i.rev`. -/
@[simp]
theorem GridDiagram.simplyBlockedDifferential_rotate_simplyBlockedHalfTurnEquiv {n : ℕ}
    (G : GridDiagram n) (R : Type*) [CommSemiring R] (i : Fin n) (c : GridChainHat R n i) :
    G.rotate.simplyBlockedDifferential R (Fin.revPerm i)
        (GridChain.simplyBlockedHalfTurnEquiv R i c) =
      GridChain.simplyBlockedHalfTurnEquiv R i (G.simplyBlockedDifferential R i c) := by
  obtain ⟨c, rfl⟩ := simplyBlockedSpecialization_surjective R i c
  rw [← simplyBlockedSpecialization_halfTurnRenameEquiv,
    ← simplyBlockedSpecialization_unblockedDifferential,
    unblockedDifferential_rotate_halfTurnRenameEquiv,
    simplyBlockedSpecialization_halfTurnRenameEquiv,
    simplyBlockedSpecialization_unblockedDifferential]

/-- The half-turn, renaming the surviving variables along `Fin.revPerm`, identifies the
homogeneous pieces of the specialized complexes blocking `i` and `i.rev`.

Not a simp lemma: the chain-piece membership criterion is already a simp lemma. -/
theorem OddComponentGridDiagram.simplyBlockedHalfTurnEquiv_mem_bigradedChainHatPiece_iff {n : ℕ}
    (G : OddComponentGridDiagram n) {R : Type*} [CommSemiring R] {i : Fin n} {g : ℤ × ℤ}
    {c : GridChainHat R n i} :
    GridChain.simplyBlockedHalfTurnEquiv R i c ∈
        G.rotate.bigradedChainHatPiece R (Fin.revPerm i) g ↔
      c ∈ G.bigradedChainHatPiece R i g :=
  mem_bigradedChainHatPiece_iff_of_rename (φ := GridState.halfTurn) (κ := Fin.revPerm)
    GridState.halfTurn_involutive.surjective G.bidegree_rotate_halfTurn
    (fun x => by rw [GridChain.simplyBlockedHalfTurnEquiv_apply, GridState.halfTurn_halfTurn])

end TauCeti
