/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Transpose
public import TauCeti.KnotTheory.Grid.SimplyBlocked.Basic

/-!
# Diagonal reflection of the simply blocked grid complex

Reflection sends the `O`-marking in column `i` to column `G.O i`. Consequently it identifies
chains with `V_i = 0` with reflected chains with `V_{G.O i} = 0`, renaming the surviving
variables along `G.O`. The specified semilinear equivalence commutes with specialization
from the unblocked complex and intertwines the simply blocked differentials.

This symmetry exchanges row and column commutations while retaining the chosen blocked marking.
The unsigned chain identities hold over any commutative semiring; characteristic two is needed
only when taking homology.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters 3 and 4.6.
The construction specializes `GridDiagram.transposeRenameEquiv` and its differential identity.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommSemiring R] (i : Fin n)

/-- Reflect grid states and rename the surviving variables, blocking the reflected `O`-marking. -/
noncomputable def simplyBlockedTransposeEquiv :
    GridChainHat R n i ≃ₛₗ[((simplyBlockedRenameEquiv R G.O.toPerm i).toRingEquiv :
      MvPolynomial {c : Fin n // c ≠ i} R →+*
        MvPolynomial {c : Fin n // c ≠ G.O i} R)] GridChainHat R n (G.O i) :=
  (Finsupp.mapRange.linearEquiv
    (simplyBlockedRenameEquiv R G.O.toPerm i).toRingEquiv.toSemilinearEquiv).trans
    (GridChain.transposeEquiv _ n)

/-- A coefficient of a reflected chain is the renamed coefficient at the reflected state. -/
@[simp]
theorem simplyBlockedTransposeEquiv_apply (c : GridChainHat R n i) (y : GridState n) :
    G.simplyBlockedTransposeEquiv R i c y =
      simplyBlockedRenameEquiv R G.O.toPerm i (c y.transpose) := by
  simp only [simplyBlockedTransposeEquiv, LinearEquiv.trans_apply,
    GridChain.transposeEquiv_apply, Finsupp.mapRange.linearEquiv_apply,
    Finsupp.mapRange_apply, RingEquiv.toSemilinearEquiv_apply, AlgEquiv.coe_toRingEquiv]

/-- Inverse reflection reads coefficients at reflected states and undoes the variable renaming. -/
@[simp]
theorem simplyBlockedTransposeEquiv_symm_apply (c : GridChainHat R n (G.O i))
    (y : GridState n) :
    (G.simplyBlockedTransposeEquiv R i).symm c y =
      (simplyBlockedRenameEquiv R G.O.toPerm i).symm (c y.transpose) := by
  apply (simplyBlockedRenameEquiv R G.O.toPerm i).injective
  rw [AlgEquiv.apply_symm_apply]
  have h := congrArg (fun c => c y.transpose)
    ((G.simplyBlockedTransposeEquiv R i).apply_symm_apply c)
  simpa only [simplyBlockedTransposeEquiv_apply, GridState.transpose_transpose] using h

/-- Reflection takes a single generator to the reflected generator with renamed coefficient. -/
@[simp]
theorem simplyBlockedTransposeEquiv_single (x : GridState n)
    (p : MvPolynomial {c : Fin n // c ≠ i} R) :
    G.simplyBlockedTransposeEquiv R i (Finsupp.single x p) =
      Finsupp.single x.transpose (simplyBlockedRenameEquiv R G.O.toPerm i p) := by
  have hinv : Function.Involutive (GridState.transpose (n := n)) := GridState.transpose_transpose
  ext y : 1
  simp only [simplyBlockedTransposeEquiv_apply, Finsupp.single_apply, ← hinv.eq_iff]
  split_ifs <;> simp

/-- Reflection commutes with specialization when the blocked marking is reflected too. -/
@[simp]
theorem simplyBlockedSpecialization_transposeRenameEquiv (c : GridChainMinus R n) :
    simplyBlockedSpecialization R (G.O i) (G.transposeRenameEquiv R c) =
      G.simplyBlockedTransposeEquiv R i (simplyBlockedSpecialization R i c) := by
  ext y : 1
  simp only [simplyBlockedSpecialization_apply, transposeRenameEquiv_apply,
    simplyBlockedTransposeEquiv_apply]
  exact simplyBlockedRingHom_rename R G.O.toPerm i (c y.transpose)

/-- Reflection intertwines the simply blocked differentials with the blocked marking transported
along `G.O`. -/
@[simp]
theorem simplyBlockedDifferential_transpose_simplyBlockedTransposeEquiv
    (c : GridChainHat R n i) :
    G.transpose.simplyBlockedDifferential R (G.O i) (G.simplyBlockedTransposeEquiv R i c) =
      G.simplyBlockedTransposeEquiv R i (G.simplyBlockedDifferential R i c) := by
  obtain ⟨c, rfl⟩ := simplyBlockedSpecialization_surjective R i c
  rw [← simplyBlockedSpecialization_transposeRenameEquiv,
    ← simplyBlockedSpecialization_unblockedDifferential,
    unblockedDifferential_transpose_transposeRenameEquiv,
    simplyBlockedSpecialization_transposeRenameEquiv,
    simplyBlockedSpecialization_unblockedDifferential]

end TauCeti.GridDiagram
