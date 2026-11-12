/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.HalfTurn
public import TauCeti.KnotTheory.Grid.SimplyBlocked.Basic
public import TauCeti.KnotTheory.Grid.Grading.Unblocked.HalfTurn
public import TauCeti.KnotTheory.Grid.Grading.SimplyBlocked

/-!
# The half-turn of the simply blocked grid complex

The half-turn identifies chains with the `O`-marking in column `i` blocked with chains for
`G.rotate` blocked at `i.rev`. It moves states by `GridState.halfTurn` and renames the
surviving variables along `Fin.revPerm`. Specialization from the unblocked complex commutes
with this equivalence, which intertwines the two differentials over any commutative semiring.
On odd-component diagrams it preserves the `(O-Maslov, Alexander)` chain bigrading. Its
homology comparison exchanges the south-west and north-east stabilization corners while
tracking the blocked marking.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.2.
The construction specializes `GridChain.halfTurnRenameEquiv`.
-/

public section

namespace TauCeti

/-- The `Fin.revPerm` specialization of `simplyBlockedRenameEquiv`, reversing surviving
columns and transporting the blocked column to the target index `{c // c ≠ i.rev}`. -/
noncomputable def simplyBlockedHalfTurnRenameEquiv {n : ℕ} (R : Type*) [CommSemiring R]
    (i : Fin n) :
    MvPolynomial {c : Fin n // c ≠ i} R ≃ₐ[R] MvPolynomial {c : Fin n // c ≠ i.rev} R := by
  exact simplyBlockedRenameEquiv R (Fin.rev_involutive.toPerm Fin.rev) i

/-- A surviving variable is sent to its reversed column. -/
@[simp]
theorem simplyBlockedHalfTurnRenameEquiv_X {n : ℕ} (R : Type*) [CommSemiring R]
    (i : Fin n) (c : {c : Fin n // c ≠ i}) :
    simplyBlockedHalfTurnRenameEquiv R i (MvPolynomial.X c) =
      MvPolynomial.X ⟨c.1.rev, fun h => c.2 (Fin.rev_injective h)⟩ :=
  simplyBlockedRenameEquiv_X R (Fin.rev_involutive.toPerm Fin.rev) i c

/-- Constants are fixed by the half-turn coefficient renaming. -/
@[simp]
theorem simplyBlockedHalfTurnRenameEquiv_C {n : ℕ} (R : Type*) [CommSemiring R]
    (i : Fin n) (r : R) :
    simplyBlockedHalfTurnRenameEquiv R i (MvPolynomial.C r) = MvPolynomial.C r :=
  (simplyBlockedHalfTurnRenameEquiv R i).commutes r

/-- The inverse coefficient renaming takes a variable back to its reversed column. -/
@[simp]
theorem simplyBlockedHalfTurnRenameEquiv_symm_X {n : ℕ} (R : Type*) [CommSemiring R]
    (i : Fin n) (c : {c : Fin n // c ≠ i.rev}) :
    (simplyBlockedHalfTurnRenameEquiv R i).symm (MvPolynomial.X c) =
      MvPolynomial.X ⟨c.1.rev,
        fun h => c.2 ((Fin.rev_rev c.1).symm.trans (congrArg Fin.rev h))⟩ := by
  apply (simplyBlockedHalfTurnRenameEquiv R i).injective
  simp only [AlgEquiv.apply_symm_apply, simplyBlockedHalfTurnRenameEquiv_X, Fin.rev_rev]

/-- The inverse coefficient renaming fixes constants. -/
@[simp]
theorem simplyBlockedHalfTurnRenameEquiv_symm_C {n : ℕ} (R : Type*) [CommSemiring R]
    (i : Fin n) (r : R) :
    (simplyBlockedHalfTurnRenameEquiv R i).symm (MvPolynomial.C r) = MvPolynomial.C r :=
  (simplyBlockedHalfTurnRenameEquiv R i).symm.commutes r

/-- Blocking commutes with the half-turn renaming of coefficients. -/
theorem simplyBlockedRingHom_rename_rev {n : ℕ} (R : Type*) [CommSemiring R]
    (i : Fin n) (p : MvPolynomial (Fin n) R) :
    simplyBlockedRingHom R i.rev (MvPolynomial.rename Fin.rev p) =
      simplyBlockedHalfTurnRenameEquiv R i (simplyBlockedRingHom R i p) := by
  exact simplyBlockedRingHom_rename R (Fin.rev_involutive.toPerm Fin.rev) i p

/-- The half-turn coefficient renaming and its inverse form an inverse pair. -/
noncomputable instance simplyBlockedHalfTurnRenameRingHomInvPair {n : ℕ} (R : Type*)
    [CommSemiring R] (i : Fin n) :
    RingHomInvPair
      ((simplyBlockedHalfTurnRenameEquiv R i).toRingEquiv :
        MvPolynomial {c : Fin n // c ≠ i} R →+* MvPolynomial {c : Fin n // c ≠ i.rev} R)
      ((simplyBlockedHalfTurnRenameEquiv R i).toRingEquiv.symm :
        MvPolynomial {c : Fin n // c ≠ i.rev} R →+* MvPolynomial {c : Fin n // c ≠ i} R) :=
  RingHomInvPair.of_ringEquiv _

/-- The inverse half-turn coefficient renaming and its forward map form an inverse pair. -/
noncomputable instance simplyBlockedHalfTurnRenameRingHomInvPairSymm {n : ℕ} (R : Type*)
    [CommSemiring R] (i : Fin n) :
    RingHomInvPair
      ((simplyBlockedHalfTurnRenameEquiv R i).toRingEquiv.symm :
        MvPolynomial {c : Fin n // c ≠ i.rev} R →+* MvPolynomial {c : Fin n // c ≠ i} R)
      ((simplyBlockedHalfTurnRenameEquiv R i).toRingEquiv :
        MvPolynomial {c : Fin n // c ≠ i} R →+* MvPolynomial {c : Fin n // c ≠ i.rev} R) :=
  RingHomInvPair.of_ringEquiv_symm _

namespace GridChain

variable {n : ℕ} (R : Type*) [CommSemiring R] (i : Fin n)

/-- Half-turn grid states and rename the surviving variables, blocking column `i.rev`. -/
noncomputable def simplyBlockedHalfTurnEquiv :
    GridChainHat R n i ≃ₛₗ[((simplyBlockedHalfTurnRenameEquiv R i).toRingEquiv :
      MvPolynomial {c : Fin n // c ≠ i} R →+*
        MvPolynomial {c : Fin n // c ≠ i.rev} R)] GridChainHat R n (i.rev) :=
  (Finsupp.mapRange.linearEquiv
    (simplyBlockedHalfTurnRenameEquiv R i).toRingEquiv.toSemilinearEquiv).trans
    (Finsupp.domLCongr (Function.Involutive.toPerm _ GridState.halfTurn_involutive))

/-- A coefficient of a half-turned chain is the renamed coefficient at the half-turned state. -/
@[simp↓]
theorem simplyBlockedHalfTurnEquiv_apply (c : GridChainHat R n i) (y : GridState n) :
    simplyBlockedHalfTurnEquiv R i c y =
      simplyBlockedHalfTurnRenameEquiv R i (c y.halfTurn) := by
  rw [simplyBlockedHalfTurnEquiv]
  rfl

/-- Inverse half-turn reads coefficients at half-turned states and undoes the variable renaming. -/
@[simp↓]
theorem simplyBlockedHalfTurnEquiv_symm_apply (c : GridChainHat R n (i.rev))
    (y : GridState n) :
    (simplyBlockedHalfTurnEquiv R i).symm c y =
      (simplyBlockedHalfTurnRenameEquiv R i).symm (c y.halfTurn) := by
  apply (simplyBlockedHalfTurnRenameEquiv R i).injective
  rw [AlgEquiv.apply_symm_apply]
  have h := congrArg (fun c => c y.halfTurn)
    ((simplyBlockedHalfTurnEquiv R i).apply_symm_apply c)
  simpa only [simplyBlockedHalfTurnEquiv_apply, GridState.halfTurn_halfTurn] using h

/-- The half-turn takes a single generator to the half-turned generator with renamed coefficient. -/
@[simp↓]
theorem simplyBlockedHalfTurnEquiv_single (x : GridState n)
    (p : MvPolynomial {c : Fin n // c ≠ i} R) :
    simplyBlockedHalfTurnEquiv R i (Finsupp.single x p) =
      Finsupp.single x.halfTurn (simplyBlockedHalfTurnRenameEquiv R i p) := by
  have hinv : Function.Involutive (GridState.halfTurn (n := n)) := GridState.halfTurn_halfTurn
  ext y : 1
  simp only [simplyBlockedHalfTurnEquiv_apply, Finsupp.single_apply, ← hinv.eq_iff]
  split_ifs <;> simp

/-- The inverse half-turn takes a single generator back with inverse-renamed coefficient. -/
@[simp↓]
theorem simplyBlockedHalfTurnEquiv_symm_single (x : GridState n)
    (p : MvPolynomial {c : Fin n // c ≠ i.rev} R) :
    (simplyBlockedHalfTurnEquiv R i).symm (Finsupp.single x p) =
      Finsupp.single x.halfTurn ((simplyBlockedHalfTurnRenameEquiv R i).symm p) := by
  apply (simplyBlockedHalfTurnEquiv R i).injective
  rw [LinearEquiv.apply_symm_apply, simplyBlockedHalfTurnEquiv_single,
    GridState.halfTurn_halfTurn, AlgEquiv.apply_symm_apply]

/-- The half-turn commutes with specialization when the blocked marking is half-turned too. -/
@[simp↓]
theorem simplyBlockedSpecialization_halfTurnRenameEquiv (c : GridChainMinus R n) :
    simplyBlockedSpecialization R (i.rev) (GridChain.halfTurnRenameEquiv R c) =
      simplyBlockedHalfTurnEquiv R i (simplyBlockedSpecialization R i c) := by
  ext y : 1
  simp only [simplyBlockedSpecialization_apply, GridChain.halfTurnRenameEquiv_apply,
    simplyBlockedHalfTurnEquiv_apply]
  exact simplyBlockedRingHom_rename_rev R i (c y.halfTurn)

/-- Inverse half-turn commutes with specialization of the unblocked half-turn. -/
theorem simplyBlockedHalfTurnEquiv_symm_specialization (c : GridChainMinus R n) :
    (simplyBlockedHalfTurnEquiv R i).symm (simplyBlockedSpecialization R i.rev c) =
      simplyBlockedSpecialization R i (GridChain.halfTurnRenameEquiv R c) := by
  apply (simplyBlockedHalfTurnEquiv R i).injective
  rw [LinearEquiv.apply_symm_apply, ← simplyBlockedSpecialization_halfTurnRenameEquiv,
    GridChain.halfTurnRenameEquiv_halfTurnRenameEquiv]

end GridChain

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommSemiring R] (i : Fin n)

open GridChain

/-- The half-turn intertwines the simply blocked differentials with the blocked marking transported
along `Fin.rev`. -/
@[simp]
theorem simplyBlockedDifferential_rotate_simplyBlockedHalfTurnEquiv
    (c : GridChainHat R n i) :
    G.rotate.simplyBlockedDifferential R (i.rev) (simplyBlockedHalfTurnEquiv R i c) =
      simplyBlockedHalfTurnEquiv R i (G.simplyBlockedDifferential R i c) := by
  obtain ⟨c, rfl⟩ := simplyBlockedSpecialization_surjective R i c
  rw [← simplyBlockedSpecialization_halfTurnRenameEquiv,
    ← simplyBlockedSpecialization_unblockedDifferential,
    unblockedDifferential_rotate_halfTurnRenameEquiv,
    simplyBlockedSpecialization_halfTurnRenameEquiv,
    simplyBlockedSpecialization_unblockedDifferential]

end GridDiagram

end TauCeti

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*) [CommSemiring R]
    (i : Fin n)

/-- Half-turn preserves and reflects membership in each chain bidegree. -/
-- Simplify before membership expands into its monomial characterization.
@[simp↓]
theorem simplyBlockedHalfTurnEquiv_mem_bigradedChainHatPiece_iff
    {g : ℤ × ℤ} {c : GridChainHat R n i} :
    GridChain.simplyBlockedHalfTurnEquiv R i c ∈ G.rotate.bigradedChainHatPiece R i.rev g ↔
      c ∈ G.bigradedChainHatPiece R i g := by
  constructor
  · intro hc
    obtain ⟨b, hb, he⟩ := G.rotate.mem_bigradedChainHatPiece_iff_exists.mp hc
    have hinv := congrArg (GridChain.simplyBlockedHalfTurnEquiv R i).symm he
    rw [LinearEquiv.symm_apply_apply,
      GridChain.simplyBlockedHalfTurnEquiv_symm_specialization] at hinv
    rw [← hinv]
    apply G.simplyBlockedSpecialization_mem_bigradedChainHatPiece
    simpa only [rotate_rotate] using
      G.rotate.halfTurnRenameEquiv_mem_bigradedChainMinusPiece R hb
  · intro hc
    obtain ⟨b, hb, rfl⟩ := G.mem_bigradedChainHatPiece_iff_exists.mp hc
    rw [← GridChain.simplyBlockedSpecialization_halfTurnRenameEquiv]
    exact G.rotate.simplyBlockedSpecialization_mem_bigradedChainHatPiece i.rev
      (G.halfTurnRenameEquiv_mem_bigradedChainMinusPiece R hb)

/-- Inverse half-turn preserves and reflects membership in each chain bidegree. -/
@[simp↓]
theorem simplyBlockedHalfTurnEquiv_symm_mem_bigradedChainHatPiece_iff
    {g : ℤ × ℤ} {c : GridChainHat R n i.rev} :
    (GridChain.simplyBlockedHalfTurnEquiv R i).symm c ∈ G.bigradedChainHatPiece R i g ↔
      c ∈ G.rotate.bigradedChainHatPiece R i.rev g := by
  rw [← G.simplyBlockedHalfTurnEquiv_mem_bigradedChainHatPiece_iff R i,
    LinearEquiv.apply_symm_apply]

end TauCeti.OddComponentGridDiagram
