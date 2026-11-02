/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Stabilization.Homology
public import TauCeti.KnotTheory.Grid.SimplyBlocked

/-!
# The simply blocked stabilization chain map

An `X`-stabilization inserts a new `O`-marking and carries each old `O`-marking to its
inserted column. Blocking one of those old markings specializes the unblocked stabilization
map to a semilinear chain map. Its scalar homomorphism first merges the two stabilization
variables and then kills the chosen old variable; it need not be a renaming of variables.

The specialization identity characterizes the map on all chains and proves that it commutes
with the differentials. These constructions apply to arbitrary grid diagrams. For knots,
blocking one `O`-marking gives the simply blocked theory.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.2;
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*,
Section 3.2 (arXiv:math/0610559).
-/

public section

open MvPolynomial

namespace TauCeti.GridDiagram

variable {n : ℕ} (s i : Fin n) (R : Type*)

section Semiring

variable [CommSemiring R]

local notation "j" => s.castSucc.succAbove i
local notation "A" => MvPolynomial {c : Fin n // c ≠ i} R
local notation "S" => MvPolynomial {c : Fin (n + 1) // c ≠ j} R

/-- The coefficient homomorphism of stabilization after blocking the transported old marking.
Merge the stabilization columns using `s.predAbove`, then kill the variable of column `i`. -/
noncomputable def simplyBlockedStabilizeXRingHom : S →+* A :=
  (simplyBlockedRingHom R i).comp
    ((rename (R := R) s.predAbove).toRingHom.comp (rename Subtype.val).toRingHom)

/-- A surviving source variable is merged and then specialized in the old grid. In particular,
when `i = s`, the other variable of the stabilization block also maps to zero. -/
@[simp]
theorem simplyBlockedStabilizeXRingHom_X (c : {c : Fin (n + 1) // c ≠ j}) :
    simplyBlockedStabilizeXRingHom s i R (MvPolynomial.X c) =
      simplyBlockedRingHom R i (MvPolynomial.X (s.predAbove c)) := by
  simp [simplyBlockedStabilizeXRingHom]

/-- Stabilization leaves ground-ring coefficients unchanged after blocking. -/
@[simp]
theorem simplyBlockedStabilizeXRingHom_C (r : R) :
    simplyBlockedStabilizeXRingHom s i R (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [simplyBlockedStabilizeXRingHom]

/-- Merging columns commutes with blocking the transported old marking. -/
theorem simplyBlockedStabilizeXRingHom_specialization (p : MvPolynomial (Fin (n + 1)) R) :
    simplyBlockedStabilizeXRingHom s i R (simplyBlockedRingHom R j p) =
      simplyBlockedRingHom R i (rename s.predAbove p) := by
  have h : ((killCompl (R := R) (f := (Subtype.val : {c : Fin n // c ≠ i} → Fin n))
      Subtype.val_injective).comp ((rename s.predAbove).comp (rename Subtype.val))).comp
        (killCompl (f := (Subtype.val : {c : Fin (n + 1) // c ≠ j} → Fin (n + 1)))
          Subtype.val_injective) =
      (killCompl (f := (Subtype.val : {c : Fin n // c ≠ i} → Fin n))
        Subtype.val_injective).comp (rename s.predAbove) := by
    ext c
    by_cases hc : c = j
    · subst c
      simp [Fin.predAbove_succAbove]
    · have hX : MvPolynomial.X c = rename Subtype.val
          (MvPolynomial.X (R := R) (⟨c, hc⟩ : {c : Fin (n + 1) // c ≠ j})) := by simp
      simp only [AlgHom.comp_apply]
      rw [hX, killCompl_rename_app]
  exact DFunLike.congr_fun h p

end Semiring

variable (G : GridDiagram n) [CommRing R]

local notation "j" => s.castSucc.succAbove i
local notation "A" => MvPolynomial {c : Fin n // c ≠ i} R
local notation "S" => MvPolynomial {c : Fin (n + 1) // c ≠ j} R

/-- The stabilization comparison with the transported old `O`-marking blocked. Its image on a
generator is the specialization of the unblocked stabilization comparison. -/
noncomputable def simplyBlockedStabilizeXMap :
    GridChainHat R (n + 1) j →ₛₗ[simplyBlockedStabilizeXRingHom s i R] GridChainHat R n i :=
  (Finsupp.linearCombination A fun x : GridState (n + 1) =>
    simplyBlockedSpecialization R i (G.stabilizeXChainMap s R (Finsupp.single x 1))).comp
      (Finsupp.mapRange.linearMap (simplyBlockedStabilizeXRingHom s i R).toSemilinearMap)

/-- The specialized stabilization map on a single supported coefficient. -/
theorem simplyBlockedStabilizeXMap_single (x : GridState (n + 1)) (p : S) :
    G.simplyBlockedStabilizeXMap s i R (Finsupp.single x p) =
      simplyBlockedStabilizeXRingHom s i R p •
        simplyBlockedSpecialization R i (G.stabilizeXChainMap s R (Finsupp.single x 1)) := by
  simp [simplyBlockedStabilizeXMap]

/-- The matrix formula for the specialized stabilization comparison. -/
@[simp]
theorem simplyBlockedStabilizeXMap_apply_apply (c : GridChainHat R (n + 1) j)
    (y : GridState n) :
    G.simplyBlockedStabilizeXMap s i R c y = c.sum fun x p =>
      simplyBlockedStabilizeXRingHom s i R p *
        simplyBlockedRingHom R i (G.stabilizeXChainMap s R (Finsupp.single x 1) y) := by
  induction c using Finsupp.induction_linear with
  | zero => rw [map_zero, Finsupp.zero_apply, Finsupp.sum_zero_index]
  | add c d hc hd =>
    rw [map_add, Finsupp.add_apply, hc, hd, Finsupp.sum_add_index'] <;> simp [add_mul]
  | single x p =>
    rw [simplyBlockedStabilizeXMap_single, Finsupp.smul_apply, smul_eq_mul,
      simplyBlockedSpecialization_apply, ← simplyBlockedRingHom_apply,
      Finsupp.sum_single_index (by simp)]

/-- The simply blocked comparison is the descent of the unblocked stabilization map through
coefficient specialization. -/
@[simp]
theorem simplyBlockedStabilizeXMap_simplyBlockedSpecialization (c : GridChainMinus R (n + 1)) :
    G.simplyBlockedStabilizeXMap s i R (simplyBlockedSpecialization R j c) =
      simplyBlockedSpecialization R i (G.stabilizeXChainMap s R c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add, hc, hd]
  | single x p =>
    rw [simplyBlockedSpecialization_single, simplyBlockedStabilizeXMap_single,
      ← simplyBlockedRingHom_apply, simplyBlockedStabilizeXRingHom_specialization,
      ← Finsupp.smul_single_one x p, map_smulₛₗ, map_smulₛₗ]
    rfl

variable [CharP R 2]

/-- Stabilization commutes with the simply blocked differentials. -/
theorem simplyBlockedStabilizeXMap_simplyBlockedDifferential (c : GridChainHat R (n + 1) j) :
    G.simplyBlockedStabilizeXMap s i R
        ((G.stabilizeX s.castSucc (G.X s).castSucc s).simplyBlockedDifferential R j c) =
      G.simplyBlockedDifferential R i (G.simplyBlockedStabilizeXMap s i R c) := by
  obtain ⟨c, rfl⟩ := simplyBlockedSpecialization_surjective R j c
  rw [← simplyBlockedSpecialization_unblockedDifferential,
    simplyBlockedStabilizeXMap_simplyBlockedSpecialization,
    simplyBlockedStabilizeXMap_simplyBlockedSpecialization,
    ← simplyBlockedSpecialization_unblockedDifferential,
    stabilizeXChainMap_unblockedDifferential]

end TauCeti.GridDiagram
