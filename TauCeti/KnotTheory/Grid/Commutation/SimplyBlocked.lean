/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.Residual.Assembly
public import TauCeti.KnotTheory.Grid.SimplyBlocked

/-!
# The simply blocked commutation chain map

A column commutation carries the `O`-marking in column `i` to column `σ i`, where `σ` is the
transposition of the commuted columns. Setting its variable to zero in the unblocked pentagon
map gives a semilinear map between the polynomial modules on the surviving columns. Both
terminal-side and initial-side pentagons contribute, and those covering the blocked marking
have zero weight. The specialization identity specifies this map on every chain, and the
unblocked chain-map identity descends through the surjective specialization.

The construction applies to one-variable specializations of arbitrary grid diagrams. For a
knot grid, blocking one marking is the simply blocked theory `G-hat`. Invertibility still requires
the hexagon homotopy identities.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.1;
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559). The map specializes the unblocked pentagon map in
`TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Basic`.
-/

public section

open MvPolynomial

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommSemiring R]
  (C : ColumnCommutationData G) (i : Fin n)

local notation "σ" => Equiv.swap C.column (finRotate n C.column)
local notation "S" => MvPolynomial {c : Fin n // c ≠ σ i} R

/-- The pentagon map after blocking the `O`-marking in column `i`. Its scalar homomorphism
renames the surviving variables by the column transposition. -/
noncomputable def simplyBlockedCommutationMap :
    GridChainHat R n i →ₛₗ[((simplyBlockedRenameEquiv R σ i).toRingEquiv :
      MvPolynomial {c : Fin n // c ≠ i} R →+* S)] GridChainHat R n (σ i) :=
  (Finsupp.linearCombination S fun x : GridState n =>
    simplyBlockedSpecialization R (σ i) (G.commutationMap R C (Finsupp.single x 1))).comp
      (Finsupp.mapRange.linearMap
        ((simplyBlockedRenameEquiv R σ i).toRingEquiv :
          MvPolynomial {c : Fin n // c ≠ i} R →+* S).toSemilinearMap)

/-- On a generator, the specialized map reads the pentagon coefficient with the transported
blocked variable set to zero. -/
theorem simplyBlockedCommutationMap_single_apply (x y : GridState n)
    (p : MvPolynomial {c : Fin n // c ≠ i} R) :
    G.simplyBlockedCommutationMap R C i (Finsupp.single x p) y =
      simplyBlockedRenameEquiv R σ i p *
        simplyBlockedRingHom R (σ i) (G.commutationPentagonCoefficient R C x y) := by
  simp only [simplyBlockedCommutationMap, LinearMap.comp_apply,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
    RingHom.coe_toSemilinearMap, Finsupp.linearCombination_single,
    Finsupp.smul_apply, smul_eq_mul, simplyBlockedSpecialization_apply,
    G.commutationMap_single_apply, RingHom.coe_coe, AlgEquiv.coe_toRingEquiv,
    simplyBlockedRingHom_apply]

/-- The matrix formula on an arbitrary simply blocked chain. -/
@[simp]
theorem simplyBlockedCommutationMap_apply_apply (c : GridChainHat R n i) (y : GridState n) :
    G.simplyBlockedCommutationMap R C i c y = c.sum fun x p =>
      simplyBlockedRenameEquiv R σ i p *
        simplyBlockedRingHom R (σ i) (G.commutationPentagonCoefficient R C x y) := by
  induction c using Finsupp.induction_linear with
  | zero => rw [map_zero, Finsupp.zero_apply, Finsupp.sum_zero_index]
  | add c d hc hd =>
    rw [map_add, Finsupp.add_apply, hc, hd, Finsupp.sum_add_index'] <;>
      simp [add_mul]
  | single x p =>
    rw [simplyBlockedCommutationMap_single_apply, Finsupp.sum_single_index (by simp)]

/-- Coefficient specialization intertwines the unblocked and simply blocked pentagon maps,
including when the blocked column is one of the commuted columns. -/
@[simp]
theorem simplyBlockedCommutationMap_simplyBlockedSpecialization (c : GridChainMinus R n) :
    G.simplyBlockedCommutationMap R C i (simplyBlockedSpecialization R i c) =
      simplyBlockedSpecialization R (σ i) (G.commutationMap R C c) := by
  induction c using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add c d hc hd => rw [map_add, map_add, map_add, map_add, hc, hd]
  | single x p =>
    apply Finsupp.ext
    intro y
    rw [simplyBlockedSpecialization_single, simplyBlockedCommutationMap_single_apply,
      simplyBlockedSpecialization_apply, ← Finsupp.smul_single_one x p, map_smulₛₗ,
      Finsupp.smul_apply, smul_eq_mul]
    rw [map_mul, G.commutationMap_single_apply]
    simpa only [RingHom.coe_coe, AlgEquiv.coe_toRingEquiv, renameEquiv_apply,
      simplyBlockedRingHom_apply] using
      congrArg (· * simplyBlockedRingHom R (σ i)
        (G.commutationPentagonCoefficient R C x y))
          (simplyBlockedRingHom_rename R σ i p).symm

variable [CharP R 2]

/-- The simply blocked pentagon map intertwines the differentials. The blocked marking in the
target is the image of the chosen marking under the column transposition. -/
theorem simplyBlockedCommutationMap_simplyBlockedDifferential (c : GridChainHat R n i) :
    G.simplyBlockedCommutationMap R C i (G.simplyBlockedDifferential R i c) =
      (G.swapColumns C.column (finRotate n C.column)).simplyBlockedDifferential R (σ i)
        (G.simplyBlockedCommutationMap R C i c) := by
  obtain ⟨c, rfl⟩ := simplyBlockedSpecialization_surjective R i c
  rw [← simplyBlockedSpecialization_unblockedDifferential,
    simplyBlockedCommutationMap_simplyBlockedSpecialization,
    simplyBlockedCommutationMap_simplyBlockedSpecialization,
    ← simplyBlockedSpecialization_unblockedDifferential]
  exact congrArg (simplyBlockedSpecialization R (σ i))
    (LinearMap.congr_fun (G.commutationMap_comp_unblockedDifferential C R) c)

end TauCeti.GridDiagram
