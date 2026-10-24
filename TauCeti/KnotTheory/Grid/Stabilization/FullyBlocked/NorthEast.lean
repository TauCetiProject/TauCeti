/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.HalfTurn
public import TauCeti.KnotTheory.Grid.Stabilization.FullyBlocked.Basic

/-!
# The fully blocked north-east stabilization comparison

The fully blocked homology of a north-east `X`-stabilization is two copies of the original
homology. The specified comparison is obtained by conjugating the south-west comparison by
the half-turn of the torus. Its action on cycle classes is recorded explicitly, so the result
is a comparison map, not just equality of dimensions.

These are ungraded equivalences. The two copies account for the stabilization factor;
this file does not identify them as a bigraded tensor product.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.2 and the grid
symmetries of Chapter 3; Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer
homology*, Section 3.2. The construction uses `fullyBlockedHomologyStabilizeXEquivProd` and
the half-turn equivalence, without a second mapping-cone argument.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

local notation "F" => ZMod 2
local notation "T" => GridChain.halfTurnEquiv F
local notation "G'" => G.stabilizeX (Fin.succ s) (Fin.succ (G.X s)) s
local notation "H" => G.rotate.stabilizeX (Fin.castSucc (Fin.rev s))
  (Fin.castSucc (G.rotate.X (Fin.rev s))) (Fin.rev s)

/-- The north-east fully blocked comparison, conjugated from the south-west one by half-turns.
The first and second components retain the order of the south-west comparison. -/
noncomputable def fullyBlockedStabilizeXSuccMap :
    GridChain F (n + 1) →ₗ[F] GridChain F n × GridChain F n :=
  ((T).toLinearMap.prodMap (T).toLinearMap) ∘ₗ
    G.rotate.fullyBlockedStabilizeXMap s.rev ∘ₗ (T).toLinearMap

/-- The two components of the north-east comparison are half-turned south-west components. -/
theorem fullyBlockedStabilizeXSuccMap_apply (c : GridChain F (n + 1)) :
    G.fullyBlockedStabilizeXSuccMap s c =
      (T (G.rotate.fullyBlockedStabilizeXMap s.rev (T c)).1,
        T (G.rotate.fullyBlockedStabilizeXMap s.rev (T c)).2) := (rfl)

private theorem fullyBlockedDifferential_stabilizeX_rotate_halfTurnEquiv
    (c : GridChain F (n + 1)) :
    (H).fullyBlockedDifferential (T c) = T ((G').fullyBlockedDifferential c) := by
  rw [← rotate_stabilizeX_succ]
  exact (G').fullyBlockedDifferential_rotate_halfTurnEquiv c

/-- The north-east comparison intertwines the fully blocked differentials. -/
theorem fullyBlockedStabilizeXSuccMap_comp_differential :
    G.fullyBlockedStabilizeXSuccMap s ∘ₗ (G').fullyBlockedDifferential =
      (G.fullyBlockedDifferential.prodMap G.fullyBlockedDifferential) ∘ₗ
        G.fullyBlockedStabilizeXSuccMap s := by
  refine LinearMap.ext fun c => ?_
  have h := LinearMap.congr_fun (G.rotate.fullyBlockedStabilizeXMap_comp_differential s.rev)
    (T c)
  simp only [LinearMap.comp_apply, LinearMap.prodMap_apply] at h
  simp only [LinearMap.comp_apply, fullyBlockedStabilizeXSuccMap_apply,
    LinearMap.prodMap_apply]
  rw [← G.fullyBlockedDifferential_stabilizeX_rotate_halfTurnEquiv s c, h]
  simp only [fullyBlockedDifferential_halfTurnEquiv]

/-- Rotation identifies cycles of the north-east stabilization with cycles of the south-west
stabilization of the rotated diagram. -/
private noncomputable def fullyBlockedStabilizeXSuccSourceCyclesEquiv :
    (G').fullyBlockedCycles ≃ₗ[F] (H).fullyBlockedCycles :=
  (G').fullyBlockedCyclesEquivOfIntertwining (H) T
    (G.fullyBlockedDifferential_stabilizeX_rotate_halfTurnEquiv s)

/-- The north-east comparison on cycles. Its components are cycles representing the two
homology summands. -/
noncomputable def fullyBlockedStabilizeXSuccCycles :
    (G').fullyBlockedCycles →ₗ[F] G.fullyBlockedCycles × G.fullyBlockedCycles :=
  let e := G.fullyBlockedCyclesEquivOfIntertwining G.rotate T
    G.fullyBlockedDifferential_rotate_halfTurnEquiv
  (e.symm.prodCongr e.symm).toLinearMap ∘ₗ
    G.rotate.fullyBlockedStabilizeXCycles s.rev ∘ₗ
      (G.fullyBlockedStabilizeXSuccSourceCyclesEquiv s).toLinearMap

/-- The first comparison cycle has the first chain-comparison component as its underlying chain. -/
@[simp]
theorem fullyBlockedStabilizeXSuccCycles_fst (z : (G').fullyBlockedCycles) :
    ((G.fullyBlockedStabilizeXSuccCycles s z).1 : GridChain F n) =
      (G.fullyBlockedStabilizeXSuccMap s z).1 := by
  dsimp only [fullyBlockedStabilizeXSuccCycles, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.prodCongr_apply]
  simp only [fullyBlockedCyclesEquivOfIntertwining_symm_apply,
    GridChain.halfTurnEquiv_symm, fullyBlockedStabilizeXSuccSourceCyclesEquiv,
    fullyBlockedCyclesEquivOfIntertwining_apply, fullyBlockedStabilizeXCycles_fst,
    fullyBlockedStabilizeXSuccMap_apply, fullyBlockedStabilizeXMap_fst]

/-- The second comparison cycle has the second chain-comparison component as its underlying
chain. -/
@[simp]
theorem fullyBlockedStabilizeXSuccCycles_snd (z : (G').fullyBlockedCycles) :
    ((G.fullyBlockedStabilizeXSuccCycles s z).2 : GridChain F n) =
      (G.fullyBlockedStabilizeXSuccMap s z).2 := by
  dsimp only [fullyBlockedStabilizeXSuccCycles, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.prodCongr_apply]
  simp only [fullyBlockedCyclesEquivOfIntertwining_symm_apply,
    GridChain.halfTurnEquiv_symm, fullyBlockedStabilizeXSuccSourceCyclesEquiv,
    fullyBlockedCyclesEquivOfIntertwining_apply, fullyBlockedStabilizeXCycles_snd,
    fullyBlockedStabilizeXSuccMap_apply, fullyBlockedStabilizeXMap_snd]

/-- The fully blocked north-east stabilization equivalence, with two copies of the original
homology. It is the rotated south-west comparison, rather than a choice of vector-space bases. -/
noncomputable def fullyBlockedHomologyStabilizeXSuccEquivProd :
    (G').fullyBlockedHomology ≃ₗ[F] G.fullyBlockedHomology × G.fullyBlockedHomology :=
  ((G').fullyBlockedHomologyEquivOfIntertwining (H) T
    (G.fullyBlockedDifferential_stabilizeX_rotate_halfTurnEquiv s)).trans
    ((G.rotate.fullyBlockedHomologyStabilizeXEquivProd s.rev).trans
      (G.fullyBlockedHomologyRotateEquiv.symm.prodCongr
        G.fullyBlockedHomologyRotateEquiv.symm))

/-- The stabilization equivalence sends a cycle class to the classes of its two comparison
cycles. -/
@[simp]
theorem fullyBlockedHomologyStabilizeXSuccEquivProd_mk (z : (G').fullyBlockedCycles) :
    G.fullyBlockedHomologyStabilizeXSuccEquivProd s (Submodule.Quotient.mk z) =
      (Submodule.Quotient.mk (G.fullyBlockedStabilizeXSuccCycles s z).1,
        Submodule.Quotient.mk (G.fullyBlockedStabilizeXSuccCycles s z).2) := by
  rw [fullyBlockedHomologyStabilizeXSuccEquivProd, LinearEquiv.trans_apply,
    fullyBlockedHomologyEquivOfIntertwining_apply_mk, LinearEquiv.trans_apply,
    fullyBlockedHomologyStabilizeXEquivProd_mk, LinearEquiv.prodCongr_apply,
    fullyBlockedHomologyRotateEquiv_symm_apply_mk,
    fullyBlockedHomologyRotateEquiv_symm_apply_mk]
  rfl

/-- A north-east `X`-stabilization doubles the dimension of fully blocked grid homology. -/
theorem finrank_fullyBlockedHomology_stabilizeX_succ :
    Module.finrank F (G').fullyBlockedHomology =
      2 * Module.finrank F G.fullyBlockedHomology := by
  rw [(G.fullyBlockedHomologyStabilizeXSuccEquivProd s).finrank_eq, Module.finrank_prod]
  omega

end TauCeti.GridDiagram
