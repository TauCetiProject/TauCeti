/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Stabilization.SimplyBlocked.Basic
public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked.Basic

/-!
# The stabilization map on simply blocked knot grid homology

The specialized `X`-stabilization chain map induces a specified semilinear map on `G-hat`.
The blocked marking is an old `O`-marking carried into the stabilized diagram. On coefficients,
the map merges the stabilization variables and kills the chosen variable. On homology, it
takes a cycle class to the class of its stabilization image.

This file constructs that comparison, including its action on cycles and boundaries; it does
not assert invertibility or grading compatibility.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.2;
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*,
Section 3.2 (arXiv:math/0610559).
-/

public section

open CategoryTheory

namespace TauCeti.GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (s i : Fin n)
  (R : Type*) [CommRing R] [CharP R 2]

local notation "j" => s.castSucc.succAbove i
local notation "G'" => GridDiagram.stabilizeX G (Fin.castSucc s)
  (Fin.castSucc (GridDiagram.X G s)) s
local notation "hG'" => Iff.mpr
  (GridDiagram.isKnot_stabilizeX G (Fin.castSucc s) (Fin.castSucc (GridDiagram.X G s)) s) hG

/-- The specialized stabilization map between the categorical chain carriers. -/
private noncomputable def simplyBlockedStabilizeXChainMap :
    ((G').simplyBlockedComplex R j).X () →ₛₗ[simplyBlockedStabilizeXRingHom s i R]
      (G.simplyBlockedComplex R i).X () :=
  (G.simplyBlockedChainEquiv R i).symm.toLinearMap.comp
    ((G.simplyBlockedStabilizeXMap s i R).comp
      ((G').simplyBlockedChainEquiv R j).toLinearMap)

private theorem simplyBlockedStabilizeXChainMap_d
    (z : ((G').simplyBlockedComplex R j).X ()) :
    simplyBlockedStabilizeXChainMap s i R (((G').simplyBlockedComplex R j).d () () z) =
      (G.simplyBlockedComplex R i).d () () (simplyBlockedStabilizeXChainMap s i R z) := by
  apply (G.simplyBlockedChainEquiv R i).injective
  simp only [simplyBlockedStabilizeXChainMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, GridDiagram.simplyBlockedChainEquiv_d]
  exact G.simplyBlockedStabilizeXMap_simplyBlockedDifferential s i R _

/-- Stabilization on simply blocked cycles, with the chosen old marking blocked in each grid. -/
noncomputable def simplyBlockedStabilizeXCyclesMap :
    (hG').simplyBlockedCycles R j →ₛₗ[simplyBlockedStabilizeXRingHom s i R]
      hG.simplyBlockedCycles R i :=
  (simplyBlockedStabilizeXChainMap s i R).restrict fun z hz => by
    rw [LinearMap.mem_ker] at hz ⊢
    rw [← simplyBlockedStabilizeXChainMap_d, hz, map_zero]

/-- Under the explicit chain identifications, the map on cycles is the specialized
stabilization map. -/
@[simp]
theorem simplyBlockedChainEquiv_simplyBlockedStabilizeXCyclesMap
    (z : (hG').simplyBlockedCycles R j) :
    G.simplyBlockedChainEquiv R i (hG.simplyBlockedStabilizeXCyclesMap s i R z) =
      G.simplyBlockedStabilizeXMap s i R ((G').simplyBlockedChainEquiv R j z) := by
  simp only [simplyBlockedStabilizeXCyclesMap, LinearMap.coe_restrict_apply,
    simplyBlockedStabilizeXChainMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

private theorem simplyBlockedStabilizeXCyclesMap_mem_boundaries
    {z : (hG').simplyBlockedCycles R j} (hz : z ∈ (hG').simplyBlockedBoundaries R j) :
    hG.simplyBlockedStabilizeXCyclesMap s i R z ∈ hG.simplyBlockedBoundaries R i := by
  obtain ⟨w, rfl⟩ := hz
  refine ⟨simplyBlockedStabilizeXChainMap s i R w, ?_⟩
  apply Subtype.ext
  exact (simplyBlockedStabilizeXChainMap_d s i R w).symm

/-- The specified semilinear stabilization comparison on simply blocked knot grid homology,
from the stabilized grid to the old grid. -/
noncomputable def simplyBlockedStabilizeXHomologyMap :
    (hG').simplyBlockedHomology R j →ₛₗ[simplyBlockedStabilizeXRingHom s i R]
      hG.simplyBlockedHomology R i :=
  (hG.simplyBlockedHomologyIsoQuotient R i).toLinearEquiv.symm.toLinearMap.comp
    ((Submodule.mapQ ((hG').simplyBlockedBoundaries R j)
      (hG.simplyBlockedBoundaries R i) (hG.simplyBlockedStabilizeXCyclesMap s i R)
      (fun _ hz => hG.simplyBlockedStabilizeXCyclesMap_mem_boundaries s i R hz)).comp
        ((hG').simplyBlockedHomologyIsoQuotient R j).toLinearEquiv.toLinearMap)

/-- The stabilization comparison takes a cycle class to the class of its specified
stabilization image. -/
@[simp]
theorem simplyBlockedStabilizeXHomologyMap_oneVariableSpecializationHomologyClass
    (z : (hG').simplyBlockedCycles R j) :
    hG.simplyBlockedStabilizeXHomologyMap s i R
        ((G').oneVariableSpecializationHomologyClass R j z) =
      G.oneVariableSpecializationHomologyClass R i
        (hG.simplyBlockedStabilizeXCyclesMap s i R z) := by
  simp only [simplyBlockedStabilizeXHomologyMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_eq]
  -- Pass through the categorical isomorphisms to the explicit quotient classes.
  rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply,
    simplyBlockedHomologyIsoQuotient_hom_class, simplyBlockedHomologyIsoQuotient_hom_class,
    Submodule.mapQ_apply]

end TauCeti.GridDiagram.IsKnot
