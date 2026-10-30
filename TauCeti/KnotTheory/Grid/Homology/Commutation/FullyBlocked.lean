/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.FullyBlocked
public import TauCeti.KnotTheory.Grid.Homology.Basic

/-!
# The commutation map on fully blocked grid homology

The fully blocked pentagon chain map induces a specified map on fully blocked homology: the class
of a cycle is sent to the class of its pentagon image. This uses `LinearMap.homologyMap` through the
identification with the kernel modulo the image of the differential. The hexagon homotopy
identities are additionally needed to show that the map is invertible.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

local notation "G'" => G.swapColumns C.column (finRotate n C.column)

/-- The fully blocked pentagon map sends cycles to cycles. -/
theorem fullyBlockedCommutationMap_mem_cycles {z : GridChain (ZMod 2) n}
    (hz : z ∈ G.fullyBlockedCycles) :
    G.fullyBlockedCommutationMap (ZMod 2) C z ∈ (G').fullyBlockedCycles := by
  rw [mem_fullyBlockedCycles] at hz ⊢
  have h := LinearMap.congr_fun (G.fullyBlockedCommutationMap_comp_fullyBlockedDifferential C) z
  simpa only [LinearMap.comp_apply, hz, map_zero] using h.symm

/-- The specified map on fully blocked homology induced by counting empty pentagons avoiding
all markings. -/
noncomputable def fullyBlockedHomologyCommutationMap :
    G.fullyBlockedHomology →ₗ[ZMod 2] (G').fullyBlockedHomology :=
  (G').fullyBlockedHomologyEquivLinearMapHomology.symm.toLinearMap.comp
    ((LinearMap.homologyMap (G.fullyBlockedCommutationMap (ZMod 2) C)
      G.fullyBlockedDifferential_comp_self_eq_zero
      (G').fullyBlockedDifferential_comp_self_eq_zero
      (G.fullyBlockedCommutationMap_comp_fullyBlockedDifferential C)).comp
        G.fullyBlockedHomologyEquivLinearMapHomology.toLinearMap)

/-- A cycle class is sent to the class of its fully blocked pentagon image. -/
@[simp]
theorem fullyBlockedHomologyCommutationMap_mk (z : G.fullyBlockedCycles) :
    G.fullyBlockedHomologyCommutationMap C (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk
        (⟨G.fullyBlockedCommutationMap (ZMod 2) C z,
          G.fullyBlockedCommutationMap_mem_cycles C z.2⟩ : (G').fullyBlockedCycles) := by
  simp only [fullyBlockedHomologyCommutationMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    fullyBlockedHomologyEquivLinearMapHomology_mk, LinearMap.homologyMap_mk,
    fullyBlockedHomologyEquivLinearMapHomology_symm_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  simp only [LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply]

end TauCeti.GridDiagram
