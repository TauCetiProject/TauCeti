/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.SimplyBlocked
public import TauCeti.KnotTheory.Grid.Commutation.Components
public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked

/-!
# The commutation map on simply blocked grid homology

For a knot grid, the specialized pentagon map induces a specified semilinear map on `G-hat`.
The chosen blocked marking is transported by the column transposition, and the coefficient
ring is the polynomial ring on the remaining columns. The cycle-class formula retains the
underlying pentagon map, rather than only asserting existence of a homology map.

The construction uses the existing categorical chain identifications and cycles-modulo-boundaries
presentation of simply blocked homology. Invertibility additionally needs the hexagon homotopy
identities.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.1;
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

open CategoryTheory

namespace TauCeti.GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot)
  (R : Type*) [CommRing R] [CharP R 2] (C : ColumnCommutationData G) (i : Fin n)

local notation "σ" => Equiv.swap C.column (finRotate n C.column)
local notation "G'" => G.swapColumns C.column (finRotate n C.column)
local notation "hG'" => C.isColumnCommutation.isKnot_iff.mpr hG

/-- The specialized pentagon map between the categorical chain carriers. -/
private noncomputable def simplyBlockedCommutationChainMap :
    (G.simplyBlockedComplex R i).X () →ₛₗ[((simplyBlockedRenameEquiv R σ i).toRingEquiv :
      MvPolynomial {c : Fin n // c ≠ i} R →+*
        MvPolynomial {c : Fin n // c ≠ σ i} R)] ((G').simplyBlockedComplex R (σ i)).X () :=
  ((G').simplyBlockedChainEquiv R (σ i)).symm.toLinearMap.comp
    ((G.simplyBlockedCommutationMap R C i).comp (G.simplyBlockedChainEquiv R i).toLinearMap)

private theorem simplyBlockedCommutationChainMap_d
    (z : (G.simplyBlockedComplex R i).X ()) :
    simplyBlockedCommutationChainMap R C i ((G.simplyBlockedComplex R i).d () () z) =
      ((G').simplyBlockedComplex R (σ i)).d () ()
        (simplyBlockedCommutationChainMap R C i z) := by
  apply ((G').simplyBlockedChainEquiv R (σ i)).injective
  simp only [simplyBlockedCommutationChainMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, GridDiagram.simplyBlockedChainEquiv_d]
  exact G.simplyBlockedCommutationMap_simplyBlockedDifferential R C i _

/-- The pentagon comparison on simply blocked cycles, transporting the blocked marking. -/
noncomputable def simplyBlockedCommutationCyclesMap :
    hG.simplyBlockedCycles R i →ₛₗ[((simplyBlockedRenameEquiv R σ i).toRingEquiv :
      MvPolynomial {c : Fin n // c ≠ i} R →+*
        MvPolynomial {c : Fin n // c ≠ σ i} R)] (hG').simplyBlockedCycles R (σ i) :=
  (simplyBlockedCommutationChainMap R C i).restrict fun z hz => by
    rw [LinearMap.mem_ker] at hz ⊢
    rw [← simplyBlockedCommutationChainMap_d, hz, map_zero]

/-- Under the explicit chain identifications, the map of cycles is the specialized pentagon map. -/
@[simp]
theorem simplyBlockedChainEquiv_simplyBlockedCommutationCyclesMap
    (z : hG.simplyBlockedCycles R i) :
    (G').simplyBlockedChainEquiv R (σ i) (hG.simplyBlockedCommutationCyclesMap R C i z) =
      G.simplyBlockedCommutationMap R C i (G.simplyBlockedChainEquiv R i z) := by
  simp only [simplyBlockedCommutationCyclesMap, LinearMap.coe_restrict_apply,
    simplyBlockedCommutationChainMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

private theorem simplyBlockedCommutationCyclesMap_mem_boundaries
    {z : hG.simplyBlockedCycles R i} (hz : z ∈ hG.simplyBlockedBoundaries R i) :
    hG.simplyBlockedCommutationCyclesMap R C i z ∈ (hG').simplyBlockedBoundaries R (σ i) := by
  obtain ⟨w, rfl⟩ := hz
  refine ⟨simplyBlockedCommutationChainMap R C i w, ?_⟩
  apply Subtype.ext
  exact (simplyBlockedCommutationChainMap_d R C i w).symm

/-- The specified semilinear commutation map on simply blocked knot grid homology. -/
noncomputable def simplyBlockedHomologyCommutationMap :
    hG.simplyBlockedHomology R i →ₛₗ[((simplyBlockedRenameEquiv R σ i).toRingEquiv :
      MvPolynomial {c : Fin n // c ≠ i} R →+*
        MvPolynomial {c : Fin n // c ≠ σ i} R)] (hG').simplyBlockedHomology R (σ i) :=
  ((hG').simplyBlockedHomologyIsoQuotient R (σ i)).toLinearEquiv.symm.toLinearMap.comp
    ((Submodule.mapQ (hG.simplyBlockedBoundaries R i)
      ((hG').simplyBlockedBoundaries R (σ i)) (hG.simplyBlockedCommutationCyclesMap R C i)
      (fun _ hz => hG.simplyBlockedCommutationCyclesMap_mem_boundaries R C i hz)).comp
        (hG.simplyBlockedHomologyIsoQuotient R i).toLinearEquiv.toLinearMap)

/-- The commutation map takes a cycle class to the class of its specified pentagon image. -/
@[simp]
theorem simplyBlockedHomologyCommutationMap_simplyBlockedHomologyClass
    (z : hG.simplyBlockedCycles R i) :
    hG.simplyBlockedHomologyCommutationMap R C i (hG.simplyBlockedHomologyClass R i z) =
      (hG').simplyBlockedHomologyClass R (σ i) (hG.simplyBlockedCommutationCyclesMap R C i z) := by
  simp only [simplyBlockedHomologyCommutationMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_eq]
  -- Pass through the categorical isomorphisms to the explicit quotient classes.
  rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply,
    simplyBlockedHomologyIsoQuotient_hom_class, simplyBlockedHomologyIsoQuotient_hom_class,
    Submodule.mapQ_apply]

end TauCeti.GridDiagram.IsKnot
