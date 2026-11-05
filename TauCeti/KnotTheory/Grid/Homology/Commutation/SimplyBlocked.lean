/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.SimplyBlocked
public import TauCeti.KnotTheory.Grid.Commutation.Components
public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked
import TauCeti.Algebra.CharP.Two
import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Equation

/-!
# The commutation map on simply blocked grid homology

For a knot grid, the specialized pentagon map induces a specified semilinear map on `G-hat`.
The chosen blocked marking is transported by the column transposition, and the coefficient
ring is the polynomial ring on the remaining columns. The cycle-class formula retains the
underlying pentagon map, rather than only asserting existence of a homology map.

The construction uses the existing categorical chain identifications and cycles-modulo-boundaries
presentation of simply blocked homology.

This map is bijective, so `G-hat` is invariant under column commutation. The argument lifts
simply blocked chains to the unblocked complex `GC⁻`, where the pentagon map `Φ` of a commutation
and the pentagon map `Ψ` of the reverse commutation are chain maps whose composites are homotopic
to the identity through the hexagon maps
(`GridDiagram.unblockedDifferential_commutationHomotopy_add_eq` and
`GridDiagram.unblockedDifferential_commutationHomotopy_reverse_add_eq`). It then specializes
back. Specialization at `V_i = 0` kills exactly the multiples of `V_i`, and every map involved is
linear over the polynomial ring or semilinear along the column transposition, which carries `V_i`
to `V_{σ i}`. So each error term of an unblocked identity specializes to zero once the blocked
variable divides it. In particular the specialized maps of `Ψ` and of the hexagon maps never have
to be compared across the identification of the doubly commuted diagram with the original one.

## Main definitions

* `TauCeti.GridDiagram.IsKnot.simplyBlockedHomologyCommutationMap`: the map induced on `G-hat`
  by the pentagon map of a column commutation.
* `TauCeti.GridDiagram.IsKnot.simplyBlockedHomologyCommutationEquiv`: the same map as a
  semilinear equivalence.

## Main results

* `TauCeti.GridDiagram.IsKnot.simplyBlockedHomologyCommutationMap_bijective`: **commutation
  invariance of `G-hat`**, the commutation map on simply blocked grid homology is bijective.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.1;
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

open CategoryTheory

namespace TauCeti.GridDiagram

/-! ### Specializing the homotopy equations -/

section Chain

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]
  (C : ColumnCommutationData G) (i : Fin n)

local notation "σ" => Equiv.swap C.column (finRotate n C.column)
local notation "G'" => G.swapColumns C.column (finRotate n C.column)

omit [CharP R 2] in
/-- The pentagon map of the reverse commutation carries multiples of `V_{σ i}` to multiples of
`V_i`. -/
private theorem commutationMap_reverse_X_smul (Q : GridChainMinus R n) :
    (G').commutationMap R C.reverse ((MvPolynomial.X (σ i) : MvPolynomial (Fin n) R) • Q) =
      (MvPolynomial.X i : MvPolynomial (Fin n) R) • (G').commutationMap R C.reverse Q := by
  rw [LinearMap.map_smulₛₗ]
  simp

/-- If the boundary of an unblocked chain `Z` vanishes at `V_i = 0`, and its pentagon image `Φ Z`
is a boundary at `V_{σ i} = 0`, then `Z` itself is a boundary at `V_i = 0`. -/
private theorem simplyBlockedSpecialization_mem_range_of_commutationMap
    {Z : GridChainMinus R n}
    (hZ : simplyBlockedSpecialization R i (G.unblockedDifferential R Z) = 0)
    (hΦ : simplyBlockedSpecialization R (σ i) (G.commutationMap R C Z) ∈
      LinearMap.range ((G').simplyBlockedDifferential R (σ i))) :
    simplyBlockedSpecialization R i Z ∈ LinearMap.range (G.simplyBlockedDifferential R i) := by
  obtain ⟨P, hP⟩ := (exact_X_smul_simplyBlockedSpecialization R i _).mp hZ
  obtain ⟨w, hw⟩ := hΦ
  obtain ⟨W, rfl⟩ := simplyBlockedSpecialization_surjective R (σ i) w
  rw [← simplyBlockedSpecialization_unblockedDifferential, eq_comm, ← sub_eq_zero, ← map_sub] at hw
  obtain ⟨Q, hQ⟩ : ∃ Q, (MvPolynomial.X (σ i) : MvPolynomial (Fin n) R) • Q = _ :=
    (exact_X_smul_simplyBlockedSpecialization R (σ i) _).mp hw
  -- In `GC⁻(G)`, `∂ (H Z - Ψ W) = Z + V_i • (Ψ Q - H P)`, by the homotopy equation of `C`.
  have hΦZ : G.commutationMap R C Z = (G').unblockedDifferential R W +
      (MvPolynomial.X (σ i) : MvPolynomial (Fin n) R) • Q := by
    rw [hQ, add_sub_cancel]
  have hΨ := LinearMap.congr_fun (G.commutationMap_reverse_comp_unblockedDifferential R C) W
  simp only [LinearMap.comp_apply] at hΨ
  have hH := G.unblockedDifferential_commutationHomotopy_add_eq C R Z
  rw [← hP, LinearMap.map_smul, hΦZ, map_add, commutationMap_reverse_X_smul, hΨ] at hH
  have key : G.unblockedDifferential R
        (G.commutationHomotopy R C Z - (G').commutationMap R C.reverse W) =
      Z + (MvPolynomial.X i : MvPolynomial (Fin n) R) •
        ((G').commutationMap R C.reverse Q - G.commutationHomotopy R C P) := by
    rw [map_sub, smul_sub, eq_sub_of_add_eq hH]
    abel
  refine ⟨simplyBlockedSpecialization R i
    (G.commutationHomotopy R C Z - (G').commutationMap R C.reverse W), ?_⟩
  rw [← simplyBlockedSpecialization_unblockedDifferential, key, map_add,
    simplyBlockedSpecialization_X_smul, add_zero]

/-- If the boundary of an unblocked chain `Y` of the commuted diagram vanishes at `V_{σ i} = 0`,
then the boundary of its image `Ψ Y` under the reverse pentagon map vanishes at `V_i = 0`. -/
private theorem simplyBlockedSpecialization_unblockedDifferential_commutationMap_reverse
    {Y : GridChainMinus R n}
    (hY : simplyBlockedSpecialization R (σ i) ((G').unblockedDifferential R Y) = 0) :
    simplyBlockedSpecialization R i
      (G.unblockedDifferential R ((G').commutationMap R C.reverse Y)) = 0 := by
  obtain ⟨P, hP⟩ := (exact_X_smul_simplyBlockedSpecialization R (σ i) _).mp hY
  have hΨ := LinearMap.congr_fun (G.commutationMap_reverse_comp_unblockedDifferential R C) Y
  simp only [LinearMap.comp_apply] at hΨ
  rw [← hΨ, ← hP, commutationMap_reverse_X_smul]
  exact simplyBlockedSpecialization_X_smul R i _

/-- If the boundary of an unblocked chain `Y` of the commuted diagram vanishes at
`V_{σ i} = 0`, then at `V_{σ i} = 0` the round trip `Φ Ψ Y` differs from `Y` by a boundary. -/
private theorem simplyBlockedSpecialization_commutationMap_commutationMap_reverse_sub_mem_range
    {Y : GridChainMinus R n}
    (hY : simplyBlockedSpecialization R (σ i) ((G').unblockedDifferential R Y) = 0) :
    simplyBlockedSpecialization R (σ i)
        (G.commutationMap R C ((G').commutationMap R C.reverse Y)) -
      simplyBlockedSpecialization R (σ i) Y ∈
        LinearMap.range ((G').simplyBlockedDifferential R (σ i)) := by
  obtain ⟨P, hP⟩ := (exact_X_smul_simplyBlockedSpecialization R (σ i) _).mp hY
  -- In `GC⁻(G')`, `Φ Ψ Y - Y = ∂' (H' Y) + V_{σ i} • H' P`, by the homotopy equation of the
  -- reverse commutation in characteristic two.
  have hH := G.unblockedDifferential_commutationHomotopy_reverse_add_eq C R Y
  rw [← hP, LinearMap.map_smul] at hH
  have key : G.commutationMap R C ((G').commutationMap R C.reverse Y) - Y =
      (G').unblockedDifferential R ((G').commutationHomotopy R C.reverse Y) +
        (MvPolynomial.X (σ i) : MvPolynomial (Fin n) R) •
          (G').commutationHomotopy R C.reverse P := by
    calc G.commutationMap R C ((G').commutationMap R C.reverse Y) - Y
        = (Y + G.commutationMap R C ((G').commutationMap R C.reverse Y)) - (Y + Y) := by abel
      _ = _ := by rw [← hH, add_self_eq_zero_of_charTwo (MvPolynomial (Fin n) R) Y, sub_zero]
  refine ⟨simplyBlockedSpecialization R (σ i) ((G').commutationHomotopy R C.reverse Y), ?_⟩
  rw [← simplyBlockedSpecialization_unblockedDifferential, ← map_sub, key, map_add,
    simplyBlockedSpecialization_X_smul, add_zero]

end Chain

end TauCeti.GridDiagram

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
theorem simplyBlockedHomologyCommutationMap_oneVariableSpecializationHomologyClass
    (z : hG.simplyBlockedCycles R i) :
    hG.simplyBlockedHomologyCommutationMap R C i (G.oneVariableSpecializationHomologyClass R i z) =
      (G').oneVariableSpecializationHomologyClass R (σ i)
        (hG.simplyBlockedCommutationCyclesMap R C i z) := by
  simp only [simplyBlockedHomologyCommutationMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_eq]
  -- Pass through the categorical isomorphisms to the explicit quotient classes.
  rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply,
    simplyBlockedHomologyIsoQuotient_hom_class, simplyBlockedHomologyIsoQuotient_hom_class,
    Submodule.mapQ_apply]

/-! ### Invariance of `G-hat` under commutation -/

/-- **Commutation invariance of `G-hat`.** The map induced on simply blocked grid homology by the
pentagon map of a validated column commutation is bijective. -/
theorem simplyBlockedHomologyCommutationMap_bijective :
    Function.Bijective (hG.simplyBlockedHomologyCommutationMap R C i) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun y hy => ?_, fun y => ?_⟩
  · -- A cycle whose pentagon image is a boundary is a boundary.
    obtain ⟨z, rfl⟩ := G.oneVariableSpecializationHomologyClass_surjective R i y
    rw [simplyBlockedHomologyCommutationMap_oneVariableSpecializationHomologyClass,
      oneVariableSpecializationHomologyClass_eq_zero_iff,
      (G').mem_range_moduleCatToCycles_simplyBlockedComplex_iff R (σ i),
      simplyBlockedChainEquiv_simplyBlockedCommutationCyclesMap] at hy
    have hz := (G.mem_ker_simplyBlockedComplex_d_iff R i z).mp z.2
    obtain ⟨Z, hZ⟩ := simplyBlockedSpecialization_surjective R i (G.simplyBlockedChainEquiv R i z)
    rw [← hZ, simplyBlockedCommutationMap_simplyBlockedSpecialization] at hy
    rw [← hZ, ← simplyBlockedSpecialization_unblockedDifferential] at hz
    rw [oneVariableSpecializationHomologyClass_eq_zero_iff,
      G.mem_range_moduleCatToCycles_simplyBlockedComplex_iff R i, ← hZ]
    exact G.simplyBlockedSpecialization_mem_range_of_commutationMap R C i hz hy
  · -- The class of a cycle `y` of the commuted diagram is the image of the class of `Ψ y`.
    obtain ⟨y, rfl⟩ := (G').oneVariableSpecializationHomologyClass_surjective R (σ i) y
    have hy := ((G').mem_ker_simplyBlockedComplex_d_iff R (σ i) y).mp y.2
    obtain ⟨Y, hY⟩ :=
      simplyBlockedSpecialization_surjective R (σ i) ((G').simplyBlockedChainEquiv R (σ i) y)
    rw [← hY, ← simplyBlockedSpecialization_unblockedDifferential] at hy
    let z : hG.simplyBlockedCycles R i :=
      ⟨(G.simplyBlockedChainEquiv R i).symm
        (simplyBlockedSpecialization R i ((G').commutationMap R C.reverse Y)), by
        rw [G.mem_ker_simplyBlockedComplex_d_iff R i, LinearEquiv.apply_symm_apply,
          ← simplyBlockedSpecialization_unblockedDifferential]
        exact G.simplyBlockedSpecialization_unblockedDifferential_commutationMap_reverse R C i hy⟩
    refine ⟨G.oneVariableSpecializationHomologyClass R i z, ?_⟩
    rw [simplyBlockedHomologyCommutationMap_oneVariableSpecializationHomologyClass,
      oneVariableSpecializationHomologyClass_eq_iff,
      (G').mem_range_moduleCatToCycles_simplyBlockedComplex_iff R (σ i), Submodule.coe_sub,
      map_sub, simplyBlockedChainEquiv_simplyBlockedCommutationCyclesMap, ← hY,
      LinearEquiv.apply_symm_apply, simplyBlockedCommutationMap_simplyBlockedSpecialization]
    exact G.simplyBlockedSpecialization_commutationMap_commutationMap_reverse_sub_mem_range R C i hy

/-- The commutation map on simply blocked grid homology, as a semilinear equivalence along the
renaming of the surviving variables by the column transposition. -/
noncomputable def simplyBlockedHomologyCommutationEquiv :
    hG.simplyBlockedHomology R i ≃ₛₗ[((simplyBlockedRenameEquiv R σ i).toRingEquiv :
      MvPolynomial {c : Fin n // c ≠ i} R →+*
        MvPolynomial {c : Fin n // c ≠ σ i} R)] (hG').simplyBlockedHomology R (σ i) :=
  LinearEquiv.ofBijective (hG.simplyBlockedHomologyCommutationMap R C i)
    (hG.simplyBlockedHomologyCommutationMap_bijective R C i)

/-- The commutation equivalence on simply blocked grid homology is the commutation map. -/
@[simp]
theorem coe_simplyBlockedHomologyCommutationEquiv :
    ⇑(hG.simplyBlockedHomologyCommutationEquiv R C i) =
      hG.simplyBlockedHomologyCommutationMap R C i :=
  (rfl)

end TauCeti.GridDiagram.IsKnot
