/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.KnotTheory.Grid.Stabilization.SimplyBlocked.Basic
public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked
import TauCeti.Algebra.Homology.SquareZero

/-!
# Stabilization invariance of simply blocked grid homology

Let `G` be a grid diagram of size `n`, let `s` and `i` be columns of `G`, and let
`G' = G.stabilizeX s.castSucc (G.X s).castSucc s` be the stabilization splitting the `X`-marking of
column `s`, with `j = s.castSucc.succAbove i` the column of `G'` carrying the old `O`-marking of
column `i`. The specialized `X`-stabilization chain map `GridDiagram.simplyBlockedStabilizeXMap`
merges the two variables of the stabilization block along `s.predAbove` and sets `V_i` to zero.

This file descends that chain map to a specified semilinear map on the homology of the one-variable
specialization for any grid diagram (`GridDiagram.oneVariableSpecializationStabilizeXHomologyMap`),
sending each cycle class to the class of its stabilization image. For a knot grid (`G.IsKnot`), the
one-variable specialization is simply blocked grid homology `G-hat`
(`GridDiagram.IsKnot.simplyBlockedHomology`), so these declarations apply directly to `G-hat`.

It then proves that this map is bijective
(`oneVariableSpecializationStabilizeXHomologyMap_bijective`), establishing invariance of the
one-variable specialization—and hence of `G-hat` for a knot grid—under this `X`-stabilization. The
proof lifts specialized chains to `GC⁻`, where specialization at `V_j = 0` or `V_i = 0` has kernel
equal to the multiples of that variable, multiplication by a variable is injective, and
`GridDiagram.stabilizeXChainMap` induces a bijection on unblocked homology
(`GridDiagram.stabilizeXHomologyMap_bijective`) while carrying `V_j`-multiples to `V_i`-multiples.
Since the coefficient homomorphism `simplyBlockedStabilizeXRingHom` fixes ground-ring scalars,
restricting scalars along `MvPolynomial.C` packages the bijection as an `R`-linear equivalence
(`oneVariableSpecializationStabilizeXHomologyEquiv`). Bigrading compatibility is treated in
`TauCeti.KnotTheory.Grid.Stabilization.SimplyBlocked.Bigraded`.

## Main definitions

* `TauCeti.GridDiagram.oneVariableSpecializationStabilizeXCyclesMap` and
  `TauCeti.GridDiagram.oneVariableSpecializationStabilizeXHomologyMap`: the stabilization
  comparisons on cycles and homology of the one-variable specialization of an arbitrary grid.
* `TauCeti.GridDiagram.oneVariableSpecializationStabilizeXHomologyEquiv`: the homology comparison
  as an `R`-linear equivalence after restricting scalars to the ground ring.

## Main results

* `TauCeti.GridDiagram.oneVariableSpecializationStabilizeXHomologyMap_bijective`: **stabilization
  invariance for the one-variable specialization** (and therefore of `G-hat` for a knot grid) under
  the south-west corner `X`-stabilization.

## References

* Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.2.
* Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*,
  Section 3.2 (arXiv:math/0610559).
-/

public section

open CategoryTheory

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (s i : Fin n)
  (R : Type*) [CommRing R] [CharP R 2]

local notation "j" => Fin.succAbove (Fin.castSucc s) i
local notation "G'" => GridDiagram.stabilizeX G (Fin.castSucc s)
  (Fin.castSucc (GridDiagram.X G s)) s
local notation "A" => MvPolynomial {c : Fin n // c ≠ i} R
local notation "S" => MvPolynomial {c : Fin (n + 1) // c ≠ j} R

/-- The specialized stabilization map between the categorical chain carriers. -/
private noncomputable def oneVariableSpecializationStabilizeXChainMap :
    ((G').simplyBlockedComplex R j).X () →ₛₗ[simplyBlockedStabilizeXRingHom s i R]
      (G.simplyBlockedComplex R i).X () :=
  (G.simplyBlockedChainEquiv R i).symm.toLinearMap.comp
    ((G.simplyBlockedStabilizeXMap s i R).comp
      ((G').simplyBlockedChainEquiv R j).toLinearMap)

private theorem oneVariableSpecializationStabilizeXChainMap_d
    (z : ((G').simplyBlockedComplex R j).X ()) :
    oneVariableSpecializationStabilizeXChainMap G s i R
        (((G').simplyBlockedComplex R j).d () () z) =
      (G.simplyBlockedComplex R i).d () ()
        (oneVariableSpecializationStabilizeXChainMap G s i R z) := by
  apply (G.simplyBlockedChainEquiv R i).injective
  simp only [oneVariableSpecializationStabilizeXChainMap, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, simplyBlockedChainEquiv_d]
  exact G.simplyBlockedStabilizeXMap_simplyBlockedDifferential s i R _

/-- Stabilization on cycles of the one-variable specialization, with the chosen old `O`-marking
blocked in each diagram. -/
noncomputable def oneVariableSpecializationStabilizeXCyclesMap :
    LinearMap.ker (((G').simplyBlockedComplex R j).d () ()).hom
      →ₛₗ[simplyBlockedStabilizeXRingHom s i R]
      LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom :=
  (oneVariableSpecializationStabilizeXChainMap G s i R).restrict fun z hz => by
    rw [LinearMap.mem_ker] at hz ⊢
    rw [← oneVariableSpecializationStabilizeXChainMap_d, hz, map_zero]

/-- Under the explicit chain identifications, the map on cycles of the one-variable specialization
is `simplyBlockedStabilizeXMap`. -/
@[simp]
theorem simplyBlockedChainEquiv_oneVariableSpecializationStabilizeXCyclesMap
    (z : LinearMap.ker (((G').simplyBlockedComplex R j).d () ()).hom) :
    G.simplyBlockedChainEquiv R i (G.oneVariableSpecializationStabilizeXCyclesMap s i R z) =
      G.simplyBlockedStabilizeXMap s i R ((G').simplyBlockedChainEquiv R j z) := by
  simp only [oneVariableSpecializationStabilizeXCyclesMap, LinearMap.coe_restrict_apply,
    oneVariableSpecializationStabilizeXChainMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

private theorem oneVariableSpecializationStabilizeXCyclesMap_mem_boundariesInKer
    {z : LinearMap.ker (((G').simplyBlockedComplex R j).d () ()).hom}
    (hz : z ∈ (((G').simplyBlockedComplex R j).d () ()).hom.boundariesInKer) :
    G.oneVariableSpecializationStabilizeXCyclesMap s i R z ∈
      ((G.simplyBlockedComplex R i).d () ()).hom.boundariesInKer := by
  obtain ⟨w, hw⟩ := hz
  refine ⟨oneVariableSpecializationStabilizeXChainMap G s i R w, ?_⟩
  simp only [Submodule.subtype_apply, oneVariableSpecializationStabilizeXCyclesMap,
    LinearMap.coe_restrict_apply] at hw ⊢
  rw [← hw, oneVariableSpecializationStabilizeXChainMap_d]

/-- The specified semilinear stabilization comparison on the homology of the one-variable
specialization, from the stabilized grid to the original grid. -/
noncomputable def oneVariableSpecializationStabilizeXHomologyMap :
    ((G').simplyBlockedComplex R j).homology () →ₛₗ[simplyBlockedStabilizeXRingHom s i R]
      (G.simplyBlockedComplex R i).homology () :=
  (G.simplyBlockedComplex R i).moduleCatHomologyIso.toLinearEquiv.symm.toLinearMap.comp
    ((Submodule.mapQ
      (((G').simplyBlockedComplex R j).d () ()).hom.boundariesInKer
      ((G.simplyBlockedComplex R i).d () ()).hom.boundariesInKer
      (G.oneVariableSpecializationStabilizeXCyclesMap s i R)
      (fun _ hz =>
        G.oneVariableSpecializationStabilizeXCyclesMap_mem_boundariesInKer s i R hz)).comp
          ((G').simplyBlockedComplex R j).moduleCatHomologyIso.toLinearEquiv.toLinearMap)

/-- The stabilization comparison on the one-variable specialization sends a cycle class to the class
of its stabilization image. -/
@[simp]
theorem oneVariableSpecializationStabilizeXHomologyMap_oneVariableSpecializationHomologyClass
    (z : LinearMap.ker (((G').simplyBlockedComplex R j).d () ()).hom) :
    G.oneVariableSpecializationStabilizeXHomologyMap s i R
        ((G').oneVariableSpecializationHomologyClass R j z) =
      G.oneVariableSpecializationHomologyClass R i
        (G.oneVariableSpecializationStabilizeXCyclesMap s i R z) := by
  simp only [oneVariableSpecializationStabilizeXHomologyMap, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_eq]
  rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply,
    HomologicalComplex.moduleCatHomologyIso_hom_moduleCatKerHomologyClass,
    HomologicalComplex.moduleCatHomologyIso_hom_moduleCatKerHomologyClass,
    LinearMap.homologyπ_apply, LinearMap.homologyπ_apply, Submodule.mapQ_apply]

/-! ### Bijectivity via unblocked chain lifting -/

/-- If an unblocked chain `Z'` of `G'` becomes a cycle at `V_j = 0` and its stabilization image
becomes a boundary at `V_i = 0`, then `Z'` is already a boundary at `V_j = 0`. -/
private theorem simplyBlockedSpecialization_mem_range_of_stabilizeXChainMap
    {Z' : GridChainMinus R (n + 1)}
    (hZ' : simplyBlockedSpecialization R j ((G').unblockedDifferential R Z') = 0)
    (hS : simplyBlockedSpecialization R i (G.stabilizeXChainMap s R Z') ∈
      LinearMap.range (G.simplyBlockedDifferential R i)) :
    simplyBlockedSpecialization R j Z' ∈
      LinearMap.range ((G').simplyBlockedDifferential R j) := by
  obtain ⟨P', hP'⟩ : ∃ P', (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) • P' = _ :=
    (exact_X_smul_simplyBlockedSpecialization R j _).mp hZ'
  obtain ⟨w, hw⟩ := hS
  obtain ⟨W, rfl⟩ := simplyBlockedSpecialization_surjective R i w
  rw [← G.simplyBlockedSpecialization_unblockedDifferential R i W, eq_comm,
    ← sub_eq_zero, ← map_sub] at hw
  obtain ⟨Q, hQ⟩ : ∃ Q, (MvPolynomial.X i : MvPolynomial (Fin n) R) • Q = _ :=
    (exact_X_smul_simplyBlockedSpecialization R i _).mp hw
  have hSZ' : G.stabilizeXChainMap s R Z' =
      G.unblockedDifferential R W + (MvPolynomial.X i : MvPolynomial (Fin n) R) • Q := by
    rw [hQ, add_sub_cancel]
  -- Since `∂' Z' = V_j • P'` and `∂'² = 0`, regularity of `V_j` shows `P'` is an unblocked cycle.
  have hdP' : P' ∈ LinearMap.ker ((G').unblockedDifferential R) :=
    (G').mem_ker_unblockedDifferential_of_X_smul_eq R hP'
  -- Applying `S` to `∂' Z' = V_j • P'` and comparing with `∂ (S Z')` shows `S P' = ∂ Q`.
  have hSP' : G.stabilizeXChainMap s R P' = G.unblockedDifferential R Q := by
    have hdW : G.unblockedDifferential R (G.unblockedDifferential R W) = 0 :=
      LinearMap.congr_fun (G.unblockedDifferential_comp_self_eq_zero R) W
    refine X_smul_gridChainMinus_injective R i ?_
    dsimp only
    calc (MvPolynomial.X i : MvPolynomial (Fin n) R) • G.stabilizeXChainMap s R P'
        = G.stabilizeXChainMap s R
            ((MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) • P') := by
          rw [G.stabilizeXChainMap_X_smul, Fin.predAbove_succAbove]
      _ = G.unblockedDifferential R (G.stabilizeXChainMap s R Z') := by
          rw [hP', G.stabilizeXChainMap_unblockedDifferential]
      _ = (MvPolynomial.X i : MvPolynomial (Fin n) R) • G.unblockedDifferential R Q := by
          rw [hSZ', map_add, LinearMap.map_smul, hdW, zero_add]
  obtain ⟨R', hR'⟩ :=
    G.mem_range_of_stabilizeXChainMap_mem_range s R hdP' ⟨Q, hSP'.symm⟩
  -- Correct `Q` by `S R'` to obtain a cycle in `GC⁻(G)`, then lift its class to `M' ∈ ker ∂'`.
  have hdQ : Q - G.stabilizeXChainMap s R R' ∈ LinearMap.ker (G.unblockedDifferential R) := by
    rw [LinearMap.mem_ker, map_sub, ← G.stabilizeXChainMap_unblockedDifferential, hR',
      hSP', sub_self]
  obtain ⟨M', hM', U, hU⟩ :=
    G.exists_sub_stabilizeXChainMap_mem_range s R hdQ
  -- Subtracting `V_j • (R' + M')` does not change the specialization at `V_j = 0`, and turns `Z'`
  -- into an unblocked cycle whose image in `GC⁻(G)` is a boundary.
  let Z₀' := Z' - (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) • (R' + M')
  have hdZ₀' : Z₀' ∈ LinearMap.ker ((G').unblockedDifferential R) := by
    rw [LinearMap.mem_ker, map_sub, LinearMap.map_smul, map_add, hR',
      LinearMap.mem_ker.mp hM', add_zero, hP', sub_self]
  have hSZ₀' : G.stabilizeXChainMap s R Z₀' ∈ LinearMap.range (G.unblockedDifferential R) := by
    refine ⟨W + (MvPolynomial.X i : MvPolynomial (Fin n) R) • U, ?_⟩
    rw [map_add, LinearMap.map_smul, hU]
    simp only [Z₀', map_sub, G.stabilizeXChainMap_X_smul, Fin.predAbove_succAbove, map_add,
      hSZ', smul_sub, smul_add]
    abel
  obtain ⟨W', hW'⟩ :=
    G.mem_range_of_stabilizeXChainMap_mem_range s R hdZ₀' hSZ₀'
  refine ⟨simplyBlockedSpecialization R j W', ?_⟩
  rw [← (G').simplyBlockedSpecialization_unblockedDifferential R j W', hW']
  simp only [Z₀', map_sub, simplyBlockedSpecialization_X_smul, sub_zero]

/-- Every unblocked chain `Z` of `G` whose differential vanishes at `V_i = 0` is homologous at
`V_i = 0` to the stabilization image of an unblocked chain `Y'` of `G'` whose differential vanishes
at `V_j = 0`. -/
private theorem exists_simplyBlockedSpecialization_stabilizeXChainMap_sub_mem_range
    {Z : GridChainMinus R n}
    (hZ : simplyBlockedSpecialization R i (G.unblockedDifferential R Z) = 0) :
    ∃ Y' : GridChainMinus R (n + 1),
      simplyBlockedSpecialization R j ((G').unblockedDifferential R Y') = 0 ∧
        simplyBlockedSpecialization R i Z -
          simplyBlockedSpecialization R i (G.stabilizeXChainMap s R Y') ∈
            LinearMap.range (G.simplyBlockedDifferential R i) := by
  obtain ⟨P, hP⟩ : ∃ P, (MvPolynomial.X i : MvPolynomial (Fin n) R) • P = _ :=
    (exact_X_smul_simplyBlockedSpecialization R i _).mp hZ
  have hdP : P ∈ LinearMap.ker (G.unblockedDifferential R) :=
    G.mem_ker_unblockedDifferential_of_X_smul_eq R hP
  obtain ⟨M', hM', U, hU⟩ :=
    G.exists_sub_stabilizeXChainMap_mem_range s R hdP
  -- The cycle `V_j • M'` maps to `V_i • S M' = ∂ (Z - V_i • U)`, so it is an unblocked boundary
  -- `∂' C'`; then `C'` is a cycle at `V_j = 0`.
  have hdXM' : (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) • M' ∈
      LinearMap.ker ((G').unblockedDifferential R) := by
    rw [LinearMap.mem_ker, LinearMap.map_smul, LinearMap.mem_ker.mp hM', smul_zero]
  have hSXM' : G.stabilizeXChainMap s R
      ((MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) • M') ∈
        LinearMap.range (G.unblockedDifferential R) := by
    refine ⟨Z - (MvPolynomial.X i : MvPolynomial (Fin n) R) • U, ?_⟩
    rw [map_sub, LinearMap.map_smul, hU, smul_sub, hP, G.stabilizeXChainMap_X_smul,
      Fin.predAbove_succAbove]
    abel
  obtain ⟨C', hC'⟩ :=
    G.mem_range_of_stabilizeXChainMap_mem_range s R hdXM' hSXM'
  have hdZ' : (Z - (MvPolynomial.X i : MvPolynomial (Fin n) R) • U) -
      G.stabilizeXChainMap s R C' ∈ LinearMap.ker (G.unblockedDifferential R) := by
    rw [LinearMap.mem_ker, map_sub, ← G.stabilizeXChainMap_unblockedDifferential, hC',
      map_sub, LinearMap.map_smul, hU, smul_sub, hP, G.stabilizeXChainMap_X_smul,
      Fin.predAbove_succAbove]
    abel
  obtain ⟨N', hN', V, hV⟩ :=
    G.exists_sub_stabilizeXChainMap_mem_range s R hdZ'
  refine ⟨C' + N', ?_, simplyBlockedSpecialization R i V, ?_⟩
  · rw [map_add, hC', LinearMap.mem_ker.mp hN', add_zero, simplyBlockedSpecialization_X_smul]
  · rw [← G.simplyBlockedSpecialization_unblockedDifferential R i V, hV]
    simp only [map_sub, map_add, simplyBlockedSpecialization_X_smul, sub_zero]
    abel

/-- **Stabilization invariance for the one-variable specialization.** For any grid diagram `G`, the
stabilization map from the homology of the specialization `V_{s.castSucc.succAbove i} = 0` of `G'`
to the homology of the specialization `V_i = 0` of `G` is bijective. -/
theorem oneVariableSpecializationStabilizeXHomologyMap_bijective :
    Function.Bijective (G.oneVariableSpecializationStabilizeXHomologyMap s i R) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun y hy => ?_, fun y => ?_⟩
  · obtain ⟨z, rfl⟩ := (G').oneVariableSpecializationHomologyClass_surjective R j y
    rw [oneVariableSpecializationStabilizeXHomologyMap_oneVariableSpecializationHomologyClass,
      oneVariableSpecializationHomologyClass_eq_zero_iff,
      mem_range_moduleCatToCycles_simplyBlockedComplex_iff,
      simplyBlockedChainEquiv_oneVariableSpecializationStabilizeXCyclesMap] at hy
    have hz := ((G').mem_ker_simplyBlockedComplex_d_iff R j z.1).mp z.2
    obtain ⟨Z', hZ'⟩ :=
      simplyBlockedSpecialization_surjective R j ((G').simplyBlockedChainEquiv R j z)
    rw [← hZ', simplyBlockedStabilizeXMap_simplyBlockedSpecialization] at hy
    rw [← hZ', ← simplyBlockedSpecialization_unblockedDifferential] at hz
    rw [oneVariableSpecializationHomologyClass_eq_zero_iff,
      mem_range_moduleCatToCycles_simplyBlockedComplex_iff, ← hZ']
    exact G.simplyBlockedSpecialization_mem_range_of_stabilizeXChainMap s i R hz hy
  · obtain ⟨z, rfl⟩ := G.oneVariableSpecializationHomologyClass_surjective R i y
    have hz := (G.mem_ker_simplyBlockedComplex_d_iff R i z.1).mp z.2
    obtain ⟨Z, hZ⟩ :=
      simplyBlockedSpecialization_surjective R i (G.simplyBlockedChainEquiv R i z)
    rw [← hZ, ← simplyBlockedSpecialization_unblockedDifferential] at hz
    obtain ⟨Y', hY', hdiff⟩ :=
      G.exists_simplyBlockedSpecialization_stabilizeXChainMap_sub_mem_range s i R hz
    let y' : LinearMap.ker (((G').simplyBlockedComplex R j).d () ()).hom :=
      ⟨((G').simplyBlockedChainEquiv R j).symm (simplyBlockedSpecialization R j Y'), by
        rw [mem_ker_simplyBlockedComplex_d_iff, LinearEquiv.apply_symm_apply,
          ← simplyBlockedSpecialization_unblockedDifferential]
        exact hY'⟩
    refine ⟨(G').oneVariableSpecializationHomologyClass R j y', ?_⟩
    rw [oneVariableSpecializationStabilizeXHomologyMap_oneVariableSpecializationHomologyClass,
      oneVariableSpecializationHomologyClass_eq_iff,
      mem_range_moduleCatToCycles_simplyBlockedComplex_iff, Submodule.coe_sub, map_sub,
      simplyBlockedChainEquiv_oneVariableSpecializationStabilizeXCyclesMap,
      LinearEquiv.apply_symm_apply, simplyBlockedStabilizeXMap_simplyBlockedSpecialization,
      ← hZ, ← neg_sub]
    exact neg_mem hdiff

/-- The stabilization comparison on the homology of the one-variable specialization, packaged as an
`R`-linear equivalence by restricting scalars along `MvPolynomial.C`. -/
noncomputable def oneVariableSpecializationStabilizeXHomologyEquiv :
    (ModuleCat.restrictScalars (MvPolynomial.C : R →+* S)).obj
        (((G').simplyBlockedComplex R j).homology ()) ≃ₗ[R]
      (ModuleCat.restrictScalars (MvPolynomial.C : R →+* A)).obj
        ((G.simplyBlockedComplex R i).homology ()) :=
  LinearEquiv.ofBijective
    ({ toFun := G.oneVariableSpecializationStabilizeXHomologyMap s i R
       map_add' := map_add _
       map_smul' := fun r y => by
         have h := (G.oneVariableSpecializationStabilizeXHomologyMap s i R).map_smulₛₗ
           (MvPolynomial.C r) y
         rwa [simplyBlockedStabilizeXRingHom_C] at h } :
      (ModuleCat.restrictScalars (MvPolynomial.C : R →+* S)).obj
          (((G').simplyBlockedComplex R j).homology ()) →ₗ[R]
        (ModuleCat.restrictScalars (MvPolynomial.C : R →+* A)).obj
          ((G.simplyBlockedComplex R i).homology ()))
    (G.oneVariableSpecializationStabilizeXHomologyMap_bijective s i R)

/-- On elements, `oneVariableSpecializationStabilizeXHomologyEquiv` is the semilinear stabilization
comparison. -/
@[simp]
theorem oneVariableSpecializationStabilizeXHomologyEquiv_apply
    (y : (ModuleCat.restrictScalars (MvPolynomial.C : R →+* S)).obj
      (((G').simplyBlockedComplex R j).homology ())) :
    G.oneVariableSpecializationStabilizeXHomologyEquiv s i R y =
      G.oneVariableSpecializationStabilizeXHomologyMap s i R y :=
  (rfl)

end TauCeti.GridDiagram
