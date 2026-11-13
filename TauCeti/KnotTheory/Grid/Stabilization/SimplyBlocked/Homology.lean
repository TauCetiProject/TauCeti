/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.KnotTheory.Grid.Stabilization.SimplyBlocked.Basic
public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked.Basic
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
one-variable specialization—and hence of `G-hat` for a knot grid—under this `X`-stabilization.
Bijectivity is deduced from stabilization invariance of `GH⁻` via the morphism of short exact
sequences `0 → GC⁻ --V--> GC⁻ → GC^ → 0`
(`GridDiagram.exists_sub_simplyBlockedStabilizeXMap_mem_range` and
`GridDiagram.mem_range_of_simplyBlockedStabilizeXMap_mem_range`). Since the coefficient homomorphism
`simplyBlockedStabilizeXRingHom` fixes ground-ring scalars, restricting scalars along
`MvPolynomial.C` packages the bijection as an `R`-linear equivalence
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

/-- **Stabilization invariance for the one-variable specialization.** For any grid diagram `G`, the
stabilization map from the homology of the specialization `V_{s.castSucc.succAbove i} = 0` of `G'`
to the homology of the specialization `V_i = 0` of `G` is bijective. -/
theorem oneVariableSpecializationStabilizeXHomologyMap_bijective :
    Function.Bijective (G.oneVariableSpecializationStabilizeXHomologyMap s i R) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun y hy => ?_, fun y => ?_⟩
  · -- A cycle whose stabilization image is a boundary is a boundary.
    obtain ⟨z, rfl⟩ := (G').oneVariableSpecializationHomologyClass_surjective R j y
    rw [oneVariableSpecializationStabilizeXHomologyMap_oneVariableSpecializationHomologyClass,
      oneVariableSpecializationHomologyClass_eq_zero_iff,
      mem_range_moduleCatToCycles_simplyBlockedComplex_iff,
      simplyBlockedChainEquiv_oneVariableSpecializationStabilizeXCyclesMap] at hy
    rw [oneVariableSpecializationHomologyClass_eq_zero_iff,
      mem_range_moduleCatToCycles_simplyBlockedComplex_iff]
    exact G.mem_range_of_simplyBlockedStabilizeXMap_mem_range s i R
      (((G').mem_ker_simplyBlockedComplex_d_iff R j z.1).mp z.2) hy
  · -- Every cycle differs from the stabilization image of a cycle by a boundary.
    obtain ⟨y, rfl⟩ := G.oneVariableSpecializationHomologyClass_surjective R i y
    obtain ⟨x, hx, hxy⟩ := G.exists_sub_simplyBlockedStabilizeXMap_mem_range s i R
      ((G.mem_ker_simplyBlockedComplex_d_iff R i y.1).mp y.2)
    let z : LinearMap.ker (((G').simplyBlockedComplex R j).d () ()).hom :=
      ⟨((G').simplyBlockedChainEquiv R j).symm x, by
        rw [mem_ker_simplyBlockedComplex_d_iff, LinearEquiv.apply_symm_apply]
        exact hx⟩
    refine ⟨(G').oneVariableSpecializationHomologyClass R j z, ?_⟩
    rw [oneVariableSpecializationStabilizeXHomologyMap_oneVariableSpecializationHomologyClass,
      oneVariableSpecializationHomologyClass_eq_iff,
      mem_range_moduleCatToCycles_simplyBlockedComplex_iff, Submodule.coe_sub, map_sub,
      simplyBlockedChainEquiv_oneVariableSpecializationStabilizeXCyclesMap,
      LinearEquiv.apply_symm_apply, ← neg_sub]
    exact neg_mem hxy

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
