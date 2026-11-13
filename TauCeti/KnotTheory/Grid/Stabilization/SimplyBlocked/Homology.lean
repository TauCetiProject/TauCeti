/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.KnotTheory.Grid.Stabilization.SimplyBlocked.Basic
public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked.Basic

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

/-- Stabilization on cycles of the one-variable specialization, with the chosen old `O`-marking
blocked in each diagram. -/
noncomputable def oneVariableSpecializationStabilizeXCyclesMap :
    LinearMap.ker (((G').simplyBlockedComplex R j).d () ()).hom
      →ₛₗ[simplyBlockedStabilizeXRingHom s i R]
      LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom :=
  oneVariableSpecializationCyclesMapOfIntertwining R j i (simplyBlockedStabilizeXRingHom s i R)
    (G.simplyBlockedStabilizeXMap s i R)
    (G.simplyBlockedStabilizeXMap_simplyBlockedDifferential s i R)

/-- Under the explicit chain identifications, the map on cycles of the one-variable specialization
is `simplyBlockedStabilizeXMap`. -/
@[simp]
theorem simplyBlockedChainEquiv_oneVariableSpecializationStabilizeXCyclesMap
    (z : LinearMap.ker (((G').simplyBlockedComplex R j).d () ()).hom) :
    G.simplyBlockedChainEquiv R i (G.oneVariableSpecializationStabilizeXCyclesMap s i R z) =
      G.simplyBlockedStabilizeXMap s i R ((G').simplyBlockedChainEquiv R j z) :=
  simplyBlockedChainEquiv_oneVariableSpecializationCyclesMapOfIntertwining
    R j i (simplyBlockedStabilizeXRingHom s i R)
    (G.simplyBlockedStabilizeXMap s i R)
    (G.simplyBlockedStabilizeXMap_simplyBlockedDifferential s i R) z

/-- The specified semilinear stabilization comparison on the homology of the one-variable
specialization, from the stabilized grid to the original grid. -/
noncomputable def oneVariableSpecializationStabilizeXHomologyMap :
    ((G').simplyBlockedComplex R j).homology () →ₛₗ[simplyBlockedStabilizeXRingHom s i R]
      (G.simplyBlockedComplex R i).homology () :=
  oneVariableSpecializationHomologyMapOfIntertwining
    R j i (simplyBlockedStabilizeXRingHom s i R)
    (G.simplyBlockedStabilizeXMap s i R)
    (G.simplyBlockedStabilizeXMap_simplyBlockedDifferential s i R)

/-- The stabilization comparison on the one-variable specialization sends a cycle class to the class
of its stabilization image. -/
@[simp]
theorem oneVariableSpecializationStabilizeXHomologyMap_oneVariableSpecializationHomologyClass
    (z : LinearMap.ker (((G').simplyBlockedComplex R j).d () ()).hom) :
    G.oneVariableSpecializationStabilizeXHomologyMap s i R
        ((G').oneVariableSpecializationHomologyClass R j z) =
      G.oneVariableSpecializationHomologyClass R i
        (G.oneVariableSpecializationStabilizeXCyclesMap s i R z) :=
  oneVariableSpecializationHomologyMapOfIntertwining_oneVariableSpecializationHomologyClass
    R j i (simplyBlockedStabilizeXRingHom s i R)
    (G.simplyBlockedStabilizeXMap s i R)
    (G.simplyBlockedStabilizeXMap_simplyBlockedDifferential s i R) z

/-- **Stabilization invariance for the one-variable specialization.** For any grid diagram `G`, the
stabilization map from the homology of the specialization `V_{s.castSucc.succAbove i} = 0` of `G'`
to the homology of the specialization `V_i = 0` of `G` is bijective. -/
theorem oneVariableSpecializationStabilizeXHomologyMap_bijective :
    Function.Bijective (G.oneVariableSpecializationStabilizeXHomologyMap s i R) := by
  apply oneVariableSpecializationHomologyMapOfIntertwining_bijective
    R j i (simplyBlockedStabilizeXRingHom s i R)
    (G.simplyBlockedStabilizeXMap s i R)
    (G.simplyBlockedStabilizeXMap_simplyBlockedDifferential s i R)
  · intro x hx hfx
    exact G.mem_range_of_simplyBlockedStabilizeXMap_mem_range s i R hx hfx
  · intro y hy
    exact G.exists_sub_simplyBlockedStabilizeXMap_mem_range s i R hy

/-- The stabilization comparison on the homology of the one-variable specialization, packaged as an
`R`-linear equivalence by restricting scalars along `MvPolynomial.C`. -/
noncomputable def oneVariableSpecializationStabilizeXHomologyEquiv :
    (ModuleCat.restrictScalars (MvPolynomial.C : R →+* S)).obj
        (((G').simplyBlockedComplex R j).homology ()) ≃ₗ[R]
      (ModuleCat.restrictScalars (MvPolynomial.C : R →+* A)).obj
        ((G.simplyBlockedComplex R i).homology ()) :=
  oneVariableSpecializationHomologyLinearEquivOfIntertwining
    R j i (simplyBlockedStabilizeXRingHom s i R)
    (G.simplyBlockedStabilizeXMap s i R)
    (G.simplyBlockedStabilizeXMap_simplyBlockedDifferential s i R)
    (simplyBlockedStabilizeXRingHom_C s i R)
    (G.oneVariableSpecializationStabilizeXHomologyMap_bijective s i R)

/-- On elements, `oneVariableSpecializationStabilizeXHomologyEquiv` is the semilinear stabilization
comparison. -/
@[simp]
theorem oneVariableSpecializationStabilizeXHomologyEquiv_apply
    (y : (ModuleCat.restrictScalars (MvPolynomial.C : R →+* S)).obj
      (((G').simplyBlockedComplex R j).homology ())) :
    G.oneVariableSpecializationStabilizeXHomologyEquiv s i R y =
      G.oneVariableSpecializationStabilizeXHomologyMap s i R y :=
  oneVariableSpecializationHomologyLinearEquivOfIntertwining_apply
    R j i (simplyBlockedStabilizeXRingHom s i R)
    (G.simplyBlockedStabilizeXMap s i R)
    (G.simplyBlockedStabilizeXMap_simplyBlockedDifferential s i R)
    (simplyBlockedStabilizeXRingHom_C s i R)
    (G.oneVariableSpecializationStabilizeXHomologyMap_bijective s i R) y

end TauCeti.GridDiagram
