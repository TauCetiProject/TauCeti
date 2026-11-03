/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.PointsFunctor
public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Braid

/-!
# Braid relations in the E₇ minuscule carrier

The pinned simple Weyl points `nᵢ = xᵢ(1) x₋ᵢ(-1) xᵢ(1)` satisfy the commuting and
three-factor braid relations of the Bourbaki E₇ diagram. These are equalities in the explicit
carrier, not merely equalities modulo its weight torus. They supply coherence for transporting
root subgroups along simple-reflection words, over every commutative coefficient ring.

The integral minuscule matrices of `TauCeti.E7Minuscule.raisingMatrix` and
`TauCeti.E7Minuscule.loweringMatrix` make each simple Weyl point a signed permutation of the
fifty-six weight vectors. The relations retain these signs, including before reduction in
characteristic two. No identification with an independently pinned group scheme is asserted.

## Main declarations

* `TauCeti.E7Minuscule.simpleWeylPoint`
* `TauCeti.E7Minuscule.coe_simpleWeylPoint_mulVec_single`
* `TauCeti.E7Minuscule.commute_simpleWeylPoint_of_cartanMatrix_eq_zero`
* `TauCeti.E7Minuscule.simpleWeylPoint_braid_of_cartanMatrix_eq_neg_one`

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §6, for the relations between pinned Weyl lifts.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VI, for the numbering.

The explicit weight and reflection data are those of
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E7.MinusculeWeight`.
-/

public section

open scoped Matrix

namespace TauCeti.E7Minuscule

open TauCeti.DynkinType

/-- The pinned simple Weyl representative `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` in the E₇ carrier. -/
noncomputable def simpleWeylPoint (i : Fin 7) (R : Type*) [CommRing R] : points R :=
  rootSubgroupPoints (.inl i) R (Multiplicative.ofAdd 1) *
    rootSubgroupPoints (.inr i) R (Multiplicative.ofAdd (-1)) *
    rootSubgroupPoints (.inl i) R (Multiplicative.ofAdd 1)

/-- The representative is the specified product of pinned root-subgroup points. -/
theorem simpleWeylPoint_def (i : Fin 7) (R : Type*) [CommRing R] :
    simpleWeylPoint i R =
      rootSubgroupPoints (.inl i) R (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) R (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) R (Multiplicative.ofAdd 1) := by
  rw [simpleWeylPoint]

/-- Simple Weyl representatives commute with change of value ring. -/
theorem map_simpleWeylPoint {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (i : Fin 7) :
    (pointsPresentation R).map (pointsPresentation S) f (simpleWeylPoint i R) =
      simpleWeylPoint i S := by
  rw [simpleWeylPoint_def, simpleWeylPoint_def, map_mul, map_mul,
    map_rootSubgroupPoints, map_rootSubgroupPoints]
  simp only [toAdd_ofAdd, map_one, map_neg]

/-- The matrix of the pinned representative is the Weyl matrix of the minuscule table. -/
@[simp]
theorem coe_simpleWeylPoint (i : Fin 7) (R : Type*) [CommRing R] :
    (((simpleWeylPoint i R : points R) : Matrix.GeneralLinearGroup (Fin 56) R) :
        Matrix (Fin 56) (Fin 56) R) = weightTable.simpleWeylMatrix i R := by
  simp only [simpleWeylPoint_def, Subgroup.coe_mul, Units.val_mul,
    coe_rootSubgroupPoints_inl, coe_rootSubgroupPoints_inr, toAdd_ofAdd, one_smul,
    neg_smul, MinusculeWeightTable.simpleWeylMatrix_def, weightTable_raisingMatrix,
    weightTable_loweringMatrix, sub_eq_add_neg]

/-- A simple Weyl point acts by the weight reflection, with a minus sign exactly at
simple-coroot coordinate `1`. -/
theorem coe_simpleWeylPoint_mulVec_single (i : Fin 7) (R : Type*) [CommRing R] (a : Fin 56) :
    ((((simpleWeylPoint i R : points R) : Matrix.GeneralLinearGroup (Fin 56) R) :
        Matrix (Fin 56) (Fin 56) R)).mulVec (Pi.single a 1) =
      (if e7MinusculeWeight a i = 1 then (-1 : R) else 1) •
        Pi.single (e7MinusculeReflection i a) 1 := by
  rw [coe_simpleWeylPoint]
  simpa only [weightTable_weight, weightTable_reflection] using
    weightTable.simpleWeylMatrix_mulVec_single i R a

/-- Pinned simple Weyl points at nonadjacent E₇ nodes commute over every commutative ring. -/
theorem commute_simpleWeylPoint_of_cartanMatrix_eq_zero (R : Type*) [CommRing R]
    (i j : Fin 7) (h : CartanMatrix.E 7 i j = 0) :
    Commute (simpleWeylPoint i R) (simpleWeylPoint j R) := by
  rw [commute_iff_eq]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_simpleWeylPoint]
  exact (weightTable.commute_simpleWeylMatrix_of_cartanMatrix_eq_zero R i j
    (by simpa only [weightTable_cartanMatrix] using h)).eq

/-- The pinned simple Weyl points at adjacent E₇ nodes satisfy the length-three braid relation,
with their integral signs retained over arbitrary commutative rings. -/
theorem simpleWeylPoint_braid_of_cartanMatrix_eq_neg_one (R : Type*) [CommRing R]
    (i j : Fin 7) (h : CartanMatrix.E 7 i j = -1) :
    simpleWeylPoint i R * simpleWeylPoint j R * simpleWeylPoint i R =
      simpleWeylPoint j R * simpleWeylPoint i R * simpleWeylPoint j R := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_simpleWeylPoint]
  apply weightTable.simpleWeylMatrix_braid_of_cartanMatrix_eq_neg_one
  · simpa only [weightTable_cartanMatrix] using h
  · simpa only [weightTable_cartanMatrix, (CartanMatrix.E_isSymm 7).apply j i] using h

end TauCeti.E7Minuscule
