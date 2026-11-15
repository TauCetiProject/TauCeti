/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.Basic
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl.RankOne

/-!
# Weyl squares in the Geck carrier

The pinned opposite-root word at a unit parameter satisfies
`(xᵢ(u) x₋ᵢ(-u⁻¹) xᵢ(u))² = αᵢ∨(-1)` in the Geck carrier over every commutative ring.
Here the simple coroot is the coordinate cocharacter of the represented weight torus in
fundamental-weight coordinates. In particular, the pinned simple Weyl representative has fourth
power one, but its square need not be one.

These relations record the torus correction in the normalizer representatives used to transport
numbered root subgroups. They do not identify the explicit carrier with an independently pinned
group scheme. The proof transports
`TauCeti.UniversalEnvelopingAlgebra.kostantWeylParam_sq` through the Geck coordinate basis; no
factorial or bad prime is inverted in the value ring.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 19–20.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups* (2017).
-/

public section

open TensorProduct

namespace TauCeti.DynkinType

universe v

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] TauCeti.moduleNNRat
-- Scalar extension uses the integer module structure of the value algebra.
attribute [local instance high] Algebra.toModule

variable (t : DynkinType) (ht : t.Valid)

private theorem coe_root_eq_basisMatrix (i : Fin t.rank ⊕ Fin t.rank)
    (A : Type v) [CommRing A] (u : Multiplicative A) :
    (t.geckRootSubgroupPoints ht i A u :
      Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) =
    Units.map (LinearMap.toMatrixAlgEquiv
      ((t.geckCoordinateBasisFin ht).baseChange A)).toMulEquiv
      (t.geckRootSubgroupParam ht i (CommAlgCat.of ℤ A) u) := by
  exact (t.coe_geckRootSubgroupPoints ht i A u).trans
    (UniversalEnvelopingAlgebra.basisMatrix_kostantRootSubgroupParam
      _ _ _ _ _ _ (t.geckCoordinateBasisFin ht) A i u).symm

private theorem coe_torus_eq_basisMatrix (A : Type v) [CommRing A]
    (s : Fin t.rank → Aˣ) :
    (t.geckWeightTorusPoints ht A s :
      Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) =
    Units.map (LinearMap.toMatrixAlgEquiv
      ((t.geckCoordinateBasisFin ht).baseChange A)).toMonoidHom
      (t.geckTorusPoints ht (CommAlgCat.of ℤ A) s) := by
  rw [coe_geckWeightTorusPoints]
  exact (UniversalEnvelopingAlgebra.basisMatrix_kostantTorusPoints
    (t.geckCoordinateLattice ht).toAddSubgroup (t.geckCoordinateBasisFin ht)
    (t.geckWeightFin ht) s).symm

/-- The square of the opposite-root Weyl word, at any unit parameter, is the simple-coroot
value at `-1`. This holds in the carrier itself, over arbitrary commutative value rings. -/
@[simp↓]
theorem geckRootSubgroupPoints_weyl_sq (i : Fin t.rank) (A : Type v) [CommRing A]
    (u : Aˣ) :
    (t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd (u : A)) *
      t.geckRootSubgroupPoints ht (.inr i) A
        (Multiplicative.ofAdd (-((u⁻¹ : Aˣ) : A))) *
      t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd (u : A))) ^ 2 =
        t.geckWeightTorusPoints ht A (Pi.mulSingle i (-1)) := by
  classical
  have h := UniversalEnvelopingAlgebra.kostantWeylParam_sq
    (i := Sum.inl i) (j := Sum.inr i) (c := i)
    (α := (t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i))
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht (.inl i))
    (t.isNilpotent_geckRepresentation_rootGenerator ht (.inr i))
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht)
    (t.isCartanWeightVector_geckCoordinateBasisFin ht)
    (t.isSl2Triple_geckRepresentation ht i)
    (fun q ↦ by
      rw [← t.rootGeneratorWeight_inl_eq_root_simpleIndex ht i]
      exact t.lie_lieBasis_h_rootGenerator ht (.inl i) q)
    (fun q ↦ by
      have hneg := t.lie_lieBasis_h_rootGenerator ht (.inr i) q
      rw [t.rootGeneratorWeight_inr_eq_neg_root_simpleIndex ht i,
        Pi.neg_apply, Int.cast_neg, neg_smul] at hneg
      exact hneg)
    (CommAlgCat.of ℤ A) u
  have hmatrix := congrArg
    (Units.map (LinearMap.toMatrixAlgEquiv
      ((t.geckCoordinateBasisFin ht).baseChange A)).toMonoidHom) h
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_mul, coe_root_eq_basisMatrix,
    coe_torus_eq_basisMatrix]
  simpa only [UniversalEnvelopingAlgebra.kostantWeylParam_def,
    UniversalEnvelopingAlgebra.kostantCoordinateCocharacter_apply, map_pow, map_mul,
    MulEquiv.toMonoidHom_eq_coe] using hmatrix

/-- The pinned simple Weyl representative squares to the simple-coroot value at `-1`. -/
@[simp]
theorem geckSimpleWeylPoint_sq (i : Fin t.rank) (A : Type v) [CommRing A] :
    t.geckSimpleWeylPoint ht i A ^ 2 =
      t.geckWeightTorusPoints ht A (Pi.mulSingle i (-1)) := by
  classical
  have h := t.geckRootSubgroupPoints_weyl_sq ht i A (1 : Aˣ)
  rw [geckSimpleWeylPoint_eq_mul]
  simpa only [inv_one, Units.val_one] using h

/-- The pinned simple Weyl representatives have fourth power one, without a characteristic
restriction or an assumption that their squares are trivial. -/
@[simp]
theorem geckSimpleWeylPoint_pow_four (i : Fin t.rank) (A : Type v) [CommRing A] :
    t.geckSimpleWeylPoint ht i A ^ 4 = 1 := by
  classical
  calc
    t.geckSimpleWeylPoint ht i A ^ 4 = (t.geckSimpleWeylPoint ht i A ^ 2) ^ 2 :=
      pow_mul (t.geckSimpleWeylPoint ht i A) 2 2
    _ = 1 := by
      rw [geckSimpleWeylPoint_sq, ← map_pow (t.geckWeightTorusPoints ht A),
        ← Pi.mulSingle_pow, neg_one_sq, Pi.mulSingle_one, map_one]

end

end TauCeti.DynkinType
