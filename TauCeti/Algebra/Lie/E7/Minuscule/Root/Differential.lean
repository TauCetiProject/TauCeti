/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Differential
public import TauCeti.Algebra.AlgebraicGroup.Tangent.DerivationMap
public import TauCeti.Algebra.Lie.E7.Minuscule.ClosedGenerators

/-!
# Numbered root differentials of the minuscule E₇ carrier

Over every commutative base ring, the fourteen transported signed-simple-root subgroups
have injective differentials, even with coefficients in nonreduced algebras. In the
minuscule basis their differentials are the additive tangent parameter times the integral
raising or lowering matrix. The normalized root vectors are thus determined by the existing
root-subgroup maps, with no restriction on characteristic.

These are differential normalization data for the pinning required by the E₇ carrier
comparison. No assertion is made that the specialized integral carrier is reductive, that
its torus is maximal, or that these vectors span full adjoint root spaces.

The universal-point calculation follows
`TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Root.Differential`. The interpretation of the
linear coefficient as the root vector follows
`TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.Tangent`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a and §21.1.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.E7Minuscule

universe u v

noncomputable section

variable (R : Type u) [CommRing R]

private theorem map_genericMatrix_rootSubgroup (k : Fin 7 ⊕ Fin 7) :
    (GeneralLinear.genericMatrix R 56).map
        ((rootSubgroupToBaseChangeCoordinateMap R k).hom.toAlgHom.comp
          (coordinateMap R).hom.toAlgHom) =
      1 + SymmetricAlgebra.ι R R 1 •
        (Sum.elim raisingMatrix loweringMatrix k).map
          (Int.cast : ℤ → AdditiveGroup.coordinateHopfAlgebra R) := by
  let A := CommAlgCat.of R (AdditiveGroup.coordinateHopfAlgebra R)
  let q : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A :=
    toConv (AlgHom.id R (AdditiveGroup.coordinateHopfAlgebra R))
  have hu : AdditiveGroup.gaPointsMulEquiv (R := R) q =
      Multiplicative.ofAdd (SymmetricAlgebra.ι R R 1) := by
    rw [← ofAdd_toAdd (AdditiveGroup.gaPointsMulEquiv (R := R) q),
      AdditiveGroup.toAdd_gaPointsMulEquiv]
    simp [q]
  have h := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 56) A =>
    (g : Matrix (Fin 56) (Fin 56) A))
    (pointToGeneralLinear_mapDomain_rootSubgroupToBaseChangeCoordinateMap_eq_rootSubgroupPoints
      R k A q)
  rw [← GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear,
    AlgHom.mapDomain_apply] at h
  simp only [q, AlgHom.id_comp] at h
  rw [h, hu]
  rcases k with i | i
  · exact coe_rootSubgroupPoints_inl i _ _
  · exact coe_rootSubgroupPoints_inr i _ _

variable {B : Type v} [CommRing B] [Algebra R B]

/-- Each transported numbered root-subgroup differential is injective with coefficients
in every commutative base algebra, including nonreduced algebras. -/
theorem derivationComp_rootSubgroupToBaseChangeCoordinateMap_injective (k : Fin 7 ⊕ Fin 7) :
    Function.Injective (derivationComp (B := B)
      (rootSubgroupToBaseChangeCoordinateMap R k).hom) :=
  derivationComp_injective_of_surjective _
    (rootSubgroupToBaseChangeCoordinateMap_surjective R k)

/-- The matrix of a transported numbered root differential is the tangent parameter times
its integral raising or lowering matrix, over arbitrary commutative coefficient algebras. -/
theorem tangentMatrix_derivationComp_rootSubgroupToBaseChangeCoordinateMap
    (k : Fin 7 ⊕ Fin 7)
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) B)) :
    GeneralLinear.tangentMatrix 56
        (derivationComp (B := B) (coordinateMap R).hom
          (derivationComp (B := B) (rootSubgroupToBaseChangeCoordinateMap R k).hom d)) =
      AdditiveGroup.gaTangentLinearEquiv d •
        (Sum.elim raisingMatrix loweringMatrix k).map (Int.cast : ℤ → B) := by
  rw [← LinearMap.comp_apply, ← derivationComp_comp]
  exact GeneralLinear.tangentMatrix_derivationComp_eq_smul_of_map_genericMatrix _ _
    (map_genericMatrix_rootSubgroup R k) d

/-- The unit tangent vector of the numbered transported root subgroup, viewed intrinsically
in the specialized integral carrier. -/
def rootVector (k : Fin 7 ⊕ Fin 7) :
    Derivation R (coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R) R) :=
  derivationComp (B := R) (rootSubgroupToBaseChangeCoordinateMap R k).hom
    ((AdditiveGroup.gaTangentLinearEquiv (R := R) (B := R)).symm 1)

/-- The normalized root vector is the differential of the existing root parametrization
on the unit additive tangent vector. -/
theorem rootVector_def (k : Fin 7 ⊕ Fin 7) :
    rootVector R k =
      derivationComp (B := R) (rootSubgroupToBaseChangeCoordinateMap R k).hom
        ((AdditiveGroup.gaTangentLinearEquiv (R := R) (B := R)).symm 1) := by
  rw [rootVector]

/-- The normalized transported root vector has exactly the integral numbered root matrix. -/
@[simp↓]
theorem tangentMatrix_rootVector (k : Fin 7 ⊕ Fin 7) :
    GeneralLinear.tangentMatrix 56 (derivationComp (B := R) (coordinateMap R).hom
        (rootVector R k)) =
      (Sum.elim raisingMatrix loweringMatrix k).map (Int.cast : ℤ → R) := by
  rw [rootVector_def, tangentMatrix_derivationComp_rootSubgroupToBaseChangeCoordinateMap,
    LinearEquiv.apply_symm_apply, one_smul]

/-- A transported numbered root vector is nonzero over every nontrivial commutative base ring. -/
theorem rootVector_ne_zero [Nontrivial R] (k : Fin 7 ⊕ Fin 7) : rootVector R k ≠ 0 := by
  intro h
  rw [rootVector_def] at h
  have hz := derivationComp_rootSubgroupToBaseChangeCoordinateMap_injective R k
    (h.trans (map_zero _).symm)
  have hu := congrArg AdditiveGroup.gaTangentLinearEquiv hz
  exact (one_ne_zero : (1 : R) ≠ 0)
    (by simpa only [LinearEquiv.apply_symm_apply, map_zero] using hu)

end

end TauCeti.E7Minuscule
