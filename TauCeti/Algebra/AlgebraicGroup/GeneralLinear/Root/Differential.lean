/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Tangent
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.RootSpace
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Subgroup
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Map

/-!
# Differential of a matrix root subgroup

The root subgroup `xᵢⱼ : 𝔾ₐ → GLₙ` has derivative `c ↦ c Eᵢⱼ`. In particular, its derivative
at `1` is the matrix unit which spans the corresponding adjoint root space. The statement works
over an arbitrary commutative base ring and after extension to any commutative coefficient
algebra. It identifies the differential of the represented group-scheme morphism, rather than
only the derivative of an informal matrix formula.

The calculation supplies the root vector attached to the standard pinning of `GLₙ`.

## Reference

J. S. Milne, *Algebraic Groups* (2017), §21.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear

universe u v

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
variable {n : ℕ} {i j : Fin n}

/-- The root-subgroup coordinate map sends a generic matrix entry to the corresponding entry
of `1 + X Eᵢⱼ`. -/
theorem rootSubgroupCoordinateMap_apply_X (hij : i ≠ j) (a b : Fin n) :
    (rootSubgroupCoordinateMap (R := R) (N := n) hij).hom
      (coordinateHopfAlgebraAlgEquiv R n
        (coordinateRingMap R n (MvPolynomial.X (a, b)))) =
      (1 : Matrix (Fin n) (Fin n) (AdditiveGroup.coordinateHopfAlgebra R)) a b +
        (Matrix.single i j (SymmetricAlgebra.ι R R 1)) a b := by
  let A := AdditiveGroup.coordinateHopfAlgebra R
  let q : WithConv (A →ₐ[R] A) := toConv (AlgHom.id R A)
  let p : WithConv (coordinateHopfAlgebra R n →ₐ[R] A) :=
    (CommHopfAlgCat.mapPointsFunctor
      (rootSubgroupCoordinateMap (R := R) (N := n) hij)).app (CommAlgCat.of R A) q
  have h := congrArg
    (fun p' : WithConv (coordinateHopfAlgebra R n →ₐ[R] A) ↦
      (pointsMulEquiv n p' : Matrix (Fin n) (Fin n) A) a b)
    -- Name the functorial point explicitly: its category-theoretic coercion otherwise hides
    -- the `WithConv` carrier expected by the matrix point equivalence.
    (show p = rootSubgroupPoints hij q from
      mapPointsFunctor_rootSubgroupCoordinateMap_app hij (CommAlgCat.of R A) q)
  rw [pointsMulEquiv_rootSubgroupPoints, coe_transvectionUnit] at h
  rw [pointsMulEquiv_apply, pointToGeneralLinear_apply] at h
  simp only [Matrix.transvection, Matrix.add_apply] at h
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply_apply] at h
  simp only [AdditiveGroup.toAdd_gaPointsMulEquiv] at h
  dsimp [q] at h
  exact h

/-- The differential of the matrix root subgroup sends an additive tangent vector `c` to
`c Eᵢⱼ`. This holds over every commutative base ring and coefficient algebra. -/
theorem tangentMatrix_derivationComp_rootSubgroup (hij : i ≠ j)
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) B)) :
    tangentMatrix n
        (derivationComp (B := B)
          (rootSubgroupCoordinateMap (R := R) (N := n) hij).hom d) =
      Matrix.single i j (AdditiveGroup.gaTangentLinearEquiv d) := by
  ext a b
  rw [tangentMatrix_apply, algEquivSelf_derivationComp_apply]
  have hcoord := congrArg d (rootSubgroupCoordinateMap_apply_X (R := R) hij a b)
  -- The two counit coefficient algebras share the carrier `B`, but the category-morphism
  -- coercion hides the exact coordinate expression used by `hcoord`.
  change Bialgebra.CounitAlgebra.algEquivSelf R
      (AdditiveGroup.coordinateHopfAlgebra R) B
        (d ((rootSubgroupCoordinateMap (R := R) (N := n) hij).hom
          (coordinateHopfAlgebraAlgEquiv R n
            (coordinateRingMap R n (MvPolynomial.X (a, b)))))) = _
  rw [hcoord, map_add]
  have hconst : d ((1 : Matrix (Fin n) (Fin n)
      (AdditiveGroup.coordinateHopfAlgebra R)) a b) = 0 := by
    classical
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  rw [hconst, zero_add]
  classical
  by_cases h : i = a ∧ j = b
  · rcases h with ⟨rfl, rfl⟩
    simp [Matrix.single, AdditiveGroup.gaTangentLinearEquiv_apply]
    rfl
  · simp [Matrix.single, h]
    rfl

section Field

variable {k : Type u} [Field k] {n : ℕ} {i j : Fin n}

/-- The unit tangent vector of `𝔾ₐ` maps to the matrix unit `Eᵢⱼ` in the fixed cotangent-dual
model of the Lie algebra of `GLₙ`. -/
theorem cotangentDual_rootSubgroup_unit (hij : i ≠ j) :
    (Derivation.cotangentLinearEquiv (R := k)
      (A := coordinateHopfAlgebra k n) (B := k)).symm
      (derivationComp (B := k) (rootSubgroupCoordinateMap (R := k) (N := n) hij).hom
        ((AdditiveGroup.gaTangentLinearEquiv (R := k) (B := k)).symm 1)) =
      matrixUnitTangent (k := k) i j := by
  apply (cotangentDualMatrixEquiv (k := k) (n := n)).injective
  rw [cotangentDualMatrixEquiv_matrixUnitTangent]
  rw [cotangentDualMatrixEquiv_apply,
    LinearEquiv.apply_symm_apply, tangentMatrix_derivationComp_rootSubgroup]
  simp

/-- The derivative of a root subgroup at the identity lies in the adjoint weight space of
weight `eᵢ - eⱼ` for the diagonal torus. -/
theorem cotangentDual_rootSubgroup_unit_mem_adjointWeightSpace (hij : i ≠ j) :
    (Derivation.cotangentLinearEquiv (R := k)
      (A := coordinateHopfAlgebra k n) (B := k)).symm
      (derivationComp (B := k) (rootSubgroupCoordinateMap (R := k) (N := n) hij).hom
        ((AdditiveGroup.gaTangentLinearEquiv (R := k) (B := k)).symm 1)) ∈
      Derivation.adjointWeightSpace
        (diagonalTorusCoordinateMap (R := k) (N := n)).hom (matrixUnitWeight i j) := by
  rw [cotangentDual_rootSubgroup_unit hij]
  exact matrixUnitTangent_mem_adjointWeightSpace i j

end Field

end TauCeti.GeneralLinear
