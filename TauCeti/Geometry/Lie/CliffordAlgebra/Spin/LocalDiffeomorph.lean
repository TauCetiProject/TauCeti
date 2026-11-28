/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.Differential
public import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Standard

/-!
# The compact real Spin projection is a local diffeomorphism

The smooth projection between the native Spin and special-orthogonal units ranges has an
invertible Lie differential. In quadratic-Clifford and skew-matrix coordinates this is precisely
the bivector equivalence, including its factor of two. Consequently the projection is a smooth
local diffeomorphism at every point. Mathlib's `IsLocalDiffeomorphAt.localInverse` then supplies
smooth local sections through each chosen point of the Spin range.

The Lie-algebra equivalence and its inverse use the same closed-subgroup smooth structures as
the smooth projection. On the matrix side the topology is the operator-induced topology,
selected explicitly by `Matrix.linftyOpTopologicalSpace`, not the default Pi topology.
These statements also hold in dimensions zero and one; dimension zero concerns the native
trivial Spin group, not the separate geometric two-element group.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Section 2.
-/

public section

open Manifold
open scoped ContDiff Manifold Matrix.Norms.Operator

noncomputable section

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Matrix.linftyOpTopologicalSpace

local notation "SpinUnitsRange(" n ")" =>
  MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))

local notation "SpecialOrthogonalUnitsRange(" n ")" =>
  MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
    (realCliffordForm n 0 : QuadraticForm ℝ (Fin n → ℝ)))

local notation "SpinLieModel(" n ")" =>
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, CliffordAlgebra (realCliffordForm n 0))) (SpinUnitsRange(n)))

local notation "SpecialOrthogonalLieModel(" n ")" =>
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) (SpecialOrthogonalUnitsRange(n)))

/-- The identity linear equivalence as an isometry from `realCliffordForm n 0` to the standard
sum-of-squares form. -/
def realCliffordFormZeroIsometryWeightedSumSquares (n : ℕ) :
    (realCliffordForm n 0).IsometryEquiv (QuadraticMap.weightedSumSquares ℝ (1 : Fin n → ℝ)) where
  __ := LinearEquiv.refl ℝ (Fin n → ℝ)
  map_app' v := congrArg (fun Q : QuadraticForm ℝ (Fin n → ℝ) ↦ Q v)
    (realCliffordForm_zero_eq_weightedSumSquares_one n).symm

/-- `realCliffordFormZeroIsometryWeightedSumSquares` acts as the identity on vectors. -/
@[simp]
theorem realCliffordFormZeroIsometryWeightedSumSquares_apply (n : ℕ) (v : Fin n → ℝ) :
    realCliffordFormZeroIsometryWeightedSumSquares n v = v :=
  (rfl)

/-- The inverse of `realCliffordFormZeroIsometryWeightedSumSquares` acts as the identity on
vectors. -/
@[simp]
theorem realCliffordFormZeroIsometryWeightedSumSquares_symm_apply (n : ℕ) (v : Fin n → ℝ) :
    (realCliffordFormZeroIsometryWeightedSumSquares n).symm v = v :=
  (rfl)

/-- The coordinate differential of the real Spin projection undoes
`CliffordAlgebra.matrixSoEquivQuadratic`. -/
theorem realCliffordSpinToSpecialOrthogonalCoordinateLieHom_matrixSoEquivQuadratic (n : ℕ)
    (A : LieAlgebra.Orthogonal.so (Fin n) ℝ) :
    realCliffordSpinToSpecialOrthogonalCoordinateLieHom n
        (matrixSoEquivQuadratic (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0)
          (realCliffordFormZeroIsometryWeightedSumSquares n) A) = A := by
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext v
  apply ι_injective (realCliffordForm n 0)
  rw [realCliffordSpinToSpecialOrthogonalCoordinateLieHom_lie_ι,
    matrixSoEquivQuadratic_lie_ι,
    realCliffordFormZeroIsometryWeightedSumSquares_apply,
    realCliffordFormZeroIsometryWeightedSumSquares_symm_apply]

/-- In quadratic Clifford and skew-matrix coordinates, the differential of the real Spin projection
is the inverse of `CliffordAlgebra.matrixSoEquivQuadratic`. -/
theorem realCliffordSpinToSpecialOrthogonalCoordinateLieHom_eq_symm_matrixSoEquivQuadratic
    (n : ℕ) :
    realCliffordSpinToSpecialOrthogonalCoordinateLieHom n =
      (matrixSoEquivQuadratic (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0)
        (realCliffordFormZeroIsometryWeightedSumSquares n)).symm.toLieHom := by
  refine LieHom.ext fun x ↦ ?_
  calc
    realCliffordSpinToSpecialOrthogonalCoordinateLieHom n x
      = realCliffordSpinToSpecialOrthogonalCoordinateLieHom n
          (matrixSoEquivQuadratic (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0)
            (realCliffordFormZeroIsometryWeightedSumSquares n)
            ((matrixSoEquivQuadratic (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0)
              (realCliffordFormZeroIsometryWeightedSumSquares n)).symm x)) := by
        rw [LieEquiv.apply_symm_apply]
    _ = _ := realCliffordSpinToSpecialOrthogonalCoordinateLieHom_matrixSoEquivQuadratic n _

/-- In `so(n)` coordinates, the quadratic Clifford realization along
`realCliffordFormZeroIsometryWeightedSumSquares` agrees with the normalized exterior-bivector
embedding of `(bivectorEquivSo n ℝ).symm A`. -/
theorem matrixSoEquivQuadratic_realCliffordFormZeroIsometryWeightedSumSquares_eq_bivector
    (n : ℕ) (A : LieAlgebra.Orthogonal.so (Fin n) ℝ) :
    let Q₀ := QuadraticMap.weightedSumSquares ℝ (1 : Fin n → ℝ)
    letI := bivectorLieRing Q₀
    letI := bivectorLieAlgebra Q₀
    matrixSoEquivQuadratic (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0)
        (realCliffordFormZeroIsometryWeightedSumSquares n) A =
      bivectorExteriorEquivQuadraticLieSubalgebra (realCliffordForm n 0)
        ((bivectorEquivSo n ℝ).symm A) := by
  let Q₀ := QuadraticMap.weightedSumSquares ℝ (1 : Fin n → ℝ)
  let _ := bivectorLieRing Q₀
  let _ := bivectorLieAlgebra Q₀
  apply (matrixSoEquivQuadratic (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0)
    (realCliffordFormZeroIsometryWeightedSumSquares n)).symm.injective
  simp only [LieEquiv.coe_toLieHom]
  rw [LieEquiv.symm_apply_apply, ← LieEquiv.coe_toLieHom,
    ← realCliffordSpinToSpecialOrthogonalCoordinateLieHom_eq_symm_matrixSoEquivQuadratic,
    realCliffordSpinToSpecialOrthogonalCoordinateLieHom_eq_bivectorEquivSo,
    LieEquiv.apply_symm_apply]

/-- The differential of the Spin projection in quadratic and skew-matrix coordinates is
bijective, in every dimension. -/
theorem realCliffordSpinToSpecialOrthogonalCoordinateLieHom_bijective (n : ℕ) :
    Function.Bijective (realCliffordSpinToSpecialOrthogonalCoordinateLieHom n) := by
  rw [realCliffordSpinToSpecialOrthogonalCoordinateLieHom_eq_symm_matrixSoEquivQuadratic]
  exact (matrixSoEquivQuadratic (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0)
    (realCliffordFormZeroIsometryWeightedSumSquares n)).symm.bijective

/-- The differential of the smooth Spin projection on the native units-range carriers is
bijective. -/
theorem realCliffordSpinToSpecialOrthogonalRangeLieMap_bijective (n : ℕ) :
    Function.Bijective (realCliffordSpinToSpecialOrthogonalRangeLieMap n) := by
  have h := realCliffordSpinToSpecialOrthogonalCoordinateLieHom_bijective n
  have heq : (realCliffordSpinToSpecialOrthogonalCoordinateLieHom n : _ → _) =
      realCliffordSpecialOrthogonalLieEquivSo n ∘
        realCliffordSpinToSpecialOrthogonalRangeLieMap n ∘
          (realCliffordSpinLieEquivQuadratic n).symm := by
    funext x
    exact realCliffordSpinToSpecialOrthogonalCoordinateLieHom_apply n x
  rw [heq] at h
  exact ((realCliffordSpecialOrthogonalLieEquivSo n).bijective.of_comp_iff' _).mp
    ((Function.Bijective.of_comp_iff _
      (realCliffordSpinLieEquivQuadratic n).symm.bijective).mp h)

/-- The invertible Lie differential of the smooth Spin projection. Its inverse lifts an
infinitesimal orthogonal transformation to the native Spin Lie algebra. -/
def realCliffordSpinToSpecialOrthogonalRangeLieEquiv (n : ℕ) :
    LeftInvariantDerivation 𝓘(ℝ, SpinLieModel(n)) (SpinUnitsRange(n)) ≃ₗ⁅ℝ⁆
      LeftInvariantDerivation 𝓘(ℝ, SpecialOrthogonalLieModel(n))
        (SpecialOrthogonalUnitsRange(n)) :=
  LieEquiv.ofBijective (realCliffordSpinToSpecialOrthogonalRangeLieMap n)
    (realCliffordSpinToSpecialOrthogonalRangeLieMap_bijective n)

/-- The Lie equivalence acts by the supplied Lie differential. -/
@[simp]
theorem realCliffordSpinToSpecialOrthogonalRangeLieEquiv_apply (n : ℕ)
    (X : LeftInvariantDerivation 𝓘(ℝ, SpinLieModel(n)) (SpinUnitsRange(n))) :
    realCliffordSpinToSpecialOrthogonalRangeLieEquiv n X =
      realCliffordSpinToSpecialOrthogonalRangeLieMap n X := (rfl)

/-- The Lie equivalence is the actual differential of the smooth projection. -/
@[simp]
theorem realCliffordSpinToSpecialOrthogonalRangeLieEquiv_toLieHom (n : ℕ) :
    (realCliffordSpinToSpecialOrthogonalRangeLieEquiv n).toLieHom =
      realCliffordSpinToSpecialOrthogonalRangeLieMap n := (rfl)

/-- The smooth compact real Spin projection is a local diffeomorphism on the native
units-range Lie-group carriers. This includes the native trivial group in dimension zero. -/
theorem isLocalDiffeomorph_realCliffordSpinToSpecialOrthogonalSmoothRange (n : ℕ) :
    IsLocalDiffeomorph 𝓘(ℝ, SpinLieModel(n)) 𝓘(ℝ, SpecialOrthogonalLieModel(n)) ∞
      (realCliffordSpinToSpecialOrthogonalSmoothRange n) := by
  apply (realCliffordSpinToSpecialOrthogonalSmoothRange n).isLocalDiffeomorph_of_lieMap_bijective
  simpa only [realCliffordSpinToSpecialOrthogonalRangeLieMap_eq_lieMap] using
    realCliffordSpinToSpecialOrthogonalRangeLieMap_bijective n

end TauCeti.CliffordAlgebra
