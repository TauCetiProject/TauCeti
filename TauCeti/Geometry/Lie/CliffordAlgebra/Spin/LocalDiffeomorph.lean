/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.Differential

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

/-- The differential of the Spin projection in quadratic and skew-matrix coordinates is
bijective, in every dimension. -/
theorem realCliffordSpinToSpecialOrthogonalCoordinateLieHom_bijective (n : ℕ) :
    Function.Bijective (realCliffordSpinToSpecialOrthogonalCoordinateLieHom n) := by
  let e := bivectorExteriorEquivQuadraticLieSubalgebra (realCliffordForm n 0)
  apply (Function.Bijective.of_comp_iff _ e.bijective).mp
  have h : realCliffordSpinToSpecialOrthogonalCoordinateLieHom n ∘ e =
      bivectorEquivSo n ℝ := by
    funext z
    exact realCliffordSpinToSpecialOrthogonalCoordinateLieHom_eq_bivectorEquivSo n z
  rw [h]
  let Q := QuadraticMap.weightedSumSquares ℝ (1 : Fin n → ℝ)
  let _ := bivectorLieRing Q
  let _ := bivectorLieAlgebra Q
  exact (bivectorEquivSo n ℝ).bijective

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
