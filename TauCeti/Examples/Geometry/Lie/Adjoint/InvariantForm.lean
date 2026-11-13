/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.InvariantForm
public import TauCeti.Geometry.Lie.Exponential.Circle
public import TauCeti.Geometry.Manifold.Instances.PUnit
import TauCeti.Geometry.Lie.Subgroup.Commutative
import Mathlib.Algebra.Lie.Solvable

/-!
# Boundary cases for the compact Lie-algebra Haar average

The circle has trivial adjoint action, so Haar averaging preserves every starting form. Its
Lie algebra is one-dimensional, is its own centre, and has zero derived algebra. For the point
group, the Lie algebra and every starting form are zero.

## Main results

* `TauCeti.Examples.LieGroups.circle_averageAdjointBilinForm`: circle forms are fixed by averaging.
* `TauCeti.Examples.LieGroups.circle_lieAlgebra_center_derived`: its dimension and ideals.
* `TauCeti.Examples.LieGroups.point_lieAlgebra_center_derived`: dimension and ideals for the point.
* `TauCeti.Examples.LieGroups.point_averageAdjointBilinForm`: every point form has zero average.

## References

* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer Monographs in
  Mathematics (2012), Lemma 10.4.14, for the Haar average.
-/

public noncomputable section

open scoped ContDiff Manifold
open TauCeti.Lie

namespace TauCeti.Examples.LieGroups

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- Haar averaging on the circle fixes every real bilinear form on its Lie algebra. -/
theorem circle_averageAdjointBilinForm
    (B : LinearMap.BilinForm ℝ (LeftInvariantDerivation (𝓡 1) Circle)) :
    letI : MeasurableSpace Circle := borel Circle
    letI : BorelSpace Circle := ⟨rfl⟩
    averageAdjointBilinForm B = B := by
  let : MeasurableSpace Circle := borel Circle
  let : BorelSpace Circle := ⟨rfl⟩
  apply averageAdjointBilinForm_eq_self
  apply Representation.isInvariantForm_iff.mpr
  intro g X Y
  have hAd (g : Circle) (X : LeftInvariantDerivation (𝓡 1) Circle) : Ad g X = X :=
    Ad_apply_eq_self_of_forall_commute fun _ ↦ Commute.all _ _
  simp only [ContRepresentation.toRepresentation_apply, continuousAdjointRepresentation_apply,
    hAd]

/-- The circle's Lie algebra has dimension one, full centre, and zero derived algebra. -/
theorem circle_lieAlgebra_center_derived :
    Module.finrank ℝ (LeftInvariantDerivation (𝓡 1) Circle) = 1 ∧
      LieAlgebra.center ℝ (LeftInvariantDerivation (𝓡 1) Circle) = ⊤ ∧
      LieAlgebra.derivedSeries ℝ (LeftInvariantDerivation (𝓡 1) Circle) 1 = ⊥ := by
  refine ⟨?_, (LieAlgebra.isLieAbelian_iff_center_eq_top ℝ _).mp inferInstance, ?_⟩
  · simpa only [Module.finrank_self] using circleLieAlgebraEquiv.finrank_eq
  · exact (LieAlgebra.abelian_iff_derived_one_eq_bot
      (⊤ : LieIdeal ℝ (LeftInvariantDerivation (𝓡 1) Circle))).mp
      ((lie_abelian_iff_equiv_lie_abelian LieIdeal.topEquiv).mpr inferInstance)

/-- The point's Lie algebra has dimension zero, zero centre, and zero derived algebra. -/
theorem point_lieAlgebra_center_derived :
    Module.finrank ℝ (LeftInvariantDerivation 𝓘(ℝ, PUnit.{1}) PUnit.{1}) = 0 ∧
      LieAlgebra.center ℝ (LeftInvariantDerivation 𝓘(ℝ, PUnit.{1}) PUnit.{1}) = ⊥ ∧
      LieAlgebra.derivedSeries ℝ (LeftInvariantDerivation 𝓘(ℝ, PUnit.{1}) PUnit.{1}) 1 = ⊥ := by
  exact ⟨Module.finrank_zero_of_subsingleton, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- Every form on the point's Lie algebra, including its Haar average, is zero. -/
theorem point_averageAdjointBilinForm
    (B : LinearMap.BilinForm ℝ (LeftInvariantDerivation 𝓘(ℝ, PUnit.{1}) PUnit.{1})) :
    averageAdjointBilinForm B = 0 := by
  ext X Y
  rw [Subsingleton.elim X 0]
  simp

end TauCeti.Examples.LieGroups
