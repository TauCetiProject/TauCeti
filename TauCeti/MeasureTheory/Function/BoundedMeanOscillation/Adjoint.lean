/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation

/-!
# Mean oscillation of the adjoint of an operator field

Taking adjoints of operators between complete inner product spaces is a real linear isometric
equivalence (`ContinuousLinearMap.adjointRealLinearIsometryEquiv`), so it commutes with averages
and preserves distances. Hence the field of adjoints `x ↦ (f x)†` of an operator field `f` has the
same VMO modulus and the same BMO seminorm as `f`.

## Main declarations

* `ContinuousLinearMap.vmoModulus_adjoint`: the equality for the VMO modulus.
* `ContinuousLinearMap.bmoSeminorm_adjoint`: the equality for the BMO seminorm.
-/

public section

namespace ContinuousLinearMap

open MeasureTheory TauCeti

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V] [CompleteSpace V] [NormedAddCommGroup W]
  [InnerProductSpace 𝕜 W] [NormedSpace ℝ W] [IsScalarTower ℝ 𝕜 W] [CompleteSpace W]

private theorem comp_eq_adjoint {X : Type*} (f : X → V →L[𝕜] W) :
    (adjointRealLinearIsometryEquiv (𝕜 := 𝕜) (V := V) (W := W)).toLinearIsometry ∘ f =
      fun x => adjoint (f x) :=
  funext fun x => adjointRealLinearIsometryEquiv_apply (f x)

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {μ : Measure X}

/-- Taking adjoints does not change the VMO modulus of an operator field: the adjoint is a real
linear isometry. -/
@[simp]
theorem vmoModulus_adjoint (f : X → V →L[𝕜] W) (r : ℝ) :
    vmoModulus (fun x => adjoint (f x)) μ r = vmoModulus f μ r := by
  rw [← comp_eq_adjoint]
  exact LinearIsometry.vmoModulus_comp _ r

/-- Taking adjoints does not change the BMO seminorm of an operator field: the adjoint is a real
linear isometry. -/
@[simp]
theorem bmoSeminorm_adjoint (f : X → V →L[𝕜] W) :
    bmoSeminorm (fun x => adjoint (f x)) μ = bmoSeminorm f μ := by
  rw [← comp_eq_adjoint]
  exact LinearIsometry.bmoSeminorm_comp _

end ContinuousLinearMap
