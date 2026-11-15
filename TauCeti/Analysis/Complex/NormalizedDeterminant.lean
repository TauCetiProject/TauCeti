/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The normalized determinant of a complex-linear automorphism

The determinant of a complex-linear automorphism `A` is a nonzero complex number, so it is
`‖det A‖` times the point `det A / ‖det A‖` of the unit circle
(`ContinuousLinearEquiv.normalizedDet`). The normalized determinant depends continuously on `A`,
so a loop of automorphisms gives a loop on the circle; its degree is the winding number of the
loop of determinants.

## Main declarations

* `ContinuousLinearEquiv.normalizedDet`: the point `det A / ‖det A‖` of the circle.
* `ContinuousLinearEquiv.det_eq_norm_mul_normalizedDet`: `det A = ‖det A‖ * normalizedDet A`.
* `Continuous.normalizedDet`: a continuous family of automorphisms has continuous normalized
  determinant.
-/

public section

namespace ContinuousLinearEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The normalized determinant `det A / ‖det A‖` of a complex-linear automorphism, a point of the
circle. -/
noncomputable def normalizedDet (A : E ≃L[ℂ] E) : Circle :=
  ⟨LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E) / ‖LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E)‖,
    mem_sphere_zero_iff_norm.2 (by simp [A.toLinearEquiv.isUnit_det'.ne_zero])⟩

/-- The normalized determinant, as a complex number. -/
@[simp]
theorem coe_normalizedDet (A : E ≃L[ℂ] E) :
    (A.normalizedDet : ℂ) =
      LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E) /
        ‖LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E)‖ :=
  (rfl)

/-- The determinant of an automorphism is its modulus times its normalized determinant. -/
theorem det_eq_norm_mul_normalizedDet (A : E ≃L[ℂ] E) :
    LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E) =
      ‖LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E)‖ * (A.normalizedDet : ℂ) := by
  have hd : LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E) ≠ 0 := A.toLinearEquiv.isUnit_det'.ne_zero
  rw [coe_normalizedDet, mul_div_cancel₀ _ (by simpa using hd)]

end ContinuousLinearEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A continuous family of complex-linear automorphisms has a continuous family of normalized
determinants. -/
theorem Continuous.normalizedDet {X : Type*} [TopologicalSpace X] {A : X → E ≃L[ℂ] E}
    (hA : Continuous fun x => (A x : E →L[ℂ] E)) : Continuous fun x => (A x).normalizedDet := by
  have hd : Continuous fun x => LinearMap.det ((A x).toLinearEquiv : E →ₗ[ℂ] E) :=
    ContinuousLinearMap.continuous_det.comp hA
  refine Continuous.subtype_mk (hd.div (Complex.continuous_ofReal.comp hd.norm) fun x => ?_) _
  simpa using (A x).toLinearEquiv.isUnit_det'.ne_zero
