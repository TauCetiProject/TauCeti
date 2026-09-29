/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Circle.Degree
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Normalized determinant loops in the circle

The determinant of a complex-linear automorphism is nonzero. Dividing it by its norm therefore
gives a point of the circle. A continuous closed path of automorphisms yields a circle loop, whose
degree is the winding number of the determinant. This is the loop used in the Maslov index
change-of-frame formula.
-/

public section

open scoped ComplexConjugate unitInterval

namespace TauCeti

namespace Complex

/-- The determinant phase of a complex number is the square of its normalization to the
unit circle. -/
theorem div_conj_eq_normalized_mul (z : ℂ) :
    z / conj z = (z / (‖z‖ : ℂ)) * (z / (‖z‖ : ℂ)) := by
  by_cases hz : z = 0
  · simp [hz]
  have hc : conj z ≠ 0 := by simp [hz]
  have hn : (‖z‖ : ℂ) ≠ 0 := by simp [hz]
  calc
    z / conj z = z * z / (z * conj z) := by field_simp
    _ = z * z / (‖z‖ : ℂ) ^ 2 := by rw [Complex.mul_conj']
    _ = (z / (‖z‖ : ℂ)) * (z / (‖z‖ : ℂ)) := by ring

end Complex

namespace LinearEquiv

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]

/-- The normalized complex determinant of an automorphism, as a point of the unit circle. -/
noncomputable def detCircle (B : E ≃ₗ[ℂ] E) : Circle :=
  ⟨LinearMap.det (B : E →ₗ[ℂ] E) /
    ‖LinearMap.det (B : E →ₗ[ℂ] E)‖, by
    have hdet : LinearMap.det (B : E →ₗ[ℂ] E) ≠ 0 := by
      rw [← LinearEquiv.coe_det]
      exact (LinearEquiv.det B).ne_zero
    simp [Submonoid.unitSphere, hdet]⟩

omit [FiniteDimensional ℂ E] in
@[simp]
theorem coe_detCircle (B : E ≃ₗ[ℂ] E) :
    (detCircle B : ℂ) =
      LinearMap.det (B : E →ₗ[ℂ] E) /
        ‖LinearMap.det (B : E →ₗ[ℂ] E)‖ :=
  (rfl)

end LinearEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- The loop in the unit circle obtained by normalizing the determinant of a closed path of
complex-linear automorphisms. -/
noncomputable def normalizedDetPath (B : I → E ≃L[ℂ] E)
    (hB : Continuous fun t => (B t : E →L[ℂ] E)) (hB01 : B 0 = B 1) :
    Path (LinearEquiv.detCircle (B 0).toLinearEquiv)
      (LinearEquiv.detCircle (B 0).toLinearEquiv) where
  toFun t := LinearEquiv.detCircle (B t).toLinearEquiv
  continuous_toFun := by
    have hd : Continuous fun t => LinearMap.det ((B t).toLinearEquiv : E →ₗ[ℂ] E) :=
      ContinuousLinearMap.continuous_det.comp hB
    have hden : Continuous fun t =>
        ((‖LinearMap.det ((B t).toLinearEquiv : E →ₗ[ℂ] E)‖ : ℝ) : ℂ) := by
      fun_prop
    have hn : ∀ t, ((‖LinearMap.det ((B t).toLinearEquiv : E →ₗ[ℂ] E)‖ : ℝ) : ℂ) ≠ 0 := by
      intro t
      simp only [Complex.ofReal_ne_zero, norm_ne_zero_iff]
      rw [← LinearEquiv.coe_det]
      exact (LinearEquiv.det (B t).toLinearEquiv).ne_zero
    exact (hd.div hden hn).subtype_mk _
  source' := rfl
  target' := by rw [hB01]

omit [FiniteDimensional ℂ E] in
@[simp]
theorem normalizedDetPath_apply (B : I → E ≃L[ℂ] E)
    (hB : Continuous fun t => (B t : E →L[ℂ] E)) (hB01 : B 0 = B 1) (t : I) :
    ((normalizedDetPath B hB hB01 t : Circle) : ℂ) =
      LinearMap.det ((B t).toLinearEquiv : E →ₗ[ℂ] E) /
        ‖LinearMap.det ((B t).toLinearEquiv : E →ₗ[ℂ] E)‖ :=
  (rfl)

end TauCeti

end
