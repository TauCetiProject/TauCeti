/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.Normed.Module.Normalize

/-!
# The normalized determinant of a complex-linear operator

The determinant of a complex-linear operator `L` is `‖det L‖` times the point
`det L / ‖det L‖` of the unit circle when it is nonzero (`ContinuousLinearMap.detPhase`, the
determinant phase, which is `1` when the determinant vanishes). It is the direction
`TauCeti.sphereDirection 1 (det L)` of the determinant. The determinant phase depends
continuously on operators with nonzero determinant, for instance on automorphisms, so a loop of
automorphisms gives a loop on the circle; its degree is the winding number of the loop of
determinants.

## Main declarations

* `ContinuousLinearMap.detPhase`: the point `det L / ‖det L‖` of the circle.
* `ContinuousLinearMap.det_eq_norm_mul_detPhase`: `det L = ‖det L‖ * detPhase L`.
* `ContinuousLinearMap.continuousOn_detPhase`, `ContinuousLinearMap.continuous_detPhase`: a
  continuous family of operators with nonzero determinants has continuous determinant phase.
* `ContinuousLinearMap.detPhase_comp`: the determinant phase is multiplicative on operators with
  nonzero determinant.
* `ContinuousLinearEquiv.det_coe_ne_zero`: an automorphism has nonzero determinant.
* `ContinuousLinearEquiv.det_eq_norm_mul_detPhase`: `det A = ‖det A‖ * detPhase A` for an
  automorphism `A`.
-/

public section

namespace ContinuousLinearEquiv

/-- A continuous linear automorphism has nonzero determinant. -/
theorem det_coe_ne_zero {R M : Type*} [CommRing R] [Nontrivial R] [TopologicalSpace M]
    [AddCommGroup M] [Module R M] (A : M ≃L[R] M) : (A : M →L[R] M).det ≠ 0 := by
  rw [ContinuousLinearMap.det, A.toLinearMap_toContinuousLinearMap]
  exact A.toLinearEquiv.isUnit_det'.ne_zero

end ContinuousLinearEquiv

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The phase `det L / ‖det L‖` of the determinant of a complex-linear operator, a point of the
circle: the direction `TauCeti.sphereDirection 1 (det L)` of the determinant. It is `1` when the
determinant vanishes. -/
noncomputable def detPhase (L : E →L[ℂ] E) : Circle :=
  ⟨TauCeti.sphereDirection 1 L.det, (TauCeti.sphereDirection 1 L.det).2⟩

/-- The determinant phase is the direction of the determinant. -/
theorem coe_detPhase_eq_sphereDirection (L : E →L[ℂ] E) :
    (L.detPhase : ℂ) = TauCeti.sphereDirection 1 L.det :=
  (rfl)

/-- The determinant phase of an operator with nonzero determinant is `det L / ‖det L‖`. -/
theorem coe_detPhase {L : E →L[ℂ] E} (h : L.det ≠ 0) : (L.detPhase : ℂ) = L.det / ‖L.det‖ := by
  rw [coe_detPhase_eq_sphereDirection, TauCeti.coe_sphereDirection_of_ne_zero _ h,
    NormedSpace.normalize, Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]

/-- The determinant phase of an operator with vanishing determinant is `1`. -/
theorem detPhase_of_det_eq_zero {L : E →L[ℂ] E} (h : L.det = 0) : L.detPhase = 1 := by
  ext1
  rw [coe_detPhase_eq_sphereDirection, h, TauCeti.sphereDirection_zero]
  rfl

/-- The determinant of an operator is its modulus times its determinant phase. -/
theorem det_eq_norm_mul_detPhase (L : E →L[ℂ] E) : L.det = ‖L.det‖ * (L.detPhase : ℂ) := by
  rw [coe_detPhase_eq_sphereDirection, ← Complex.real_smul,
    TauCeti.norm_smul_sphereDirection]

/-- The determinant phase depends continuously on operators with nonzero determinant. -/
theorem continuousOn_detPhase {T : Type*} [TopologicalSpace T] {L : T → E →L[ℂ] E} {U : Set T}
    (hL : ContinuousOn L U) (h : ∀ t ∈ U, (L t).det ≠ 0) :
    ContinuousOn (fun t ↦ (L t).detPhase) U := by
  have hd : ContinuousOn (fun t ↦ (L t).det) U := continuous_det.comp_continuousOn hL
  have hc : ContinuousOn (fun t ↦ (TauCeti.sphereDirection 1 (L t).det : ℂ)) U := fun t ht ↦
    continuous_subtype_val.continuousAt.comp_continuousWithinAt <|
      (TauCeti.continuousAt_sphereDirection 1 (h t ht)).comp_continuousWithinAt
        (f := fun t ↦ (L t).det) (hd t ht)
  exact Topology.IsInducing.subtypeVal.continuousOn_iff.2 <|
    hc.congr fun t _ ↦ coe_detPhase_eq_sphereDirection (L t)

/-- A continuous family of operators with nonzero determinants has continuous determinant
phase. -/
theorem continuous_detPhase {T : Type*} [TopologicalSpace T] {L : T → E →L[ℂ] E}
    (hL : Continuous L) (h : ∀ t, (L t).det ≠ 0) : Continuous fun t ↦ (L t).detPhase :=
  continuousOn_univ.1 (continuousOn_detPhase hL.continuousOn fun t _ ↦ h t)

/-- The determinant phase is multiplicative on operators with nonzero determinant. -/
theorem detPhase_comp {A B : E →L[ℂ] E} (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    (A ∘L B).detPhase = A.detPhase * B.detPhase := by
  have hdet : (A ∘L B).det = A.det * B.det := LinearMap.det_comp _ _
  ext1
  rw [Circle.coe_mul, coe_detPhase hA, coe_detPhase hB, coe_detPhase (hdet ▸ mul_ne_zero hA hB),
    hdet, norm_mul, Complex.ofReal_mul, div_mul_div_comm]

end ContinuousLinearMap

namespace ContinuousLinearEquiv

/-- The determinant of an automorphism is its modulus times its determinant phase. -/
theorem det_eq_norm_mul_detPhase {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : E ≃L[ℂ] E) :
    LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E) =
      ‖LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E)‖ * ((A : E →L[ℂ] E).detPhase : ℂ) := by
  rw [← A.toLinearMap_toContinuousLinearMap]
  exact (A : E →L[ℂ] E).det_eq_norm_mul_detPhase

end ContinuousLinearEquiv
