/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The normalized determinant of a complex-linear operator

The determinant of a complex-linear operator `L` is `‖det L‖` times the point
`det L / ‖det L‖` of the unit circle when it is nonzero (`ContinuousLinearMap.detPhase`, the
determinant phase, which is `1` when the determinant vanishes). The determinant phase depends
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
-/

public section

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The phase `det L / ‖det L‖` of the determinant of a complex-linear operator, a point of the
circle. It is `1` when the determinant vanishes. -/
noncomputable def detPhase (L : E →L[ℂ] E) : Circle :=
  if h : L.det = 0 then 1 else ⟨L.det / ‖L.det‖, mem_sphere_zero_iff_norm.2 (by simp [h])⟩

/-- The determinant phase of an operator with nonzero determinant is `det L / ‖det L‖`. -/
theorem coe_detPhase {L : E →L[ℂ] E} (h : L.det ≠ 0) : (L.detPhase : ℂ) = L.det / ‖L.det‖ := by
  simp only [detPhase, h, ↓reduceDIte]

/-- The determinant of an operator is its modulus times its determinant phase. -/
theorem det_eq_norm_mul_detPhase (L : E →L[ℂ] E) : L.det = ‖L.det‖ * (L.detPhase : ℂ) := by
  by_cases h : L.det = 0
  · simp [h]
  · rw [coe_detPhase h, mul_div_cancel₀ _ (by simpa using h)]

/-- The determinant phase depends continuously on operators with nonzero determinant. -/
theorem continuousOn_detPhase {T : Type*} [TopologicalSpace T] {L : T → E →L[ℂ] E} {U : Set T}
    (hL : ContinuousOn L U) (h : ∀ t ∈ U, (L t).det ≠ 0) :
    ContinuousOn (fun t ↦ (L t).detPhase) U := by
  have hd : ContinuousOn (fun t ↦ (L t).det) U := continuous_det.comp_continuousOn hL
  have hc : ContinuousOn (fun t ↦ (L t).det / ((‖(L t).det‖ : ℝ) : ℂ)) U :=
    hd.div (Complex.continuous_ofReal.comp_continuousOn hd.norm) fun t ht ↦ by simpa using h t ht
  exact Topology.IsInducing.subtypeVal.continuousOn_iff.2 <|
    hc.congr fun t ht ↦ coe_detPhase (h t ht)

/-- A continuous family of operators with nonzero determinants has continuous determinant
phase. -/
theorem continuous_detPhase {T : Type*} [TopologicalSpace T] {L : T → E →L[ℂ] E}
    (hL : Continuous L) (h : ∀ t, (L t).det ≠ 0) : Continuous fun t ↦ (L t).detPhase :=
  continuousOn_univ.1 (continuousOn_detPhase hL.continuousOn fun t _ ↦ h t)

/-- The determinant phase is multiplicative on operators with nonzero determinant. -/
theorem detPhase_comp {A B : E →L[ℂ] E} (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    (A ∘L B).detPhase = A.detPhase * B.detPhase := by
  have hdet : (A ∘L B).det = A.det * B.det := LinearMap.det_comp _ _
  have hAB : (A ∘L B).det ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero hA hB
  ext1
  simp only [Circle.coe_mul, coe_detPhase hA, coe_detPhase hB, coe_detPhase hAB, hdet, norm_mul,
    Complex.ofReal_mul]
  field_simp

end ContinuousLinearMap
