/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.Path
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Normalized determinants of loops of operators

A continuous loop `P` of invertible complex-linear endomorphisms of a complex normed space has a
loop `δ` in the circle of normalized determinants, `det (P t) = ‖det (P t)‖ δ t`
(`TauCeti.exists_path_det_eq_norm_mul`). Its degree is the winding number of the loop of
determinants, the quantity that enters the product axiom of the Maslov index
(`TauCeti.TotallyRealLoop.maslovIndex_map`).

The normalized determinant `det L / ‖det L‖` of a single operator is its determinant phase
`ContinuousLinearMap.detPhase`. It depends continuously on operators with nonzero determinant
(`ContinuousLinearMap.continuousOn_detPhase`) and is multiplicative
(`ContinuousLinearMap.detPhase_comp`).
-/

public section

open scoped unitInterval

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The phase `det L / ‖det L‖` of the determinant of a complex-linear operator, a point of the
circle. It is `1` when the determinant vanishes. -/
noncomputable def detPhase (L : E →L[ℂ] E) : Circle :=
  if h : L.det = 0 then 1 else ⟨L.det / ‖L.det‖, mem_sphere_zero_iff_norm.2 (by simp [h])⟩

/-- The determinant phase of an operator with nonzero determinant is `det L / ‖det L‖`. -/
theorem coe_detPhase {L : E →L[ℂ] E} (h : L.det ≠ 0) : (L.detPhase : ℂ) = L.det / ‖L.det‖ := by
  simp only [detPhase, h, ↓reduceDIte]

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

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Every continuous loop `P` of invertible complex-linear endomorphisms has a circle loop `δ` of
normalized determinants, `det (P t) = ‖det (P t)‖ δ t`, as required by
`TauCeti.TotallyRealLoop.maslovIndex_map`. -/
theorem exists_path_det_eq_norm_mul {P : I → E →L[ℂ] E} (hP : Continuous P)
    (hP01 : P 0 = P 1) (hdet : ∀ t, LinearMap.det (P t : E →ₗ[ℂ] E) ≠ 0) :
    ∃ (x : Circle) (δ : Path x x), ∀ t,
      LinearMap.det (P t : E →ₗ[ℂ] E) = ‖LinearMap.det (P t : E →ₗ[ℂ] E)‖ * δ t := by
  refine ⟨(P 0).detPhase, ⟨⟨fun t ↦ (P t).detPhase,
    ContinuousLinearMap.continuous_detPhase hP hdet⟩, rfl, by simp only [hP01]⟩, fun t => ?_⟩
  rw [Path.coe_mk_mk, ContinuousLinearMap.coe_detPhase (hdet t)]
  exact (mul_div_cancel₀ _ (by simpa using hdet t)).symm

end TauCeti
