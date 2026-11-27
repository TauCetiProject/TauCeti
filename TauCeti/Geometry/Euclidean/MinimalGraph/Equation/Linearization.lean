/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Otis Chodosh, The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.MinimalGraph.Ellipticity
public import TauCeti.Geometry.Euclidean.MinimalGraph.Equation.Operator
public import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv

/-!
# The derivative of the Euclidean minimal graph flux

The derivative of the normalized gradient flux is the principal graph operator multiplied by
`(1 + ‖p‖²)^(-3/2)`. Its eigenvalues lie between `(1 + ‖p‖²)^(-3/2)` and
`(1 + ‖p‖²)^(-1/2)`, so a local gradient bound supplies a positive ellipticity constant.

The chain rule identifies this operator with the derivative of the native graph area flux.
In particular, twice continuous differentiability of the height suffices for continuously
differentiable area flux; no higher regularity of the height is assumed.

Adapted from Otis Chodosh's formalization in
`ForTauCeti/Geometry/Euclidean/MinimalGraph/Equation/Linearization.lean` in
[ColdingMinicozziTheory](https://github.com/riccardobrasca/ColdingMinicozziTheory/blob/f2d78185da1ed3b232e2cbdfeec25e7f18fbf23d/ForTauCeti/Geometry/Euclidean/MinimalGraph/Equation/Linearization.lean)
(commit `f2d78185da1ed3b232e2cbdfeec25e7f18fbf23d`).

## Main declarations

* `TauCeti.MinimalGraph.hasFDerivAt_univUnitBall_fluxJacobian`: the normalized-flux derivative.
* `TauCeti.MinimalGraph.contDiff_fluxJacobian`: smooth dependence of the coefficient operator.
* `TauCeti.MinimalGraph.fderiv_areaFlux`: the native flux chain rule.
* `TauCeti.MinimalGraph.contDiffOn_areaFlux`: finite regularity of the native flux.
* `TauCeti.MinimalGraph.norm_sq_mul_le_inner_fluxJacobian_of_norm_le`: uniform lower ellipticity
  on bounded sets of gradients.

## References

* O. Chodosh, *Introduction to minimal surfaces*, Section 18.
-/

public noncomputable section

open InnerProductSpace
open scoped ContDiff Gradient InnerProductSpace

namespace TauCeti.MinimalGraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Jacobian of the normalized Euclidean graph flux. -/
def fluxJacobian (p : E) : E →L[ℝ] E :=
  (1 + ‖p‖ ^ 2) ^ (-(3 / 2 : ℝ)) •
    ((1 + ‖p‖ ^ 2) • ContinuousLinearMap.id ℝ E - rankOne ℝ p p)

/-- The flux Jacobian is the cleared-denominator principal operator scaled by the area factor. -/
@[simp low]
theorem fluxJacobian_apply (p v : E) :
    fluxJacobian p v = (1 + ‖p‖ ^ 2) ^ (-(3 / 2 : ℝ)) • principalOperator p v := by
  simp only [fluxJacobian, smul_apply, sub_apply, ContinuousLinearMap.id_apply, rankOne_apply,
    principalOperator_apply]

private theorem fluxJacobian_eq (p : E) :
    fluxJacobian p =
      (1 + ‖p‖ ^ 2) ^ (-(1 / 2 : ℝ)) • ContinuousLinearMap.id ℝ E +
        (-(1 + ‖p‖ ^ 2) ^ (-(3 / 2 : ℝ)) • innerSL ℝ p).smulRight p := by
  ext v
  rw [fluxJacobian_apply]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    smul_eq_mul]
  rw [principalOperator_apply, smul_sub, smul_smul,
    ← Real.rpow_add_one (by positivity : 1 + ‖p‖ ^ 2 ≠ 0)]
  norm_num [mul_smul, sub_eq_add_neg]

/-- The radial unit-ball map has derivative given by the graph flux Jacobian. -/
theorem hasFDerivAt_univUnitBall_fluxJacobian (p : E) :
    HasFDerivAt (OpenPartialHomeomorph.univUnitBall : E → E) (fluxJacobian p) p := by
  rw [fluxJacobian_eq]
  have h := OpenPartialHomeomorph.hasFDerivAt_univUnitBall p
  have hweight : (√(1 + ‖p‖ ^ 2))⁻¹ = (1 + ‖p‖ ^ 2) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg (by positivity)]
  have hweight' : ((1 + ‖p‖ ^ 2) ^ (-(1 / 2 : ℝ))) ^ (3 : ℕ) =
      (1 + ‖p‖ ^ 2) ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [hweight, hweight'] at h
  convert h using 1
  ext v
  simp [sub_eq_add_neg, neg_smul, smul_smul]

/-- The normalized flux Jacobian depends smoothly on the gradient. -/
theorem contDiff_fluxJacobian : ContDiff ℝ ∞ (fluxJacobian (E := E)) := by
  have hweight : ContDiff ℝ ∞ (fun p : E ↦ (1 + ‖p‖ ^ 2) ^ (-(1 / 2 : ℝ))) :=
    TauCeti.contDiff_one_add_norm_sq_rpow _
  have hweight' : ContDiff ℝ ∞ (fun p : E ↦ (1 + ‖p‖ ^ 2) ^ (-(3 / 2 : ℝ))) :=
    TauCeti.contDiff_one_add_norm_sq_rpow _
  have hinner : ContDiff ℝ ∞ (fun p : E ↦ innerSL ℝ p) := (innerSL ℝ).contDiff
  have h : ContDiff ℝ ∞ (fun p : E ↦
      (1 + ‖p‖ ^ 2) ^ (-(1 / 2 : ℝ)) • ContinuousLinearMap.id ℝ E +
        (-(1 + ‖p‖ ^ 2) ^ (-(3 / 2 : ℝ)) • innerSL ℝ p).smulRight p) :=
    (hweight.smul contDiff_const).add ((hweight'.neg.smul hinner).smulRight contDiff_id)
  convert h using 1
  funext p
  exact fluxJacobian_eq p

section CompleteSpace

variable [CompleteSpace E]

private theorem areaFlux_eq_univUnitBall (u : E → ℝ) :
    areaFlux u = fun x ↦ OpenPartialHomeomorph.univUnitBall (∇ u x) := by
  funext x
  rw [areaFlux_apply, areaWeight_eq_inv_sqrt, OpenPartialHomeomorph.univUnitBall_apply]

/-- The inverse radial unit-ball map recovers the gradient from the graph area flux. -/
@[simp]
theorem univUnitBall_symm_comp_areaFlux (u : E → ℝ) :
    OpenPartialHomeomorph.univUnitBall.symm ∘ areaFlux u = ∇ u := by
  funext y
  rw [Function.comp_apply, areaFlux_eq_univUnitBall]
  exact OpenPartialHomeomorph.univUnitBall.left_inv (Set.mem_univ (∇ u y))

/-- The derivative of the graph area flux is the Jacobian composed with the gradient derivative. -/
theorem hasFDerivAt_areaFlux {u : E → ℝ} {x : E}
    (hgrad : DifferentiableAt ℝ (∇ u) x) :
    HasFDerivAt (areaFlux u)
      ((fluxJacobian (∇ u x)).comp (fderiv ℝ (∇ u) x)) x := by
  rw [areaFlux_eq_univUnitBall]
  exact (hasFDerivAt_univUnitBall_fluxJacobian (∇ u x)).comp x hgrad.hasFDerivAt

/-- The normalized gradient is differentiable wherever the gradient is differentiable. -/
theorem differentiableAt_areaFlux {u : E → ℝ} {x : E}
    (hgrad : DifferentiableAt ℝ (∇ u) x) : DifferentiableAt ℝ (areaFlux u) x :=
  (hasFDerivAt_areaFlux hgrad).differentiableAt

/-- The graph area flux is differentiable exactly where the gradient is differentiable. -/
@[simp]
theorem differentiableAt_areaFlux_iff {u : E → ℝ} {x : E} :
    DifferentiableAt ℝ (areaFlux u) x ↔ DifferentiableAt ℝ (∇ u) x := by
  refine ⟨fun h ↦ ?_, differentiableAt_areaFlux⟩
  have hx : areaFlux u x ∈ Metric.ball (0 : E) 1 :=
    mem_ball_zero_iff.2 (norm_areaFlux_lt_one u x)
  have hd := (OpenPartialHomeomorph.contDiffOn_univUnitBall_symm (n := 1)
    (E := E)).contDiffAt (Metric.isOpen_ball.mem_nhds hx)
  simpa only [univUnitBall_symm_comp_areaFlux] using
    (hd.differentiableAt one_ne_zero).comp x h

/-- Differentiating the actual minimal graph area flux gives the normalized Jacobian. -/
theorem fderiv_areaFlux (u : E → ℝ) (x : E) :
    fderiv ℝ (areaFlux u) x =
      (fluxJacobian (∇ u x)).comp (fderiv ℝ (∇ u) x) := by
  by_cases hu : DifferentiableAt ℝ (∇ u) x
  · exact (hasFDerivAt_areaFlux hu).fderiv
  have hflux : ¬ DifferentiableAt ℝ (areaFlux u) x :=
    mt differentiableAt_areaFlux_iff.mp hu
  rw [fderiv_zero_of_not_differentiableAt hflux, fderiv_zero_of_not_differentiableAt hu,
    ContinuousLinearMap.comp_zero]

/-- The graph area flux has one fewer continuous derivative than the height. -/
theorem contDiffOn_areaFlux {n : WithTop ℕ∞} {u : E → ℝ} {Ω : Set E} (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ (n + 1) u Ω) : ContDiffOn ℝ n (areaFlux u) Ω := by
  have hgrad : ContDiffOn ℝ n (∇ u) Ω := by
    exact (toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
      (hu.fderiv_of_isOpen hΩ le_rfl)
  -- Mathlib's unit-ball smoothness covers ℕ∞; the bracket-power lemma also covers analytic order.
  have hflux : ContDiff ℝ n (fun p : E ↦ (1 + ‖p‖ ^ 2) ^ (-(1 / 2 : ℝ)) • p) :=
    (TauCeti.contDiff_one_add_norm_sq_rpow _).smul contDiff_id
  convert hflux.comp_contDiffOn hgrad using 1
  funext x
  rw [Function.comp_apply, areaFlux_apply, areaWeight_def]

end CompleteSpace

/-- The flux Jacobian quadratic form is the normalized principal graph form. -/
theorem inner_fluxJacobian_eq (p v : E) :
    ⟪fluxJacobian p v, v⟫_ℝ =
      (1 + ‖p‖ ^ 2) ^ (-(3 / 2 : ℝ)) * principalForm p v := by
  rw [fluxJacobian_apply, real_inner_smul_left, principalForm_eq_inner]

/-- The pointwise lower ellipticity bound for the flux Jacobian. -/
theorem norm_sq_mul_le_inner_fluxJacobian (p v : E) :
    (1 + ‖p‖ ^ 2) ^ (-(3 / 2 : ℝ)) * ‖v‖ ^ 2 ≤ ⟪fluxJacobian p v, v⟫_ℝ := by
  rw [inner_fluxJacobian_eq]
  exact mul_le_mul_of_nonneg_left (norm_sq_le_principalForm p v) (by positivity)

/-- The flux Jacobian is positive on every nonzero vector. -/
theorem inner_fluxJacobian_pos (p : E) {v : E} (hv : v ≠ 0) :
    0 < ⟪fluxJacobian p v, v⟫_ℝ := by
  rw [inner_fluxJacobian_eq]
  exact mul_pos (by positivity) (principalForm_pos p hv)

/-- The pointwise upper ellipticity bound for the flux Jacobian. -/
theorem inner_fluxJacobian_le (p v : E) :
    ⟪fluxJacobian p v, v⟫_ℝ ≤ (1 + ‖p‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ‖v‖ ^ 2 := by
  rw [inner_fluxJacobian_eq]
  calc
    _ ≤ (1 + ‖p‖ ^ 2) ^ (-(3 / 2 : ℝ)) * ((1 + ‖p‖ ^ 2) * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (principalForm_le p v) (by positivity)
    _ = _ := by
      rw [← mul_assoc, ← Real.rpow_add_one (by positivity : 1 + ‖p‖ ^ 2 ≠ 0)]
      norm_num

/-- The flux Jacobian quadratic form is bounded by the Euclidean squared norm. -/
theorem inner_fluxJacobian_le_norm_sq (p v : E) : ⟪fluxJacobian p v, v⟫_ℝ ≤ ‖v‖ ^ 2 := by
  have hweight : (1 + ‖p‖ ^ 2) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖p‖]) (by norm_num)
  exact (inner_fluxJacobian_le p v).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hweight (sq_nonneg ‖v‖))

/-- A gradient bound gives a positive uniform lower bound for the flux Jacobian. -/
theorem norm_sq_mul_le_inner_fluxJacobian_of_norm_le (p v : E) {M : ℝ}
    (hp : ‖p‖ ≤ M) :
    (1 + M ^ 2) ^ (-(3 / 2 : ℝ)) * ‖v‖ ^ 2 ≤ ⟪fluxJacobian p v, v⟫_ℝ := by
  have hs : 1 + ‖p‖ ^ 2 ≤ 1 + M ^ 2 := by
    nlinarith [norm_nonneg p, (norm_nonneg p).trans hp]
  have hw := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 1 + ‖p‖ ^ 2) hs
    (by norm_num : -(3 / 2 : ℝ) ≤ 0)
  exact (mul_le_mul_of_nonneg_right hw (sq_nonneg ‖v‖)).trans
    (norm_sq_mul_le_inner_fluxJacobian p v)

end TauCeti.MinimalGraph
