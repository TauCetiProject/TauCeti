/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Index

/-!
# Nondegenerate critical points of separated sums of functions of one variable

For a finite family of functions `φ i : ℝ → ℝ`, the *separated sum* `y ↦ ∑ i, φ i (y i)` on
`ι → ℝ` has diagonal second derivative: its Hessian quadratic form at `y` is the diagonal form
`∑ i, φ i'' (y i) • (v i)²`, Mathlib's `QuadraticMap.weightedSumSquares` with weights the second
derivatives of the summands. Consequently `y` is a critical point of the sum exactly when each
`y i` is a critical point of `φ i`; it is a nondegenerate critical point exactly when, moreover,
each second derivative `φ i'' (y i)` is nonzero; and its Morse index is the number of `i` with
`φ i'' (y i) < 0`, by Sylvester's count `QuadraticMap.sigNeg_weightedSumSquares`.

This is the calculus behind the standard Morse function `∑ i, cos (2π xᵢ / pᵢ)` on a torus
`∀ i, AddCircle (p i)`, whose charts have the real coordinates of the factors as coordinates. The
binary analogue for two arbitrary summands is `TauCeti.Analysis.Calculus.Morse.Prod`.

## Main declarations

* `TauCeti.hasFDerivAt_sum_comp_eval`, `TauCeti.fderiv_sum_comp_eval_eq_zero_iff`: the
  derivative of a separated sum, and its critical points.
* `TauCeti.fderiv_fderiv_sum_comp_eval_apply`, `TauCeti.hessianQuadraticForm_sum_comp_eval`: its
  second derivative is diagonal, and its Hessian quadratic form is a weighted sum of squares.
* `TauCeti.isNondegenerateCriticalPoint_sum_comp_eval_iff`: its nondegenerate critical points.
* `TauCeti.morseIndex_sum_comp_eval`: its Morse index counts the negative second derivatives.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 1.
-/

public section

open Filter Topology ContinuousLinearMap

namespace TauCeti

variable {ι : Type*} [Fintype ι] {φ : ι → ℝ → ℝ} {y : ι → ℝ}

/-- The derivative of the separated sum `z ↦ ∑ i, φ i (z i)` at `y` is `∑ i, φ i' (y i) • dzᵢ`. -/
theorem hasFDerivAt_sum_comp_eval {φ' : ι → ℝ} (hφ : ∀ i, HasDerivAt (φ i) (φ' i) (y i)) :
    HasFDerivAt (fun z : ι → ℝ ↦ ∑ i, φ i (z i)) (∑ i, φ' i • (proj i : (ι → ℝ) →L[ℝ] ℝ)) y :=
  HasFDerivAt.fun_sum fun i _ ↦ (hφ i).comp_hasFDerivAt y (hasFDerivAt_apply i y)

/-- The derivative of a separated sum of differentiable functions. -/
theorem fderiv_sum_comp_eval (hφ : ∀ i, DifferentiableAt ℝ (φ i) (y i)) :
    fderiv ℝ (fun z : ι → ℝ ↦ ∑ i, φ i (z i)) y =
      ∑ i, deriv (φ i) (y i) • (proj i : (ι → ℝ) →L[ℝ] ℝ) :=
  (hasFDerivAt_sum_comp_eval fun i ↦ (hφ i).hasDerivAt).fderiv

/-- **Critical points of a separated sum.** For differentiable summands, `y` is a critical point
of `z ↦ ∑ i, φ i (z i)` exactly when every `y i` is a critical point of `φ i`. -/
theorem fderiv_sum_comp_eval_eq_zero_iff (hφ : ∀ i, DifferentiableAt ℝ (φ i) (y i)) :
    fderiv ℝ (fun z : ι → ℝ ↦ ∑ i, φ i (z i)) y = 0 ↔ ∀ i, deriv (φ i) (y i) = 0 := by
  classical
  rw [fderiv_sum_comp_eval hφ]
  refine ⟨fun h i ↦ ?_, fun h ↦ by simp [h]⟩
  simpa [Pi.single_apply] using DFunLike.congr_fun h (Pi.single i 1)

/-- Near a point at which every summand is twice continuously differentiable, the derivative of a
separated sum is given by the formula of `TauCeti.fderiv_sum_comp_eval`. -/
private theorem fderiv_sum_comp_eval_eventuallyEq (hφ : ∀ i, ContDiffAt ℝ 2 (φ i) (y i)) :
    fderiv ℝ (fun z : ι → ℝ ↦ ∑ i, φ i (z i)) =ᶠ[𝓝 y]
      fun z ↦ ∑ i, deriv (φ i) (z i) • (proj i : (ι → ℝ) →L[ℝ] ℝ) := by
  have hdiff : ∀ i, ∀ᶠ z : ι → ℝ in 𝓝 y, DifferentiableAt ℝ (φ i) (z i) := fun i ↦
    (continuous_apply i).continuousAt.eventually
      (((hφ i).eventually (by simp)).mono fun t ht ↦ ht.differentiableAt (by simp))
  filter_upwards [eventually_all.2 hdiff] with z hz
  exact fderiv_sum_comp_eval hz

/-- **The second derivative of a separated sum is diagonal**: at a point at which every summand is
twice continuously differentiable, it sends `v` and `w` to `∑ i, φ i'' (y i) * v i * w i`. -/
theorem fderiv_fderiv_sum_comp_eval_apply (hφ : ∀ i, ContDiffAt ℝ 2 (φ i) (y i))
    (v w : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (fun z : ι → ℝ ↦ ∑ i, φ i (z i))) y v w =
      ∑ i, deriv (deriv (φ i)) (y i) * v i * w i := by
  have hd : HasFDerivAt (fun z : ι → ℝ ↦ ∑ i, deriv (φ i) (z i) • (proj i : (ι → ℝ) →L[ℝ] ℝ))
      (∑ i, (deriv (deriv (φ i)) (y i) • (proj i : (ι → ℝ) →L[ℝ] ℝ)).smulRight
        (proj i : (ι → ℝ) →L[ℝ] ℝ)) y := by
    refine HasFDerivAt.fun_sum fun i _ ↦ ?_
    have h := ((hφ i).derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero
    have h' : HasFDerivAt (fun z : ι → ℝ ↦ deriv (φ i) (z i))
        (deriv (deriv (φ i)) (y i) • (proj i : (ι → ℝ) →L[ℝ] ℝ)) y :=
      -- The inner function is named, since unification cannot split the composite itself.
      HasDerivAt.comp_hasFDerivAt (f := fun z : ι → ℝ ↦ z i) y h.hasDerivAt
        (hasFDerivAt_apply i y)
    exact h'.smul_const (proj i : (ι → ℝ) →L[ℝ] ℝ)
  rw [(fderiv_sum_comp_eval_eventuallyEq hφ).fderiv_eq, hd.fderiv]
  simp [mul_comm, mul_left_comm]

/-- **The Hessian of a separated sum is a weighted sum of squares**, with weights the second
derivatives of the summands. -/
theorem hessianQuadraticForm_sum_comp_eval (hφ : ∀ i, ContDiffAt ℝ 2 (φ i) (y i)) :
    hessianQuadraticForm (fun z : ι → ℝ ↦ ∑ i, φ i (z i)) y =
      QuadraticMap.weightedSumSquares ℝ fun i ↦ deriv (deriv (φ i)) (y i) := by
  ext v
  simp [fderiv_fderiv_sum_comp_eval_apply hφ, mul_assoc]

/-- **Nondegenerate critical points of a separated sum.** For summands twice continuously
differentiable at the coordinates of `y`, the separated sum `z ↦ ∑ i, φ i (z i)` has a
nondegenerate critical point at `y` exactly when every `y i` is a critical point of `φ i` at which
the second derivative of `φ i` does not vanish. -/
theorem isNondegenerateCriticalPoint_sum_comp_eval_iff
    (hφ : ∀ i, ContDiffAt ℝ 2 (φ i) (y i)) :
    IsNondegenerateCriticalPoint (fun z : ι → ℝ ↦ ∑ i, φ i (z i)) y ↔
      ∀ i, deriv (φ i) (y i) = 0 ∧ deriv (deriv (φ i)) (y i) ≠ 0 := by
  classical
  have hcont : ContDiffAt ℝ 2 (fun z : ι → ℝ ↦ ∑ i, φ i (z i)) y :=
    ContDiffAt.sum fun i _ ↦ (hφ i).comp y (contDiffAt_apply ℝ (fun _ ↦ ℝ) i y)
  rw [isNondegenerateCriticalPoint_iff_separatingLeft,
    fderiv_sum_comp_eval_eq_zero_iff fun i ↦ (hφ i).differentiableAt (by simp)]
  simp only [hcont, true_and, forall_and]
  refine and_congr_right fun _ ↦ ⟨fun h i hi ↦ ?_, fun h v hv ↦ funext fun i ↦ ?_⟩
  · -- A vanishing weight makes the corresponding basis vector isotropic for every vector.
    have := h (Pi.single i 1) fun w ↦ by
      simp [fderiv_fderiv_sum_comp_eval_apply hφ, Pi.single_apply, hi]
    simpa using congrFun this i
  · -- Pairing with the `i`-th basis vector reads off `φ i'' (y i) * v i`.
    have := hv (Pi.single i 1)
    simp only [toBilinForm_apply, fderiv_fderiv_sum_comp_eval_apply hφ, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
    simpa [h i] using this

/-- **The Morse index of a separated sum** at a point at which every summand is twice continuously
differentiable is the number of summands whose second derivative is negative there. -/
theorem morseIndex_sum_comp_eval (hφ : ∀ i, ContDiffAt ℝ 2 (φ i) (y i)) :
    morseIndex (fun z : ι → ℝ ↦ ∑ i, φ i (z i)) y =
      {i | deriv (deriv (φ i)) (y i) < 0}.ncard := by
  rw [morseIndex_def, hessianQuadraticForm_sum_comp_eval hφ,
    QuadraticForm.sigNeg_weightedSumSquares]

end TauCeti

end
